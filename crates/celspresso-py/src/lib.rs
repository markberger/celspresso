//! Thin PyO3 layer. All ergonomics live in the `celspresso` Python package; this
//! module exposes a compiled-environment core, compiled programs, and `verify`.

use celspresso_check::{
    check, expand_definitions, CelType, CheckedExpr, Constraints, Contract, Definition, FieldDecl, FunctionDecl, Overload, Schema,
    StructDecl, VarDecl,
};
use celspresso_eval::{date, evaluate, evaluate_traced, time, Functions, Key, Limits, StructValue, Value};
use celspresso_syntax::{parse, render_diagnostic, unparse, Literal, Span};
use celspresso_verify::{bounds as run_bounds, verify as run_verify, ErrorMode, Extreme, Options, Query, Status};
use pyo3::exceptions::{PyException, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBool, PyBytes, PyDict, PyFloat, PyInt, PyList, PyString, PyTuple};
use pyo3::IntoPyObjectExt;
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

pyo3::create_exception!(_celspresso, CompileError, PyException);
pyo3::create_exception!(_celspresso, EvalError, PyException);

// ------------------------------------------------------------------ types

fn type_from_py(obj: &Bound<'_, PyAny>) -> PyResult<CelType> {
    if let Ok(s) = obj.extract::<String>() {
        return Ok(match s.as_str() {
            "bool" => CelType::Bool,
            "int" => CelType::Int,
            "uint" => CelType::Uint,
            "double" => CelType::Double,
            "string" => CelType::String,
            "bytes" => CelType::Bytes,
            "null" => CelType::Null,
            "date" => CelType::Date,
            "timestamp" => CelType::Timestamp,
            "duration" => CelType::Duration,
            "dyn" => CelType::Dyn,
            other => return Err(PyValueError::new_err(format!("unknown CEL type '{other}'"))),
        });
    }
    let t = obj.cast::<PyTuple>().map_err(|_| PyTypeError::new_err("type spec must be a str or tuple"))?;
    let kind: String = t.get_item(0)?.extract()?;
    Ok(match kind.as_str() {
        "list" => CelType::list(type_from_py(&t.get_item(1)?)?),
        "map" => CelType::map(type_from_py(&t.get_item(1)?)?, type_from_py(&t.get_item(2)?)?),
        "nullable" => CelType::nullable(type_from_py(&t.get_item(1)?)?),
        "struct" => CelType::Struct(t.get_item(1)?.extract()?),
        other => return Err(PyValueError::new_err(format!("unknown CEL type constructor '{other}'"))),
    })
}

fn type_to_py<'py>(py: Python<'py>, t: &CelType) -> PyResult<Bound<'py, PyAny>> {
    let s = |x: &str| x.into_bound_py_any(py);
    match t {
        CelType::Bool => s("bool"),
        CelType::Int => s("int"),
        CelType::Uint => s("uint"),
        CelType::Double => s("double"),
        CelType::String => s("string"),
        CelType::Bytes => s("bytes"),
        CelType::Null => s("null"),
        CelType::Date => s("date"),
        CelType::Timestamp => s("timestamp"),
        CelType::Duration => s("duration"),
        CelType::List(e) => ("list", type_to_py(py, e)?).into_bound_py_any(py),
        CelType::Map(k, v) => ("map", type_to_py(py, k)?, type_to_py(py, v)?).into_bound_py_any(py),
        CelType::Nullable(e) => ("nullable", type_to_py(py, e)?).into_bound_py_any(py),
        CelType::Struct(n) => ("struct", n.as_str()).into_bound_py_any(py),
        _ => s("dyn"),
    }
}

fn literal_from_py(obj: &Bound<'_, PyAny>) -> PyResult<Literal> {
    Ok(if obj.is_none() {
        Literal::Null
    } else if obj.is_instance_of::<PyBool>() {
        Literal::Bool(obj.extract()?)
    } else if obj.is_instance_of::<PyInt>() {
        match obj.extract::<i64>() {
            Ok(i) => Literal::Int(i),
            Err(_) => Literal::Uint(obj.extract()?),
        }
    } else if obj.is_instance_of::<PyFloat>() {
        Literal::Double(obj.extract()?)
    } else {
        Literal::String(obj.extract()?)
    })
}

fn constraints_from_py(obj: Option<&Bound<'_, PyAny>>) -> PyResult<Constraints> {
    let mut c = Constraints::default();
    let Some(obj) = obj else { return Ok(c) };
    if obj.is_none() {
        return Ok(c);
    }
    let d = obj.cast::<PyDict>().map_err(|_| PyTypeError::new_err("constraints must be a dict"))?;
    for (k, v) in d.iter() {
        let k: String = k.extract()?;
        match k.as_str() {
            "ge" => c.ge = Some(v.extract()?),
            "gt" => c.gt = Some(v.extract()?),
            "le" => c.le = Some(v.extract()?),
            "lt" => c.lt = Some(v.extract()?),
            "min_length" => c.min_length = Some(v.extract()?),
            "max_length" => c.max_length = Some(v.extract()?),
            "pattern" => c.pattern = Some(v.extract()?),
            "one_of" => {
                let mut out = Vec::new();
                for x in v.try_iter()? {
                    out.push(literal_from_py(&x?)?);
                }
                c.one_of = Some(out);
            }
            "items" => c.items = Some(Box::new(constraints_from_py(Some(&v))?)),
            other => return Err(PyValueError::new_err(format!("unknown constraint '{other}'"))),
        }
    }
    Ok(c)
}

// ----------------------------------------------------------------- values

fn date_class<'py>(py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
    py.import("datetime")?.getattr("date")
}

fn value_to_py<'py>(py: Python<'py>, v: &Value) -> PyResult<Bound<'py, PyAny>> {
    Ok(match v {
        // an absent optional is None, a present one its value
        Value::Null | Value::Optional(None) => py.None().into_bound(py),
        Value::Optional(Some(x)) => value_to_py(py, x)?,
        // ipaddress.IPv4Address / IPv6Address, and IPv4Interface / IPv6Interface for CIDRs
        // (an interface keeps the host bits that cidr('10.0.0.1/8') was written with)
        Value::Net(n) => {
            let ipaddress = py.import("ipaddress")?;
            let ctor = if matches!(**n, celspresso_eval::net::Net::Ip(_)) { "ip_address" } else { "ip_interface" };
            ipaddress.getattr(ctor)?.call1((n.to_string(),))?
        }
        Value::Bool(b) => b.into_bound_py_any(py)?,
        Value::Int(i) => i.into_bound_py_any(py)?,
        Value::Uint(u) => u.into_bound_py_any(py)?,
        Value::Double(d) => d.into_bound_py_any(py)?,
        Value::String(s) => s.as_ref().into_bound_py_any(py)?,
        Value::Bytes(b) => PyBytes::new(py, b).into_any(),
        Value::Date(d) => {
            let (y, m, dd) = date::civil_from_days(*d);
            date_class(py)?.call1((y, m, dd))?
        }
        Value::Timestamp(ns) => {
            // aware UTC datetime; Python has microsecond precision
            let dt = py.import("datetime")?;
            let epoch = dt.getattr("datetime")?.call1((1970, 1, 1, 0, 0, 0, 0, dt.getattr("timezone")?.getattr("utc")?))?;
            epoch.call_method1("__add__", (timedelta(py, *ns)?,))?
        }
        Value::Duration(ns) => timedelta(py, *ns)?,
        Value::Type(t) => t.as_ref().into_bound_py_any(py)?,
        Value::List(items) => {
            let out = PyList::empty(py);
            for x in items.iter() {
                out.append(value_to_py(py, x)?)?;
            }
            out.into_any()
        }
        Value::Map(m) => {
            let out = PyDict::new(py);
            for (k, x) in m.iter() {
                out.set_item(value_to_py(py, &k.to_value())?, value_to_py(py, x)?)?;
            }
            out.into_any()
        }
        Value::Struct(s) => {
            let out = PyDict::new(py);
            for (k, x) in s.fields.iter() {
                out.set_item(k, value_to_py(py, x)?)?;
            }
            out.into_any()
        }
    })
}

/// `datetime.timedelta` for a nanosecond span, truncated to microseconds.
fn timedelta<'py>(py: Python<'py>, ns: i128) -> PyResult<Bound<'py, PyAny>> {
    let us = ns.div_euclid(1000);
    let (secs, micros) = (us.div_euclid(1_000_000) as i64, us.rem_euclid(1_000_000) as i64);
    py.import("datetime")?.getattr("timedelta")?.call1((0, secs, micros))
}

fn timedelta_ns(td: &Bound<'_, PyAny>) -> PyResult<i128> {
    let days: i64 = td.getattr("days")?.extract()?;
    let secs: i64 = td.getattr("seconds")?.extract()?;
    let micros: i64 = td.getattr("microseconds")?.extract()?;
    Ok((i128::from(days) * 86_400 + i128::from(secs)) * 1_000_000_000 + i128::from(micros) * 1000)
}

fn conv_err(path: &str, expected: &str, obj: &Bound<'_, PyAny>) -> PyErr {
    // PHI-safe: name the type, never the value
    let got = obj.get_type().name().map(|n| n.to_string()).unwrap_or_else(|_| "?".into());
    PyTypeError::new_err(format!("expected {expected} at '{path}', got {got}"))
}

fn is_date(obj: &Bound<'_, PyAny>) -> PyResult<bool> {
    let py = obj.py();
    let date = date_class(py)?;
    let datetime = py.import("datetime")?.getattr("datetime")?;
    Ok(obj.is_instance(&date)? && !obj.is_instance(&datetime)?)
}

fn date_from_py(obj: &Bound<'_, PyAny>) -> PyResult<i64> {
    let y: i64 = obj.getattr("year")?.extract()?;
    let m: i64 = obj.getattr("month")?.extract()?;
    let d: i64 = obj.getattr("day")?.extract()?;
    Ok(date::days_from_civil(y, m, d))
}

/// Custom field readers, passed per call from Python (never stored here, so the GC
/// sees them): {struct name: {field name: callable(containing object) -> value}}.
type Readers<'a, 'py> = Option<&'a Bound<'py, PyDict>>;

/// Read field `name` from a mapping or an object (Pydantic model, dataclass, ...), or
/// with the field's custom reader if it has one. A reader's exception propagates, with
/// a note naming the field (a schema path, never a value).
fn get_field<'py>(
    obj: &Bound<'py, PyAny>,
    name: &str,
    reader: Option<Bound<'py, PyAny>>,
    path: &str,
) -> PyResult<Option<Bound<'py, PyAny>>> {
    if let Some(f) = reader {
        return f.call1((obj,)).map(Some).map_err(|e| {
            let _ = e.value(obj.py()).call_method1("add_note", (format!("while reading field '{path}'"),));
            e
        });
    }
    if let Ok(d) = obj.cast::<PyDict>() {
        return d.get_item(name);
    }
    match obj.getattr(name) {
        Ok(v) => Ok(Some(v)),
        Err(_) => Ok(None),
    }
}

fn value_from_py(obj: &Bound<'_, PyAny>, ty: &CelType, schema: &Schema, readers: Readers, path: &str) -> PyResult<Value> {
    match ty {
        CelType::Nullable(inner) => {
            if obj.is_none() {
                Ok(Value::Null)
            } else {
                value_from_py(obj, inner, schema, readers, path)
            }
        }
        CelType::Bool => {
            if obj.is_instance_of::<PyBool>() {
                Ok(Value::Bool(obj.extract()?))
            } else {
                Err(conv_err(path, "bool", obj))
            }
        }
        CelType::Int => {
            if obj.is_instance_of::<PyBool>() || !obj.is_instance_of::<PyInt>() {
                return Err(conv_err(path, "int", obj));
            }
            obj.extract::<i64>().map(Value::Int).map_err(|_| PyValueError::new_err(format!("int at '{path}' is out of int64 range")))
        }
        CelType::Uint => {
            if obj.is_instance_of::<PyBool>() || !obj.is_instance_of::<PyInt>() {
                return Err(conv_err(path, "uint", obj));
            }
            obj.extract::<u64>().map(Value::Uint).map_err(|_| PyValueError::new_err(format!("uint at '{path}' is out of uint64 range")))
        }
        CelType::Double => {
            if obj.is_instance_of::<PyFloat>() || (obj.is_instance_of::<PyInt>() && !obj.is_instance_of::<PyBool>()) {
                Ok(Value::Double(obj.extract()?))
            } else {
                Err(conv_err(path, "float", obj))
            }
        }
        CelType::String => {
            if obj.is_instance_of::<PyString>() {
                Ok(Value::str(&obj.extract::<String>()?))
            } else {
                Err(conv_err(path, "str", obj))
            }
        }
        CelType::Bytes => match obj.cast::<PyBytes>() {
            Ok(b) => Ok(Value::Bytes(Arc::from(b.as_bytes()))),
            Err(_) => Err(conv_err(path, "bytes", obj)),
        },
        CelType::Date => {
            if is_date(obj)? {
                Ok(Value::Date(date_from_py(obj)?))
            } else {
                Err(conv_err(path, "datetime.date", obj))
            }
        }
        CelType::Timestamp => {
            let datetime = obj.py().import("datetime")?.getattr("datetime")?;
            if !obj.is_instance(&datetime)? {
                return Err(conv_err(path, "datetime.datetime", obj));
            }
            if obj.call_method0("utcoffset")?.is_none() {
                return Err(PyValueError::new_err(format!(
                    "naive datetime at '{path}' has no time zone; attach one, e.g. tzinfo=datetime.timezone.utc"
                )));
            }
            let epoch = value_to_py(obj.py(), &Value::Timestamp(0))?;
            let ns = timedelta_ns(&obj.call_method1("__sub__", (epoch,))?)?;
            if !time::ts_in_range(ns) {
                return Err(PyValueError::new_err(format!("datetime at '{path}' is outside the CEL timestamp range")));
            }
            Ok(Value::Timestamp(ns))
        }
        CelType::Duration => {
            let td = obj.py().import("datetime")?.getattr("timedelta")?;
            if !obj.is_instance(&td)? {
                return Err(conv_err(path, "datetime.timedelta", obj));
            }
            let ns = timedelta_ns(obj)?;
            if !time::dur_in_range(ns) {
                return Err(PyValueError::new_err(format!("timedelta at '{path}' is outside the CEL duration range")));
            }
            Ok(Value::Duration(ns))
        }
        CelType::Null => {
            if obj.is_none() {
                Ok(Value::Null)
            } else {
                Err(conv_err(path, "None", obj))
            }
        }
        CelType::List(elem) => {
            if obj.is_instance_of::<PyString>() || obj.is_instance_of::<PyDict>() {
                return Err(conv_err(path, "list", obj));
            }
            let mut out = Vec::new();
            for (i, x) in obj.try_iter().map_err(|_| conv_err(path, "list", obj))?.enumerate() {
                out.push(value_from_py(&x?, elem, schema, readers, &format!("{path}[{i}]"))?);
            }
            Ok(Value::list(out))
        }
        CelType::Map(kt, vt) => {
            let d = obj.cast::<PyDict>().map_err(|_| conv_err(path, "dict", obj))?;
            let mut out = BTreeMap::new();
            for (k, v) in d.iter() {
                let kv = value_from_py(&k, kt, schema, readers, path)?;
                let key = Key::from_value(&kv).ok_or_else(|| PyTypeError::new_err(format!("unsupported map key type at '{path}'")))?;
                let vv = value_from_py(&v, vt, schema, readers, &format!("{path}[{}]", kv))?;
                out.insert(key, vv);
            }
            Ok(Value::Map(Arc::new(out)))
        }
        CelType::Struct(name) => {
            let Some(sd) = schema.structs.get(name) else {
                return Err(PyTypeError::new_err(format!("unknown struct type '{name}'")));
            };
            if obj.is_none() {
                return Err(conv_err(path, name, obj));
            }
            let mut fields = BTreeMap::new();
            let struct_readers = match readers {
                Some(r) => r.get_item(name)?.map(|d| d.cast_into::<PyDict>()).transpose()?,
                None => None,
            };
            for f in &sd.fields {
                let fpath = format!("{path}.{}", f.name);
                let reader = match &struct_readers {
                    Some(d) => d.get_item(&f.name)?,
                    None => None,
                };
                match get_field(obj, &f.name, reader, &fpath)? {
                    Some(v) => {
                        fields.insert(f.name.clone(), value_from_py(&v, &f.ty, schema, readers, &fpath)?);
                    }
                    None if matches!(f.ty, CelType::Nullable(_)) => {
                        fields.insert(f.name.clone(), Value::Null);
                    }
                    None => return Err(PyTypeError::new_err(format!("missing field '{fpath}'"))),
                }
            }
            Ok(Value::Struct(Arc::new(StructValue { type_name: name.clone(), fields })))
        }
        _ => infer_value(obj, path),
    }
}

fn infer_value(obj: &Bound<'_, PyAny>, path: &str) -> PyResult<Value> {
    if obj.is_none() {
        Ok(Value::Null)
    } else if obj.is_instance_of::<PyBool>() {
        Ok(Value::Bool(obj.extract()?))
    } else if obj.is_instance_of::<PyInt>() {
        match obj.extract::<i64>() {
            Ok(i) => Ok(Value::Int(i)),
            Err(_) => {
                obj.extract::<u64>().map(Value::Uint).map_err(|_| PyValueError::new_err(format!("integer at '{path}' is out of range")))
            }
        }
    } else if obj.is_instance_of::<PyFloat>() {
        Ok(Value::Double(obj.extract()?))
    } else if obj.is_instance_of::<PyString>() {
        Ok(Value::str(&obj.extract::<String>()?))
    } else if let Ok(b) = obj.cast::<PyBytes>() {
        Ok(Value::Bytes(Arc::from(b.as_bytes())))
    } else if is_date(obj)? {
        Ok(Value::Date(date_from_py(obj)?))
    } else if let Ok(d) = obj.cast::<PyDict>() {
        let mut out = BTreeMap::new();
        for (k, v) in d.iter() {
            let kv = infer_value(&k, path)?;
            let key = Key::from_value(&kv).ok_or_else(|| PyTypeError::new_err(format!("unsupported map key type at '{path}'")))?;
            out.insert(key, infer_value(&v, &format!("{path}[{kv}]"))?);
        }
        Ok(Value::Map(Arc::new(out)))
    } else if obj.is_instance_of::<PyList>() || obj.is_instance_of::<PyTuple>() {
        let mut out = Vec::new();
        for (i, x) in obj.try_iter()?.enumerate() {
            out.push(infer_value(&x?, &format!("{path}[{i}]"))?);
        }
        Ok(Value::list(out))
    } else if obj.hasattr("model_dump")? {
        infer_value(&obj.call_method0("model_dump")?, path)
    } else {
        Err(conv_err(path, "a CEL-compatible value", obj))
    }
}

// -------------------------------------------------------------- functions

/// Host functions, keyed by CEL function name.
struct PyFunctions {
    map: HashMap<String, Py<PyAny>>,
}

impl PyFunctions {
    fn from_dict(d: Option<&Bound<'_, PyDict>>) -> PyResult<Self> {
        let mut map = HashMap::new();
        if let Some(d) = d {
            for (k, v) in d.iter() {
                map.insert(k.extract::<String>()?, v.unbind());
            }
        }
        Ok(PyFunctions { map })
    }
}

impl Functions for PyFunctions {
    fn call(&self, function: &str, args: &[Value]) -> Option<Result<Value, String>> {
        let f = self.map.get(function)?;
        Some(Python::attach(|py| {
            let pyargs: Vec<Bound<'_, PyAny>> =
                args.iter().map(|a| value_to_py(py, a)).collect::<PyResult<_>>().map_err(|e| e.to_string())?;
            let tuple = PyTuple::new(py, pyargs).map_err(|e| e.to_string())?;
            match f.bind(py).call1(tuple) {
                Ok(r) => infer_value(&r, function).map_err(|e| format!("function '{function}' returned an unsupported value: {e}")),
                Err(e) => {
                    let ty = e.get_type(py).name().map(|n| n.to_string()).unwrap_or_default();
                    Err(format!("function '{function}' raised {ty}"))
                }
            }
        }))
    }
}

// -------------------------------------------------------------------- core

fn byte_to_char(src: &str, b: u32) -> usize {
    let b = (b as usize).min(src.len());
    src.get(..b).map(|s| s.chars().count()).unwrap_or(b)
}

fn span_chars(src: &str, s: Span) -> (usize, usize) {
    (byte_to_char(src, s.start), byte_to_char(src, s.end))
}

fn compile_err(kind: &str, src: &str, diags: Vec<(String, Span)>) -> PyErr {
    let items: Vec<(String, usize, usize, String)> = diags
        .into_iter()
        .map(|(m, s)| {
            let (a, b) = span_chars(src, s);
            let rendered = render_diagnostic(src, s, &m);
            (m, a, b, rendered)
        })
        .collect();
    CompileError::new_err((kind.to_string(), items, src.to_string()))
}

fn compile_source(schema: &Arc<Schema>, defs: &BTreeMap<String, Definition>, src: &str) -> PyResult<CheckedExpr> {
    let parsed = parse(src).map_err(|e| compile_err("syntax", src, vec![(e.message, e.span)]))?;
    let expanded = if defs.is_empty() { parsed } else { expand_definitions(parsed, defs) };
    check(expanded, schema.clone()).map_err(|errs| compile_err("type", src, errs.into_iter().map(|e| (e.message, e.span)).collect()))
}

#[pyclass(frozen, module = "celspresso._celspresso")]
struct Core {
    schema: Arc<Schema>,
    defs: BTreeMap<String, Definition>,
}

/// One tabulated call: (arguments, returned normally, result value or error message).
type TableRow<'py> = (Vec<Bound<'py, PyAny>>, bool, Bound<'py, PyAny>);
/// (parameter names, ensures source, total, table) for a host function.
type ContractSpec<'py> = (Vec<String>, Option<String>, bool, Option<Vec<TableRow<'py>>>);

/// A Value as a literal for a function table (scalars only).
fn value_literal(v: &Value) -> Option<Literal> {
    Some(match v {
        Value::Bool(b) => Literal::Bool(*b),
        Value::Int(i) | Value::Date(i) => Literal::Int(*i),
        Value::Uint(u) => Literal::Uint(*u),
        Value::Double(d) => Literal::Double(*d),
        Value::String(s) => Literal::String(s.to_string()),
        _ => return None,
    })
}

#[pymethods]
impl Core {
    /// structs: [(name, [(field, type, constraints)])]; vars: [(name, type, constraints)];
    /// functions: [(name, overload_id, receiver, [param types], result type)]; defs: [(name, source)];
    /// readers: {struct: [fields with a custom reader]}, checked here; the callables
    /// themselves are passed to each evaluate call
    #[new]
    #[pyo3(signature = (structs, vars, functions, defs, readers=None))]
    fn new(
        structs: Vec<(String, Vec<(String, Bound<'_, PyAny>, Option<Bound<'_, PyAny>>)>)>,
        vars: Vec<(String, Bound<'_, PyAny>, Option<Bound<'_, PyAny>>)>,
        functions: Vec<(String, String, bool, Vec<Bound<'_, PyAny>>, Bound<'_, PyAny>, Option<ContractSpec<'_>>)>,
        defs: Vec<(String, String, Option<Vec<(String, Bound<'_, PyAny>)>>)>,
        readers: Option<HashMap<String, Vec<String>>>,
    ) -> PyResult<Self> {
        let mut s = Schema::with_stdlib();
        for (name, fields) in structs {
            let mut fs = Vec::new();
            for (f, t, c) in fields {
                fs.push(FieldDecl { name: f, ty: type_from_py(&t)?, constraints: constraints_from_py(c.as_ref())? });
            }
            s.structs.insert(name.clone(), StructDecl { name, fields: fs });
        }
        for (name, t, c) in vars {
            s.vars.insert(name.clone(), VarDecl { name, ty: type_from_py(&t)?, constraints: constraints_from_py(c.as_ref())? });
        }
        let mut contracts = Vec::new();
        for (name, id, receiver, params, result, ensures) in functions {
            let params = params.iter().map(type_from_py).collect::<PyResult<Vec<_>>>()?;
            let result = type_from_py(&result)?;
            if let Some((names, src, total, rows)) = ensures {
                // a row that doesn't convert (an unsupported value) drops the whole table
                let table = match rows {
                    Some(rows) => {
                        let mut out = Vec::new();
                        for (args, ok, r) in rows {
                            let mut lits = Vec::new();
                            for (a, t) in args.iter().zip(&params) {
                                lits.extend(value_from_py(a, t, &s, None, &name).ok().as_ref().and_then(value_literal));
                            }
                            let res =
                                if ok { value_from_py(&r, &result, &s, None, &name).ok().as_ref().and_then(value_literal) } else { None };
                            if lits.len() != params.len() || (ok && res.is_none()) {
                                out.clear();
                                break;
                            }
                            out.push((lits, res));
                        }
                        (!out.is_empty()).then_some(out)
                    }
                    None => None,
                };
                contracts.push((id.clone(), names, params.clone(), result.clone(), src, total, table));
            }
            s.add_function(FunctionDecl { name, overloads: vec![Overload { id, receiver, params, result }] })
                .map_err(PyValueError::new_err)?;
        }
        // contracts see the structs, the parameters and `result`; never other functions (no recursion)
        for (id, names, params, result, src, total, table) in contracts {
            let Some(src) = src else {
                s.contracts.insert(id, Arc::new(Contract { params: names, ensures: None, total, table }));
                continue;
            };
            let mut cs = Schema::with_stdlib();
            cs.structs = s.structs.clone();
            for (n, t) in names.iter().zip(params).chain([(&"result".to_string(), result)]) {
                cs.vars.insert(n.clone(), VarDecl { name: n.clone(), ty: t, constraints: Constraints::default() });
            }
            let ensures = compile_source(&Arc::new(cs), &BTreeMap::new(), &src)?;
            if *ensures.output_type() != CelType::Bool {
                return Err(PyValueError::new_err(format!("ensures for '{id}' must be a bool expression, not {}", ensures.output_type())));
            }
            s.contracts.insert(id, Arc::new(Contract { params: names, ensures: Some(ensures), total, table }));
        }
        // definitions in order: each sees the ones before it. A definition with parameters
        // is checked with them as variables, and declared as a function returning its type.
        let mut defmap = BTreeMap::new();
        for (name, src, params) in defs {
            if s.vars.contains_key(&name) {
                return Err(PyValueError::new_err(format!("definition '{name}' shadows a variable")));
            }
            match params {
                None => {
                    let checked = compile_source(&Arc::new(s.clone()), &defmap, &src)?;
                    defmap.insert(name, Definition::constant(checked.expr));
                }
                Some(params) => {
                    let mut ds = s.clone();
                    let mut names = Vec::new();
                    let mut types = Vec::new();
                    for (p, t) in &params {
                        let ty = type_from_py(t)?;
                        ds.vars.insert(p.clone(), VarDecl { name: p.clone(), ty: ty.clone(), constraints: Constraints::default() });
                        names.push(p.clone());
                        types.push(ty);
                    }
                    let checked = compile_source(&Arc::new(ds), &defmap, &src)?;
                    let result = checked.output_type().clone();
                    s.add_function(FunctionDecl {
                        name: name.clone(),
                        overloads: vec![Overload { id: format!("{name}_def"), receiver: false, params: types, result }],
                    })
                    .map_err(PyValueError::new_err)?;
                    // the body as written (parameters by their own names); expansion renames them
                    let body = parse(&src).map_err(|e| compile_err("syntax", &src, vec![(e.message, e.span)]))?;
                    defmap.insert(name, Definition { params: Some(names), body });
                }
            }
        }
        let readers = readers.unwrap_or_default();
        for (st, fields) in &readers {
            let Some(decl) = s.structs.get(st) else {
                return Err(PyValueError::new_err(format!("readers given for unknown struct '{st}'")));
            };
            if let Some(f) = fields.iter().find(|f| !decl.fields.iter().any(|d| &d.name == *f)) {
                return Err(PyValueError::new_err(format!("reader given for unknown field '{st}.{f}'")));
            }
        }
        let schema = Arc::new(s);
        Ok(Core { schema, defs: defmap })
    }

    fn compile(&self, source: &str) -> PyResult<Program> {
        let checked = compile_source(&self.schema, &self.defs, source)?;
        Ok(Program { checked: Arc::new(checked), source: source.to_string() })
    }

    /// Type of a definition (for diagnostics / docs).
    fn definition_names(&self) -> Vec<String> {
        self.defs.keys().cloned().collect()
    }
}

#[pyclass(frozen, module = "celspresso._celspresso")]
struct Program {
    checked: Arc<CheckedExpr>,
    source: String,
}

/// (max_cost, max_iterations, max_string_len, max_list_len, max_regex_size) from Python.
type LimitsSpec = (u64, u64, usize, usize, usize);

fn limits(spec: Option<LimitsSpec>) -> Limits {
    match spec {
        Some((max_cost, max_iterations, max_string_len, max_list_len, max_regex_size)) => {
            Limits { max_cost, max_iterations, max_string_len, max_list_len, max_regex_size }
        }
        None => Limits::default(),
    }
}

fn activation(py_vars: &Bound<'_, PyDict>, schema: &Schema, readers: Readers) -> PyResult<HashMap<String, Value>> {
    let mut act = HashMap::new();
    for (k, v) in py_vars.iter() {
        let name: String = k.extract()?;
        let val = match schema.vars.get(&name) {
            Some(d) => {
                let val = value_from_py(&v, &d.ty, schema, readers, &name)?;
                // proofs assume the schema's constraints, so evaluation enforces them
                celspresso_eval::validate::validate(&val, &d.ty, &d.constraints, schema, &name).map_err(PyValueError::new_err)?;
                val
            }
            None => continue, // extra keys are ignored
        };
        act.insert(name, val);
    }
    Ok(act)
}

#[pymethods]
impl Program {
    #[getter]
    fn source(&self) -> &str {
        &self.source
    }
    #[getter]
    fn canonical(&self) -> String {
        unparse(&self.checked.expr)
    }
    #[getter]
    fn output_type<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        type_to_py(py, self.checked.output_type())
    }
    #[getter]
    fn output_type_name(&self) -> String {
        self.checked.output_type().to_string()
    }
    #[getter]
    fn references(&self) -> Vec<String> {
        self.checked.references()
    }
    /// Warnings: (message, start, end, rendered) for code that type-checks but looks wrong.
    fn lint(&self) -> Vec<(String, usize, usize, String)> {
        let len = self.source.len() as u32;
        celspresso_check::lint::lint(&self.checked)
            .into_iter()
            .filter(|w| w.span.end <= len) // spans from expanded definitions point elsewhere
            .map(|w| {
                let (a, b) = span_chars(&self.source, w.span);
                let rendered = render_diagnostic(&self.source, w.span, &w.message);
                (w.message, a, b, rendered)
            })
            .collect()
    }

    #[pyo3(signature = (vars, functions=None, limits=None, readers=None))]
    fn evaluate<'py>(
        &self,
        py: Python<'py>,
        vars: &Bound<'py, PyDict>,
        functions: Option<&Bound<'py, PyDict>>,
        limits: Option<LimitsSpec>,
        readers: Option<&Bound<'py, PyDict>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let act = activation(vars, &self.checked.schema, readers)?;
        let funcs = PyFunctions::from_dict(functions)?;
        match evaluate(&self.checked, &act, &funcs, self::limits(limits)) {
            Ok(v) => value_to_py(py, &v),
            Err(e) => Err(self.eval_error(e.message, e.expr_id)),
        }
    }

    /// Returns (ok, value_or_message, [(start, end, ok, value_or_message)] in pre-order).
    #[pyo3(signature = (vars, functions=None, limits=None, readers=None))]
    fn explain<'py>(
        &self,
        py: Python<'py>,
        vars: &Bound<'py, PyDict>,
        functions: Option<&Bound<'py, PyDict>>,
        limits: Option<LimitsSpec>,
        readers: Option<&Bound<'py, PyDict>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let act = activation(vars, &self.checked.schema, readers)?;
        let funcs = PyFunctions::from_dict(functions)?;
        let (r, trace) = evaluate_traced(&self.checked, &act, &funcs, self::limits(limits));
        let nodes = PyList::empty(py);
        let mut err = None;
        self.checked.expr.walk(&mut |e| {
            if err.is_some() {
                return;
            }
            if let Some(res) = trace.get(&e.id) {
                let (a, b) = span_chars(&self.source, e.span);
                let item = match res {
                    Ok(v) => value_to_py(py, v).and_then(|pv| (a, b, true, pv).into_bound_py_any(py)),
                    Err(m) => (a, b, false, m.as_str()).into_bound_py_any(py),
                };
                match item.and_then(|i| nodes.append(i)) {
                    Ok(()) => {}
                    Err(e) => err = Some(e),
                }
            }
        });
        if let Some(e) = err {
            return Err(e);
        }
        let head = match r {
            Ok(v) => (true, value_to_py(py, &v)?),
            Err(e) => (false, e.message.into_bound_py_any(py)?),
        };
        (head.0, head.1, nodes).into_bound_py_any(py)
    }
}

impl Program {
    fn eval_error(&self, message: String, expr_id: u32) -> PyErr {
        let mut span = Span::new(0, self.source.len());
        self.checked.expr.walk(&mut |e| {
            if e.id == expr_id {
                span = e.span;
            }
        });
        let (a, b) = span_chars(&self.source, span);
        let rendered = render_diagnostic(&self.source, span, &message);
        EvalError::new_err((message, expr_id, a, b, rendered))
    }
}

/// kind: satisfiable | always_true | equivalent | implies | can_error
#[pyfunction]
#[pyo3(signature = (kind, a, b, assumptions, timeout_ms, unroll_limit, schema_constraints, errors, functions=None, sample_proofs=0))]
#[allow(clippy::too_many_arguments)]
fn verify<'py>(
    py: Python<'py>,
    kind: &str,
    a: PyRef<'py, Program>,
    b: Option<PyRef<'py, Program>>,
    assumptions: Vec<PyRef<'py, Program>>,
    timeout_ms: u64,
    unroll_limit: usize,
    schema_constraints: bool,
    errors: &str,
    functions: Option<&Bound<'py, PyDict>>,
    sample_proofs: usize,
) -> PyResult<Bound<'py, PyDict>> {
    let mode = match errors {
        "strict" => ErrorMode::Strict,
        "as_false" => ErrorMode::AsFalse,
        other => return Err(PyValueError::new_err(format!("errors must be 'strict' or 'as_false', not {other:?}"))),
    };
    let ae = a.checked.clone();
    let be = b.as_ref().map(|p| p.checked.clone());
    let asm: Vec<Arc<CheckedExpr>> = assumptions.iter().map(|p| p.checked.clone()).collect();
    let need_b = || be.clone().ok_or_else(|| PyValueError::new_err(format!("'{kind}' needs two expressions")));
    let kind_owned = kind.to_string();
    let bb = if matches!(kind, "equivalent" | "implies") { Some(need_b()?) } else { None };
    let funcs = PyFunctions::from_dict(functions)?;
    let opts = Options { timeout_ms, unroll_limit, schema_constraints, sample_proofs };
    let out = py.detach(|| {
        let refs: Vec<&CheckedExpr> = asm.iter().map(|x| x.as_ref()).collect();
        let q = match kind_owned.as_str() {
            "satisfiable" => Query::Satisfiable(&ae),
            "always_true" => Query::AlwaysTrue(&ae),
            "can_error" => Query::CanError(&ae),
            "equivalent" => Query::Equivalent(&ae, bb.as_ref().unwrap(), mode),
            "implies" => Query::Implies(&ae, bb.as_ref().unwrap()),
            _ => return None,
        };
        Some(run_verify(&q, &refs, opts, &funcs))
    });
    let out = out.ok_or_else(|| PyValueError::new_err(format!("unknown verification kind '{kind}'")))?;
    let d = PyDict::new(py);
    match &out.status {
        Status::Found(w) => {
            d.set_item("status", "found")?;
            let wd = PyDict::new(py);
            for (k, v) in w {
                wd.set_item(k, value_to_py(py, v)?)?;
            }
            d.set_item("witness", wd)?;
            d.set_item("reason", py.None())?;
        }
        Status::NotFound => {
            d.set_item("status", "not_found")?;
            d.set_item("witness", py.None())?;
            d.set_item("reason", py.None())?;
        }
        Status::Unknown(r) => {
            d.set_item("status", "unknown")?;
            d.set_item("witness", py.None())?;
            d.set_item("reason", r)?;
        }
    }
    d.set_item("bounded", out.bounded)?;
    d.set_item("elapsed_ms", out.elapsed_ms)?;
    d.set_item("approximations", out.approximations.clone())?;
    Ok(d)
}

/// The range of a numeric expression: {min, max: {value, witness, attained, sound} | None, reason, ...}.
#[pyfunction]
#[pyo3(signature = (a, assumptions, timeout_ms, unroll_limit, schema_constraints, functions=None))]
fn bounds<'py>(
    py: Python<'py>,
    a: PyRef<'py, Program>,
    assumptions: Vec<PyRef<'py, Program>>,
    timeout_ms: u64,
    unroll_limit: usize,
    schema_constraints: bool,
    functions: Option<&Bound<'py, PyDict>>,
) -> PyResult<Bound<'py, PyDict>> {
    let sample_proofs = 0;
    let ae = a.checked.clone();
    let asm: Vec<Arc<CheckedExpr>> = assumptions.iter().map(|p| p.checked.clone()).collect();
    let funcs = PyFunctions::from_dict(functions)?;
    let opts = Options { timeout_ms, unroll_limit, schema_constraints, sample_proofs };
    let out = py.detach(|| {
        let refs: Vec<&CheckedExpr> = asm.iter().map(|x| x.as_ref()).collect();
        run_bounds(&ae, &refs, opts, &funcs)
    });
    let extreme = |x: &Option<Extreme>| -> PyResult<Py<PyAny>> {
        let Some(x) = x else { return Ok(py.None()) };
        let d = PyDict::new(py);
        d.set_item("value", value_to_py(py, &x.value)?)?;
        let wd = PyDict::new(py);
        for (k, v) in &x.witness {
            wd.set_item(k, value_to_py(py, v)?)?;
        }
        d.set_item("witness", wd)?;
        d.set_item("attained", x.attained)?;
        d.set_item("sound", x.sound)?;
        Ok(d.into_any().unbind())
    };
    let d = PyDict::new(py);
    d.set_item("min", extreme(&out.min)?)?;
    d.set_item("max", extreme(&out.max)?)?;
    d.set_item("reason", out.reason.clone())?;
    d.set_item("bounded", out.bounded)?;
    d.set_item("elapsed_ms", out.elapsed_ms)?;
    d.set_item("approximations", out.approximations.clone())?;
    Ok(d)
}

/// Why `pattern` is not a usable schema pattern (`None` if it is).
#[pyfunction]
fn pattern_error(pattern: &str) -> Option<String> {
    celspresso_eval::validate::pattern_error(pattern)
}

#[pymodule]
fn _celspresso(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(bounds, m)?)?;
    m.add_class::<Core>()?;
    m.add_class::<Program>()?;
    m.add_function(wrap_pyfunction!(verify, m)?)?;
    m.add_function(wrap_pyfunction!(pattern_error, m)?)?;
    m.add("CompileError", m.py().get_type::<CompileError>())?;
    m.add("EvalError", m.py().get_type::<EvalError>())?;
    Ok(())
}
