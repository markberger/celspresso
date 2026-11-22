//! Declarations: schema (structs, variables, constraints) and function overloads.

use crate::types::CelType;
use celspresso_syntax::Literal;
use std::collections::BTreeMap;

/// Value constraints from the schema (Pydantic `Field(ge=..)`, `Literal[..]`, ...).
/// They are used as solver assumptions and never change evaluation semantics.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Constraints {
    pub ge: Option<f64>,
    pub gt: Option<f64>,
    pub le: Option<f64>,
    pub lt: Option<f64>,
    pub min_length: Option<u64>,
    pub max_length: Option<u64>,
    /// Allowed values (`Literal[...]`, `Enum`).
    pub one_of: Option<Vec<Literal>>,
    /// Regex pattern (RE2 syntax).
    pub pattern: Option<String>,
    /// Constraints that apply to each element of a list field.
    pub items: Option<Box<Constraints>>,
}

impl Constraints {
    pub fn is_empty(&self) -> bool {
        *self == Constraints::default()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldDecl {
    pub name: String,
    pub ty: CelType,
    pub constraints: Constraints,
}

#[derive(Clone, Debug, PartialEq)]
pub struct StructDecl {
    pub name: String,
    pub fields: Vec<FieldDecl>,
}

impl StructDecl {
    pub fn field(&self, name: &str) -> Option<&FieldDecl> {
        self.fields.iter().find(|f| f.name == name)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct VarDecl {
    pub name: String,
    pub ty: CelType,
    pub constraints: Constraints,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Overload {
    pub id: String,
    pub receiver: bool,
    pub params: Vec<CelType>,
    pub result: CelType,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDecl {
    pub name: String,
    pub overloads: Vec<Overload>,
}

/// The type environment the checker resolves against.
#[derive(Clone, Debug, Default)]
pub struct Schema {
    pub structs: BTreeMap<String, StructDecl>,
    pub vars: BTreeMap<String, VarDecl>,
    pub functions: BTreeMap<String, FunctionDecl>,
}

impl Schema {
    pub fn with_stdlib() -> Schema {
        let mut s = Schema::default();
        for f in stdlib() {
            s.functions.insert(f.name.clone(), f);
        }
        s
    }

    pub fn add_function(&mut self, f: FunctionDecl) {
        match self.functions.get_mut(&f.name) {
            Some(existing) => existing.overloads.extend(f.overloads),
            None => {
                self.functions.insert(f.name.clone(), f);
            }
        }
    }
}

fn ov(id: &str, params: Vec<CelType>, result: CelType) -> Overload {
    Overload { id: id.to_string(), receiver: false, params, result }
}

fn rov(id: &str, params: Vec<CelType>, result: CelType) -> Overload {
    Overload { id: id.to_string(), receiver: true, params, result }
}

fn func(name: &str, overloads: Vec<Overload>) -> FunctionDecl {
    FunctionDecl { name: name.to_string(), overloads }
}

/// Standard library declarations (cel-go overload ids).
pub fn stdlib() -> Vec<FunctionDecl> {
    use celspresso_syntax::ast::ops;
    use CelType::*;
    let a = || CelType::p("A");
    let k = || CelType::p("K");
    let v = || CelType::p("V");
    let la = || CelType::list(CelType::p("A"));
    let mkv = || CelType::map(CelType::p("K"), CelType::p("V"));

    let mut fns = vec![
        func(ops::LOGICAL_AND, vec![ov("logical_and", vec![Bool, Bool], Bool)]),
        func(ops::LOGICAL_OR, vec![ov("logical_or", vec![Bool, Bool], Bool)]),
        func(ops::LOGICAL_NOT, vec![ov("logical_not", vec![Bool], Bool)]),
        func(ops::NOT_STRICTLY_FALSE, vec![ov("not_strictly_false", vec![Bool], Bool)]),
        func(ops::CONDITIONAL, vec![ov("conditional", vec![Bool, a(), a()], a())]),
        func(ops::NEGATE, vec![ov("negate_int64", vec![Int], Int), ov("negate_double", vec![Double], Double)]),
        func(
            ops::ADD,
            vec![
                ov("add_int64", vec![Int, Int], Int),
                ov("add_uint64", vec![Uint, Uint], Uint),
                ov("add_double", vec![Double, Double], Double),
                ov("add_string", vec![String, String], String),
                ov("add_bytes", vec![Bytes, Bytes], Bytes),
                ov("add_list", vec![la(), la()], la()),
                ov("add_date_int64", vec![Date, Int], Date),
            ],
        ),
        func(
            ops::SUBTRACT,
            vec![
                ov("subtract_int64", vec![Int, Int], Int),
                ov("subtract_uint64", vec![Uint, Uint], Uint),
                ov("subtract_double", vec![Double, Double], Double),
                ov("subtract_date_date", vec![Date, Date], Int),
                ov("subtract_date_int64", vec![Date, Int], Date),
            ],
        ),
        func(
            ops::MULTIPLY,
            vec![
                ov("multiply_int64", vec![Int, Int], Int),
                ov("multiply_uint64", vec![Uint, Uint], Uint),
                ov("multiply_double", vec![Double, Double], Double),
            ],
        ),
        func(
            ops::DIVIDE,
            vec![
                ov("divide_int64", vec![Int, Int], Int),
                ov("divide_uint64", vec![Uint, Uint], Uint),
                ov("divide_double", vec![Double, Double], Double),
            ],
        ),
        func(ops::MODULO, vec![ov("modulo_int64", vec![Int, Int], Int), ov("modulo_uint64", vec![Uint, Uint], Uint)]),
        func(ops::EQUALS, vec![ov("equals", vec![a(), a()], Bool)]),
        func(ops::NOT_EQUALS, vec![ov("not_equals", vec![a(), a()], Bool)]),
        func(ops::INDEX, vec![ov("index_list", vec![la(), Int], a()), ov("index_map", vec![mkv(), k()], v())]),
        func(ops::IN, vec![ov("in_list", vec![a(), la()], Bool), ov("in_map", vec![k(), mkv()], Bool)]),
        func(
            "size",
            vec![
                ov("size_string", vec![String], Int),
                ov("size_bytes", vec![Bytes], Int),
                ov("size_list", vec![la()], Int),
                ov("size_map", vec![mkv()], Int),
                rov("string_size", vec![String], Int),
                rov("bytes_size", vec![Bytes], Int),
                rov("list_size", vec![la()], Int),
                rov("map_size", vec![mkv()], Int),
            ],
        ),
        func("contains", vec![rov("contains_string", vec![String, String], Bool)]),
        func("startsWith", vec![rov("starts_with_string", vec![String, String], Bool)]),
        func("endsWith", vec![rov("ends_with_string", vec![String, String], Bool)]),
        func(
            "matches",
            vec![ov("matches", vec![String, String], Bool), rov("matches_string", vec![String, String], Bool)],
        ),
        func("lowerAscii", vec![rov("string_lower_ascii", vec![String], String)]),
        func("upperAscii", vec![rov("string_upper_ascii", vec![String], String)]),
        func("trim", vec![rov("string_trim", vec![String], String)]),
        func(
            "int",
            vec![
                ov("int64_to_int64", vec![Int], Int),
                ov("uint64_to_int64", vec![Uint], Int),
                ov("double_to_int64", vec![Double], Int),
                ov("string_to_int64", vec![String], Int),
            ],
        ),
        func(
            "uint",
            vec![
                ov("uint64_to_uint64", vec![Uint], Uint),
                ov("int64_to_uint64", vec![Int], Uint),
                ov("double_to_uint64", vec![Double], Uint),
                ov("string_to_uint64", vec![String], Uint),
            ],
        ),
        func(
            "double",
            vec![
                ov("double_to_double", vec![Double], Double),
                ov("int64_to_double", vec![Int], Double),
                ov("uint64_to_double", vec![Uint], Double),
                ov("string_to_double", vec![String], Double),
            ],
        ),
        func(
            "string",
            vec![
                ov("string_to_string", vec![String], String),
                ov("int64_to_string", vec![Int], String),
                ov("uint64_to_string", vec![Uint], String),
                ov("double_to_string", vec![Double], String),
                ov("bool_to_string", vec![Bool], String),
                ov("bytes_to_string", vec![Bytes], String),
                ov("date_to_string", vec![Date], String),
            ],
        ),
        func("bytes", vec![ov("string_to_bytes", vec![String], Bytes), ov("bytes_to_bytes", vec![Bytes], Bytes)]),
        func("bool", vec![ov("bool_to_bool", vec![Bool], Bool), ov("string_to_bool", vec![String], Bool)]),
        func("dyn", vec![ov("to_dyn", vec![a()], Dyn)]),
        // list extensions
        func(
            "sum",
            vec![
                rov("list_sum_int64", vec![CelType::list(Int)], Int),
                rov("list_sum_uint64", vec![CelType::list(Uint)], Uint),
                rov("list_sum_double", vec![CelType::list(Double)], Double),
            ],
        ),
        func(
            "min",
            vec![
                rov("list_min_int64", vec![CelType::list(Int)], Int),
                rov("list_min_uint64", vec![CelType::list(Uint)], Uint),
                rov("list_min_double", vec![CelType::list(Double)], Double),
            ],
        ),
        func(
            "max",
            vec![
                rov("list_max_int64", vec![CelType::list(Int)], Int),
                rov("list_max_uint64", vec![CelType::list(Uint)], Uint),
                rov("list_max_double", vec![CelType::list(Double)], Double),
            ],
        ),
        // date extension
        func("date", vec![ov("string_to_date", vec![String], Date)]),
        func("ageOn", vec![rov("date_age_on", vec![Date, Date], Int)]),
        func("daysUntil", vec![rov("date_days_until", vec![Date, Date], Int)]),
        func("year", vec![rov("date_year", vec![Date], Int)]),
    ];

    // ordering over every comparable type, plus cross-type numeric comparisons
    let cmp_types: [(&str, CelType); 7] = [
        ("int64", Int),
        ("uint64", Uint),
        ("double", Double),
        ("string", String),
        ("bytes", Bytes),
        ("bool", Bool),
        ("date", Date),
    ];
    let numeric: [(&str, CelType); 3] = [("int64", Int), ("uint64", Uint), ("double", Double)];
    for (op, name) in [
        (ops::LESS, "less"),
        (ops::LESS_EQUALS, "less_equals"),
        (ops::GREATER, "greater"),
        (ops::GREATER_EQUALS, "greater_equals"),
    ] {
        let mut overloads: Vec<Overload> = cmp_types
            .iter()
            .map(|(n, t)| ov(&format!("{name}_{n}"), vec![t.clone(), t.clone()], Bool))
            .collect();
        for (n1, t1) in &numeric {
            for (n2, t2) in &numeric {
                if n1 != n2 {
                    overloads.push(ov(&format!("{name}_{n1}_{n2}"), vec![t1.clone(), t2.clone()], Bool));
                }
            }
        }
        fns.push(func(op, overloads));
    }
    fns
}
