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
        // extension libraries add overloads to core names (`string(net.IP)`): merge them
        for f in stdlib() {
            match s.functions.get_mut(&f.name) {
                Some(existing) => existing.overloads.extend(f.overloads),
                None => {
                    s.functions.insert(f.name.clone(), f);
                }
            }
        }
        s
    }

    /// Register a function, or more overloads of an existing one. Fails if an overload
    /// would be indistinguishable from one already declared (same receiver style and
    /// parameter types), e.g. a custom `double(int)` clashing with the builtin conversion.
    pub fn add_function(&mut self, f: FunctionDecl) -> Result<(), String> {
        if let Some(existing) = self.functions.get(&f.name) {
            for new in &f.overloads {
                if let Some(old) = existing.overloads.iter().find(|o| o.receiver == new.receiver && o.params == new.params) {
                    let params = new.params.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(", ");
                    return Err(format!(
                        "function '{}({params})' clashes with existing overload '{}'; choose another name",
                        f.name, old.id
                    ));
                }
            }
        }
        match self.functions.get_mut(&f.name) {
            Some(existing) => existing.overloads.extend(f.overloads),
            None => {
                self.functions.insert(f.name.clone(), f);
            }
        }
        Ok(())
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
        func(
            ops::MAP_INSERT,
            vec![
                ov("map_insert_entry", vec![mkv(), k(), v()], mkv()),
                ov("map_insert_map", vec![mkv(), mkv()], mkv()),
            ],
        ),
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
                ov("add_timestamp_duration", vec![Timestamp, Duration], Timestamp),
                ov("add_duration_timestamp", vec![Duration, Timestamp], Timestamp),
                ov("add_duration_duration", vec![Duration, Duration], Duration),
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
                ov("subtract_timestamp_timestamp", vec![Timestamp, Timestamp], Duration),
                ov("subtract_timestamp_duration", vec![Timestamp, Duration], Timestamp),
                ov("subtract_duration_duration", vec![Duration, Duration], Duration),
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
                ov("timestamp_to_int64", vec![Timestamp], Int),
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
                ov("timestamp_to_string", vec![Timestamp], String),
                ov("duration_to_string", vec![Duration], String),
            ],
        ),
        func("bytes", vec![ov("string_to_bytes", vec![String], Bytes), ov("bytes_to_bytes", vec![Bytes], Bytes)]),
        func("bool", vec![ov("bool_to_bool", vec![Bool], Bool), ov("string_to_bool", vec![String], Bool)]),
        func("dyn", vec![ov("to_dyn", vec![a()], Dyn)]),
        func("type", vec![ov("type", vec![a()], Type(Box::new(a())))]),
        func(
            "timestamp",
            vec![
                ov("string_to_timestamp", vec![String], Timestamp),
                ov("int64_to_timestamp", vec![Int], Timestamp),
                ov("timestamp_to_timestamp", vec![Timestamp], Timestamp),
            ],
        ),
        func(
            "duration",
            vec![ov("string_to_duration", vec![String], Duration), ov("duration_to_duration", vec![Duration], Duration)],
        ),
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

    // timestamp accessors, each with an optional time zone argument
    for (name, id) in [
        ("getFullYear", "full_year"),
        ("getMonth", "month"),
        ("getDate", "date"),
        ("getDayOfMonth", "day_of_month"),
        ("getDayOfWeek", "day_of_week"),
        ("getDayOfYear", "day_of_year"),
        ("getHours", "hours"),
        ("getMinutes", "minutes"),
        ("getSeconds", "seconds"),
        ("getMilliseconds", "milliseconds"),
    ] {
        let mut overloads = vec![
            rov(&format!("timestamp_to_{id}"), vec![Timestamp], Int),
            rov(&format!("timestamp_to_{id}_with_tz"), vec![Timestamp, String], Int),
        ];
        if matches!(id, "hours" | "minutes" | "seconds" | "milliseconds") {
            overloads.push(rov(&format!("duration_to_{id}"), vec![Duration], Int));
        }
        fns.push(func(name, overloads));
    }

    // ordering over every comparable type, plus cross-type numeric comparisons
    let cmp_types: [(&str, CelType); 9] = [
        ("int64", Int),
        ("uint64", Uint),
        ("double", Double),
        ("string", String),
        ("bytes", Bytes),
        ("bool", Bool),
        ("date", Date),
        ("timestamp", Timestamp),
        ("duration", Duration),
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
    fns.extend(extensions());
    fns
}

/// cel-go's extension libraries: strings, math, lists, sets and encoders.
/// `math.greatest` / `math.least` are variadic and typed by the checker directly.
fn extensions() -> Vec<FunctionDecl> {
    use CelType::*;
    let ip = || Opaque("net.IP".into());
    let cidr = || Opaque("net.CIDR".into());
    let mut fns = vec![
        func("ip", vec![ov("string_to_ip", vec![String], ip()), rov("cidr_ip", vec![cidr()], ip())]),
        func("cidr", vec![ov("string_to_cidr", vec![String], cidr())]),
        func("isIP", vec![ov("is_ip", vec![String], Bool)]),
        func("isCIDR", vec![ov("is_cidr", vec![String], Bool)]),
        func("ip.isCanonical", vec![ov("ip_is_canonical", vec![String], Bool)]),
        func("string", vec![ov("ip_to_string", vec![ip()], String), ov("cidr_to_string", vec![cidr()], String)]),
        func("family", vec![rov("ip_family", vec![ip()], Int)]),
        func("containsIP", vec![rov("cidr_contains_ip_ip", vec![cidr(), ip()], Bool), rov("cidr_contains_ip_string", vec![cidr(), String], Bool)]),
        func("containsCIDR", vec![rov("cidr_contains_cidr", vec![cidr(), cidr()], Bool), rov("cidr_contains_cidr_string", vec![cidr(), String], Bool)]),
        func("masked", vec![rov("cidr_masked", vec![cidr()], cidr())]),
        func("prefixLength", vec![rov("cidr_prefix_length", vec![cidr()], Int)]),
    ];
    for pred in ["isUnspecified", "isLoopback", "isGlobalUnicast", "isLinkLocalMulticast", "isLinkLocalUnicast"] {
        fns.push(func(pred, vec![rov(&format!("ip_{pred}"), vec![ip()], Bool)]));
    }
    fns.extend(core_extensions());
    fns
}

fn core_extensions() -> Vec<FunctionDecl> {
    use CelType::*;
    let la = || CelType::list(CelType::p("A"));
    let ls = || CelType::list(String);
    let num1 = |name: &str, id: &str| {
        func(
            name,
            vec![
                ov(&format!("{id}_int"), vec![Int], Int),
                ov(&format!("{id}_uint"), vec![Uint], Uint),
                ov(&format!("{id}_double"), vec![Double], Double),
            ],
        )
    };
    let dbl = |name: &str, id: &str, out: CelType| func(name, vec![ov(id, vec![Double], out)]);
    let bits2 = |name: &str, id: &str| {
        func(name, vec![ov(&format!("{id}_int_int"), vec![Int, Int], Int), ov(&format!("{id}_uint_uint"), vec![Uint, Uint], Uint)])
    };
    let shift = |name: &str, id: &str| {
        func(name, vec![ov(&format!("{id}_int_int"), vec![Int, Int], Int), ov(&format!("{id}_uint_int"), vec![Uint, Int], Uint)])
    };
    let set_op = |name: &str, id: &str| func(name, vec![ov(id, vec![la(), la()], Bool)]);
    vec![
        // optionals
        func("optional.of", vec![ov("optional_of", vec![CelType::p("A")], CelType::optional(CelType::p("A")))]),
        func("optional.ofNonZeroValue", vec![ov("optional_ofNonZeroValue", vec![CelType::p("A")], CelType::optional(CelType::p("A")))]),
        func("optional.none", vec![ov("optional_none", vec![], CelType::optional(CelType::p("A")))]),
        func("hasValue", vec![rov("optional_hasValue", vec![CelType::optional(CelType::p("A"))], Bool)]),
        func("value", vec![rov("optional_value", vec![CelType::optional(CelType::p("A"))], CelType::p("A"))]),
        func("or", vec![rov("optional_or_optional", vec![CelType::optional(CelType::p("A")), CelType::optional(CelType::p("A"))], CelType::optional(CelType::p("A")))]),
        func("orValue", vec![rov("optional_orValue_value", vec![CelType::optional(CelType::p("A")), CelType::p("A")], CelType::p("A"))]),
        // math (greatest/least have no fixed signature; the checker types them)
        func("math.greatest", vec![]),
        func("math.least", vec![]),
        dbl("math.ceil", "math_ceil_double", Double),
        dbl("math.floor", "math_floor_double", Double),
        dbl("math.round", "math_round_double", Double),
        dbl("math.trunc", "math_trunc_double", Double),
        dbl("math.isNaN", "math_isNaN_double", Bool),
        dbl("math.isInf", "math_isInf_double", Bool),
        dbl("math.isFinite", "math_isFinite_double", Bool),
        num1("math.abs", "math_abs"),
        num1("math.sign", "math_sign"),
        bits2("math.bitAnd", "math_bitAnd"),
        bits2("math.bitOr", "math_bitOr"),
        bits2("math.bitXor", "math_bitXor"),
        func("math.bitNot", vec![ov("math_bitNot_int_int", vec![Int], Int), ov("math_bitNot_uint_uint", vec![Uint], Uint)]),
        shift("math.bitShiftLeft", "math_bitShiftLeft"),
        shift("math.bitShiftRight", "math_bitShiftRight"),
        // strings
        func("charAt", vec![rov("string_char_at_int", vec![String, Int], String)]),
        func(
            "indexOf",
            vec![
                rov("string_index_of_string", vec![String, String], Int),
                rov("string_index_of_string_int", vec![String, String, Int], Int),
            ],
        ),
        func(
            "lastIndexOf",
            vec![
                rov("string_last_index_of_string", vec![String, String], Int),
                rov("string_last_index_of_string_int", vec![String, String, Int], Int),
            ],
        ),
        func(
            "substring",
            vec![
                rov("string_substring_int", vec![String, Int], String),
                rov("string_substring_int_int", vec![String, Int, Int], String),
            ],
        ),
        func(
            "replace",
            vec![
                rov("string_replace_string_string", vec![String, String, String], String),
                rov("string_replace_string_string_int", vec![String, String, String, Int], String),
            ],
        ),
        func(
            "split",
            vec![rov("string_split_string", vec![String, String], ls()), rov("string_split_string_int", vec![String, String, Int], ls())],
        ),
        func("join", vec![rov("list_join", vec![ls()], String), rov("list_join_string", vec![ls(), String], String)]),
        func("reverse", vec![rov("string_reverse", vec![String], String), rov("list_reverse", vec![la()], la())]),
        func("format", vec![rov("string_format", vec![String, CelType::list(Dyn)], String)]),
        func("strings.quote", vec![ov("strings_quote", vec![String], String)]),
        // lists
        func("sort", vec![rov("list_sort", vec![la()], la())]),
        func("@sortByAssociatedKeys", vec![ov("list_sort_by_associated_keys", vec![la(), CelType::list(Dyn)], la())]),
        func("slice", vec![rov("list_slice", vec![la(), Int, Int], la())]),
        func("distinct", vec![rov("list_distinct", vec![la()], la())]),
        func(
            "flatten",
            vec![
                rov("list_flatten", vec![CelType::list(la())], la()),
                rov("list_flatten_int", vec![CelType::list(Dyn), Int], CelType::list(Dyn)),
            ],
        ),
        func("lists.range", vec![ov("lists_range", vec![Int], CelType::list(Int))]),
        // sets
        set_op("sets.contains", "list_sets_contains_list"),
        set_op("sets.equivalent", "list_sets_equivalent_list"),
        set_op("sets.intersects", "list_sets_intersects_list"),
        // encoders
        func("base64.encode", vec![ov("base64_encode_bytes", vec![Bytes], String)]),
        func("base64.decode", vec![ov("base64_decode_string", vec![String], Bytes)]),
    ]
}
