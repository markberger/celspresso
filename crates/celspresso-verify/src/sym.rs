//! Symbolic CEL values.
//!
//! Unlike cel-java's single `CelValue` datatype, we exploit the checked types:
//! every expression has a static type, so we encode it with a native Z3 sort
//! plus an error flag. Lists are bounded sequences of (live, element) slots so
//! that `filter` and conditional appends stay cheap; structs are flattened.

use celspresso_check::CelType;
use std::collections::BTreeMap;
use z3::ast::{Bool, Float, Int, String as ZStr};

#[derive(Clone, Debug)]
pub enum Sym {
    Bool(Bool),
    Int(Int),
    Uint(Int),
    /// IEEE-754 binary64.
    Double(Float),
    Str(ZStr),
    /// Day number.
    Date(Int),
    /// Nanoseconds since the Unix epoch.
    Timestamp(Int),
    /// Signed nanoseconds.
    Duration(Int),
    Null,
    /// `T?`: `inner` is meaningful only when `!is_null`.
    Nullable {
        is_null: Bool,
        inner: Box<Sym>,
    },
    /// Bounded list: ordered slots, an element is present iff its `live` flag holds.
    List {
        slots: Vec<(Bool, Sym)>,
        elem: CelType,
        trunc: bool,
    },
    Struct {
        name: String,
        fields: BTreeMap<String, Sym>,
    },
    /// `optional_type`: `val` is meaningful only when `has`.
    Optional {
        has: Bool,
        val: Box<Sym>,
    },
    /// Bounded map: slots of (live, key, value); the keys of live slots are distinct.
    Map {
        slots: Vec<(Bool, Sym, Sym)>,
        key: CelType,
        val: CelType,
        trunc: bool,
    },
    /// A value of a type the verifier does not model precisely (e.g. double,
    /// map). Opaque values are fresh and only support identity comparison.
    Opaque {
        ty: CelType,
        id: Int,
    },
}

/// A symbolic value together with "this evaluation produced an error".
#[derive(Clone, Debug)]
pub struct SV {
    pub v: Sym,
    pub err: Bool,
}

pub fn tt() -> Bool {
    Bool::from_bool(true)
}
pub fn ff() -> Bool {
    Bool::from_bool(false)
}
pub fn and(xs: &[&Bool]) -> Bool {
    match xs.len() {
        0 => tt(),
        1 => xs[0].clone(),
        _ => Bool::and(&xs.iter().map(|b| (*b).clone()).collect::<Vec<_>>()),
    }
}
pub fn or(xs: &[&Bool]) -> Bool {
    match xs.len() {
        0 => ff(),
        1 => xs[0].clone(),
        _ => Bool::or(&xs.iter().map(|b| (*b).clone()).collect::<Vec<_>>()),
    }
}

impl SV {
    pub fn ok(v: Sym) -> SV {
        SV { v, err: ff() }
    }
}

impl Sym {
    /// Every integer-sorted leaf (ints, uints, dates, timestamps, durations), for sampling.
    pub fn int_leaves(&self, out: &mut Vec<Int>) {
        match self {
            Sym::Int(i) | Sym::Uint(i) | Sym::Date(i) | Sym::Timestamp(i) | Sym::Duration(i) => out.push(i.clone()),
            Sym::Nullable { inner, .. } => inner.int_leaves(out),
            Sym::Optional { val, .. } => val.int_leaves(out),
            Sym::List { slots, .. } => slots.iter().for_each(|(_, s)| s.int_leaves(out)),
            Sym::Map { slots, .. } => slots.iter().for_each(|(_, k, v)| {
                k.int_leaves(out);
                v.int_leaves(out)
            }),
            Sym::Struct { fields, .. } => fields.values().for_each(|s| s.int_leaves(out)),
            _ => {}
        }
    }

    /// Every string inside the value (through containers, structs and optionals).
    pub fn str_leaves(&self, out: &mut Vec<ZStr>) {
        match self {
            Sym::Str(x) => out.push(x.clone()),
            Sym::Nullable { inner, .. } => inner.str_leaves(out),
            Sym::Optional { val, .. } => val.str_leaves(out),
            Sym::List { slots, .. } => slots.iter().for_each(|(_, s)| s.str_leaves(out)),
            Sym::Map { slots, .. } => slots.iter().for_each(|(_, k, v)| {
                k.str_leaves(out);
                v.str_leaves(out)
            }),
            Sym::Struct { fields, .. } => fields.values().for_each(|s| s.str_leaves(out)),
            _ => {}
        }
    }

    pub fn as_bool(&self) -> Option<&Bool> {
        match self {
            Sym::Bool(b) => Some(b),
            _ => None,
        }
    }
    pub fn as_int(&self) -> Option<&Int> {
        match self {
            Sym::Int(i) | Sym::Uint(i) | Sym::Date(i) => Some(i),
            _ => None,
        }
    }

    /// Number of live elements of a list.
    pub fn list_len(slots: &[(Bool, Sym)]) -> Int {
        let one = Int::from_i64(1);
        let zero = Int::from_i64(0);
        let terms: Vec<Int> = slots.iter().map(|(l, _)| l.ite(&one, &zero)).collect();
        if terms.is_empty() {
            zero
        } else {
            Int::add(&terms)
        }
    }

    pub fn map_len(slots: &[(Bool, Sym, Sym)]) -> Int {
        let one = Int::from_i64(1);
        let zero = Int::from_i64(0);
        let terms: Vec<Int> = slots.iter().map(|(l, _, _)| l.ite(&one, &zero)).collect();
        if terms.is_empty() {
            zero
        } else {
            Int::add(&terms)
        }
    }

    /// Strip Nullable: returns (is_null, inner).
    pub fn unwrap_nullable(&self) -> (Bool, &Sym) {
        match self {
            Sym::Nullable { is_null, inner } => (is_null.clone(), inner),
            Sym::Null => (tt(), self),
            s => (ff(), s),
        }
    }
}

/// Structural equality. Returns None if the shapes are incomparable (caller treats as unsupported).
pub fn sym_eq(a: &Sym, b: &Sym) -> Option<Bool> {
    use Sym::*;
    Some(match (a, b) {
        (Bool(x), Bool(y)) => x.eq(y),
        (Int(x), Int(y))
        | (Uint(x), Uint(y))
        | (Int(x), Uint(y))
        | (Uint(x), Int(y))
        | (Date(x), Date(y))
        | (Timestamp(x), Timestamp(y))
        | (Duration(x), Duration(y)) => x.eq(y),
        (Str(x), Str(y)) => x.eq(y),
        // IEEE equality: NaN != NaN and -0.0 == 0.0; ints compare after conversion (the spec's lossy rule)
        (Double(x), Double(y)) => x.eq_fpa(y),
        (Double(x), Int(y) | Uint(y)) | (Int(y) | Uint(y), Double(x)) => x.eq_fpa(crate::zutil::int_to_double(y)),
        (Null, Null) => tt(),
        (Nullable { is_null, .. }, Null) | (Null, Nullable { is_null, .. }) => is_null.clone(),
        (Nullable { is_null: n1, inner: i1 }, Nullable { is_null: n2, inner: i2 }) => {
            let inner = sym_eq(i1, i2)?;
            or(&[&and(&[n1, n2]), &and(&[&n1.not(), &n2.not(), &inner])])
        }
        (Nullable { is_null, inner }, other) | (other, Nullable { is_null, inner }) => {
            let inner = sym_eq(inner, other)?;
            and(&[&is_null.not(), &inner])
        }
        (Null, _) | (_, Null) => ff(),
        (Struct { name: n1, fields: f1 }, Struct { name: n2, fields: f2 }) => {
            if n1 != n2 {
                return Some(ff());
            }
            let mut parts = Vec::new();
            for (k, v) in f1 {
                parts.push(sym_eq(v, f2.get(k)?)?);
            }
            and(&parts.iter().collect::<Vec<_>>())
        }
        (List { slots: s1, .. }, List { slots: s2, .. }) => list_eq(s1, s2)?,
        (Optional { has: h1, val: v1 }, Optional { has: h2, val: v2 }) => {
            let inner = sym_eq(v1, v2)?;
            or(&[&and(&[&h1.not(), &h2.not()]), &and(&[h1, h2, &inner])])
        }
        (Map { slots: s1, .. }, Map { slots: s2, .. }) => {
            // same size, and every live entry of one is an entry of the other
            let n1 = Sym::map_len(s1);
            let n2 = Sym::map_len(s2);
            let mut parts = vec![n1.eq(&n2)];
            for (live, k, v) in s1 {
                let mut hit = Vec::new();
                for (l2, k2, v2) in s2 {
                    hit.push(and(&[l2, &sym_eq(k, k2)?, &sym_eq(v, v2)?]));
                }
                parts.push(live.implies(or(&hit.iter().collect::<Vec<_>>())));
            }
            and(&parts.iter().collect::<Vec<_>>())
        }
        (Opaque { ty: t1, id: x }, Opaque { ty: t2, id: y }) if t1 == t2 => x.eq(y),
        _ => return None,
    })
}

/// Look up `k` in a map: (found, value). The value is meaningful only when found.
pub fn map_get(slots: &[(Bool, Sym, Sym)], k: &Sym) -> Option<(Bool, Option<Sym>)> {
    let mut found = ff();
    let mut result: Option<Sym> = None;
    for (live, key, val) in slots {
        let here = and(&[live, &sym_eq(key, k)?]);
        result = Some(match result {
            None => val.clone(),
            Some(r) => ite_sym(&here, val, &r)?,
        });
        found = or(&[&found, &here]);
    }
    Some((found, result))
}

/// Keys of live slots are pairwise distinct.
pub fn distinct_keys(slots: &[(Bool, Sym, Sym)]) -> Option<Bool> {
    let mut parts = Vec::new();
    for i in 0..slots.len() {
        for j in i + 1..slots.len() {
            let (li, ki, _) = &slots[i];
            let (lj, kj, _) = &slots[j];
            parts.push(and(&[li, lj]).implies(sym_eq(ki, kj)?.not()));
        }
    }
    Some(and(&parts.iter().collect::<Vec<_>>()))
}

/// The k-th live element of a list: (exists, element).
pub fn nth_live(slots: &[(Bool, Sym)], k: &Int) -> Option<(Bool, Sym)> {
    // prefix[j] = number of live slots before j
    let mut prefix = Int::from_i64(0);
    let one = Int::from_i64(1);
    let zero = Int::from_i64(0);
    let mut found = ff();
    let mut result: Option<Sym> = None;
    for (live, elem) in slots {
        let here = and(&[live, &prefix.eq(k)]);
        result = Some(match result {
            None => elem.clone(),
            Some(r) => ite_sym(&here, elem, &r)?,
        });
        found = or(&[&found, &here]);
        prefix = &prefix + live.ite(&one, &zero);
    }
    Some((found, result?))
}

fn list_eq(s1: &[(Bool, Sym)], s2: &[(Bool, Sym)]) -> Option<Bool> {
    let n1 = Sym::list_len(s1);
    let n2 = Sym::list_len(s2);
    let mut parts = vec![n1.eq(&n2)];
    let all_live = |s: &[(Bool, Sym)]| s.iter().all(|(l, _)| l.as_bool() == Some(true));
    if all_live(s1) && all_live(s2) {
        if s1.len() != s2.len() {
            return Some(ff());
        }
        for ((_, a), (_, b)) in s1.iter().zip(s2) {
            parts.push(sym_eq(a, b)?);
        }
        return Some(and(&parts.iter().collect::<Vec<_>>()));
    }
    let cap = s1.len().min(s2.len());
    for k in 0..cap {
        let ki = Int::from_i64(k as i64);
        let (_, a) = nth_live(s1, &ki)?;
        let (_, b) = nth_live(s2, &ki)?;
        parts.push(ki.lt(&n1).implies(&sym_eq(&a, &b)?));
    }
    Some(and(&parts.iter().collect::<Vec<_>>()))
}

/// If-then-else on symbolic values of the same static shape.
pub fn ite_sym(c: &Bool, a: &Sym, b: &Sym) -> Option<Sym> {
    use Sym::*;
    Some(match (a, b) {
        (Bool(x), Bool(y)) => Bool(c.ite(x, y)),
        (Int(x), Int(y)) => Int(c.ite(x, y)),
        (Uint(x), Uint(y)) => Uint(c.ite(x, y)),
        (Date(x), Date(y)) => Date(c.ite(x, y)),
        (Timestamp(x), Timestamp(y)) => Timestamp(c.ite(x, y)),
        (Duration(x), Duration(y)) => Duration(c.ite(x, y)),
        (Str(x), Str(y)) => Str(c.ite(x, y)),
        (Double(x), Double(y)) => Double(c.ite(x, y)),
        (Null, Null) => Null,
        (Opaque { ty, id: x }, Opaque { id: y, .. }) => Opaque { ty: ty.clone(), id: c.ite(x, y) },
        (Nullable { is_null: n1, inner: i1 }, Nullable { is_null: n2, inner: i2 }) => {
            Nullable { is_null: c.ite(n1, n2), inner: Box::new(ite_sym(c, i1, i2)?) }
        }
        (Nullable { is_null, inner }, Null) => Nullable { is_null: or(&[&c.not(), is_null]), inner: inner.clone() },
        (Null, Nullable { is_null, inner }) => Nullable { is_null: or(&[c, is_null]), inner: inner.clone() },
        (Nullable { is_null, inner }, other) => Nullable { is_null: and(&[c, is_null]), inner: Box::new(ite_sym(c, inner, other)?) },
        (other, Nullable { is_null, inner }) => Nullable { is_null: and(&[&c.not(), is_null]), inner: Box::new(ite_sym(c, other, inner)?) },
        (Null, other) => Nullable { is_null: c.clone(), inner: Box::new(other.clone()) },
        (other, Null) => Nullable { is_null: c.not(), inner: Box::new(other.clone()) },
        (Struct { name, fields: f1 }, Struct { fields: f2, .. }) => {
            let mut fields = BTreeMap::new();
            for (k, v) in f1 {
                fields.insert(k.clone(), ite_sym(c, v, f2.get(k)?)?);
            }
            Struct { name: name.clone(), fields }
        }
        (Optional { has: h1, val: v1 }, Optional { has: h2, val: v2 }) => {
            Optional { has: c.ite(h1, h2), val: Box::new(ite_sym(c, v1, v2)?) }
        }
        (Map { slots: s1, key, val, trunc: t1 }, Map { slots: s2, trunc: t2, .. }) => {
            // slot-wise merge keeps each branch's keys distinct
            let n = s1.len().max(s2.len());
            let mut slots = Vec::with_capacity(n);
            for i in 0..n {
                slots.push(match (s1.get(i), s2.get(i)) {
                    (Some((l1, k1, v1)), Some((l2, k2, v2))) => (c.ite(l1, l2), ite_sym(c, k1, k2)?, ite_sym(c, v1, v2)?),
                    (Some((l1, k1, v1)), None) => (and(&[c, l1]), k1.clone(), v1.clone()),
                    (None, Some((l2, k2, v2))) => (and(&[&c.not(), l2]), k2.clone(), v2.clone()),
                    (None, None) => unreachable!(),
                });
            }
            Map { slots, key: key.clone(), val: val.clone(), trunc: *t1 || *t2 }
        }
        (List { slots: s1, elem, trunc: t1 }, List { slots: s2, trunc: t2, .. }) => {
            // pad the shorter list with dead slots, then merge slot-wise
            let n = s1.len().max(s2.len());
            let mut slots = Vec::with_capacity(n);
            for i in 0..n {
                let slot = match (s1.get(i), s2.get(i)) {
                    (Some((l1, e1)), Some((l2, e2))) => (c.ite(l1, l2), ite_sym(c, e1, e2)?),
                    (Some((l1, e1)), None) => (and(&[c, l1]), e1.clone()),
                    (None, Some((l2, e2))) => (and(&[&c.not(), l2]), e2.clone()),
                    (None, None) => unreachable!(),
                };
                slots.push(slot);
            }
            List { slots, elem: elem.clone(), trunc: *t1 || *t2 }
        }
        _ => return None,
    })
}

pub fn ite_sv(c: &Bool, a: &SV, b: &SV) -> Option<SV> {
    Some(SV { v: ite_sym(c, &a.v, &b.v)?, err: c.ite(&a.err, &b.err) })
}
