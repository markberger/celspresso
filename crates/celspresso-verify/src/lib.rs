#[cfg(test)]
mod tests {
    use z3::ast::Int;
    use z3::Solver;
    #[test]
    fn z3_smoke() {
        let s = Solver::new();
        let x = Int::new_const("x");
        s.assert((&x + 1).ge(5));
        assert_eq!(s.check(), z3::SatResult::Sat);
    }
}
