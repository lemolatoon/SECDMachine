use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::Display,
    ops::{Deref, DerefMut},
    rc::{Rc, Weak},
    str::FromStr,
    sync::atomic::AtomicUsize,
};

use anyhow::Context as _;

use crate::parse;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LambdaExpression {
    Var(String),
    Lambda(String, Box<LambdaExpression>),
    Apply(Box<LambdaExpression>, Box<LambdaExpression>),
}

impl FromStr for LambdaExpression {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        LambdaExpression::parse(s)
    }
}

impl LambdaExpression {
    pub fn parse(input: &str) -> anyhow::Result<Self> {
        parse::parse(input)
    }

    /// return `self` `arg`
    pub fn apply(self, arg: LambdaExpression) -> LambdaExpression {
        LambdaExpression::Apply(Box::new(self), Box::new(arg))
    }

    /// return \`x`. `e`
    pub fn lambda(x: impl Into<String>, e: LambdaExpression) -> LambdaExpression {
        LambdaExpression::Lambda(x.into(), Box::new(e))
    }

    /// return `x`
    pub fn var(x: impl Into<String>) -> LambdaExpression {
        LambdaExpression::Var(x.into())
    }

    pub fn alpha_rename(&mut self, old: &str, new: &str) {
        match self {
            LambdaExpression::Var(v) if v == old => *self = LambdaExpression::Var(new.to_string()),
            LambdaExpression::Var(_) => {}
            LambdaExpression::Lambda(param, body) => {
                if param == old {
                    // Bound variable matches old; don't rename inside
                    *self = LambdaExpression::Lambda(param.clone(), body.clone())
                } else {
                    // Rename occurrences of old in the body
                    body.alpha_rename(old, new);
                }
            }
            LambdaExpression::Apply(f, x) => {
                f.alpha_rename(old, new);
                x.alpha_rename(old, new);
            }
        }
    }

    pub fn alpha_equiv(&self, other: &LambdaExpression) -> bool {
        AnalyzedLambdaExpression::alpha_equiv(
            &self.clone().into_analyzed(),
            &other.clone().into_analyzed(),
        )
    }

    pub fn into_analyzed(self) -> Rc<RefCell<AnalyzedLambdaExpression>> {
        fn convert(
            expr: &LambdaExpression,
            env: &mut Vec<Rc<RefCell<AnalyzedLambdaExpression>>>,
        ) -> Rc<RefCell<AnalyzedLambdaExpression>> {
            match expr {
                // Look up any matching lambda parameter in env to see if it's bound.
                LambdaExpression::Var(name) => {
                    for parent in env.iter().rev() {
                        if let AnalyzedLambdaExpression::Lambda(l) = parent.borrow().deref() {
                            if l.param_name() == name {
                                let var =
                                    AnalyzedVar::new_bounded(name.clone(), Rc::downgrade(parent));
                                return Rc::new(RefCell::new(AnalyzedLambdaExpression::Var(var)));
                            }
                        }
                    }
                    Rc::new(RefCell::new(AnalyzedLambdaExpression::Var(
                        AnalyzedVar::new(name.clone()),
                    )))
                }
                // Create a new AnalyzedLambda, push it in env, recurse on body, then pop.
                LambdaExpression::Lambda(param, body) => {
                    static PLACEHOLDER_INDEX: AtomicUsize = AtomicUsize::new(0);
                    let placeholder_name = format!(
                        "<placeholder-{}>",
                        PLACEHOLDER_INDEX.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                    );
                    let placeholder = Rc::new(RefCell::new(AnalyzedLambdaExpression::Lambda(
                        AnalyzedLambda::new(
                            param.clone(),
                            Rc::new(RefCell::new(AnalyzedLambdaExpression::Var(
                                AnalyzedVar::new(placeholder_name),
                            ))),
                        ),
                    )));
                    env.push(Rc::clone(&placeholder));
                    let analyzed_body = convert(body, env);
                    env.pop();

                    // Rebuild the lambda with a param referencing itself and gather bounds.
                    let mut lambda = AnalyzedLambda::new(param.clone(), Rc::clone(&analyzed_body));
                    lambda.bounds = collect_bounds(param, analyzed_body);
                    {
                        let mut placeholder_mut = placeholder.borrow_mut();
                        // Update placeholder’s body to the final analyzed body
                        let AnalyzedLambdaExpression::Lambda(ref mut placeholder_mut) =
                            placeholder_mut.deref_mut()
                        else {
                            panic!("placeholder is not a lambda");
                        };
                        *placeholder_mut = lambda;
                    }
                    let lambda = Rc::clone(&placeholder);

                    lambda
                }
                // Recursively analyze sub-expressions.
                LambdaExpression::Apply(fun, arg) => {
                    let analyzed_fun = convert(fun, env);
                    let analyzed_arg = convert(arg, env);
                    Rc::new(RefCell::new(AnalyzedLambdaExpression::Apply(
                        AnalyzedApply::new(analyzed_fun, analyzed_arg),
                    )))
                }
            }
        }

        // Gather references to param in body.
        fn collect_bounds(
            param: &str,
            body: Rc<RefCell<AnalyzedLambdaExpression>>,
        ) -> Vec<Rc<RefCell<AnalyzedLambdaExpression>>> {
            let mut refs = Vec::new();
            fn walk(
                expr: &Rc<RefCell<AnalyzedLambdaExpression>>,
                param: &str,
                out: &mut Vec<Rc<RefCell<AnalyzedLambdaExpression>>>,
            ) {
                match &*expr.borrow() {
                    AnalyzedLambdaExpression::Var(v) => {
                        if v.name() == param {
                            out.push(Rc::clone(expr));
                        }
                    }
                    AnalyzedLambdaExpression::Lambda(l) => {
                        // Skip if param shadows another variable
                        // e.g. (λx.(λx.x)) should not capture the inner x
                        if l.param_name() != param {
                            walk(l.body(), param, out);
                        }
                    }
                    AnalyzedLambdaExpression::Apply(a) => {
                        walk(a.fun(), param, out);
                        walk(a.arg(), param, out);
                    }
                }
            }
            walk(&body, param, &mut refs);
            refs
        }

        convert(&self, &mut Vec::new())
    }
}

impl Display for LambdaExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LambdaExpression::Var(x) => write!(f, "{}", x),
            LambdaExpression::Lambda(x, e) => write!(f, "(λ{}.{})", x, e),
            LambdaExpression::Apply(fun, x) => write!(f, "({} {})", fun, x),
        }
    }
}

#[derive(Clone, Debug)]
pub struct AnalyzedVar {
    name: String,
    bounded_by: Option<Weak<RefCell<AnalyzedLambdaExpression>>>,
}

impl AnalyzedVar {
    pub fn new(name: String) -> Self {
        Self {
            name,
            bounded_by: None,
        }
    }

    pub fn new_bounded(name: String, bounded_by: Weak<RefCell<AnalyzedLambdaExpression>>) -> Self {
        Self {
            name,
            bounded_by: Some(bounded_by),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    fn set_name(&mut self, name: String) {
        self.name = name;
    }

    pub fn bounded_by(&self) -> anyhow::Result<Option<Rc<RefCell<AnalyzedLambdaExpression>>>> {
        self.bounded_by
            .as_ref()
            .map(|weak| weak.upgrade().context("Bounded by has been dropped"))
            .transpose()
    }

    pub fn is_bounded(&self) -> bool {
        self.bounded_by.is_some()
    }

    pub fn is_free(&self) -> bool {
        self.bounded_by.is_none()
    }
}

impl Display for AnalyzedVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Clone, Debug)]
pub struct AnalyzedLambda {
    param_name: String,
    body: Rc<RefCell<AnalyzedLambdaExpression>>,
    bounds: Vec<Rc<RefCell<AnalyzedLambdaExpression>>>,
}

impl AnalyzedLambda {
    pub fn new(param_name: String, body: Rc<RefCell<AnalyzedLambdaExpression>>) -> Self {
        Self::new_with_bounds(param_name, body, Vec::new())
    }

    pub fn new_with_bounds(
        param_name: String,
        body: Rc<RefCell<AnalyzedLambdaExpression>>,
        bounds: Vec<Rc<RefCell<AnalyzedLambdaExpression>>>,
    ) -> Self {
        Self {
            param_name,
            body,
            bounds,
        }
    }

    pub fn param_name(&self) -> &str {
        &self.param_name
    }

    fn set_param_name(&mut self, param_name: String) {
        self.param_name = param_name;
    }

    pub fn body(&self) -> &Rc<RefCell<AnalyzedLambdaExpression>> {
        &self.body
    }

    pub fn bounds(&self) -> &[Rc<RefCell<AnalyzedLambdaExpression>>] {
        &self.bounds
    }

    /// alpha_rename_param replaces all occurrences of `old` with `new` in this lambda's body,
    /// and sets this lambda's param name to `new`.
    pub fn alpha_rename_param(&mut self, old: &str, new: &str) {
        if self.param_name == old {
            self.param_name = new.to_string();
            for bound in self.bounds.iter() {
                let mut bound_mut = bound.borrow_mut();
                let AnalyzedLambdaExpression::Var(ref mut v) = bound_mut.deref_mut() else {
                    panic!("Expected a Var in bounds");
                };
                assert_eq!(v.name(), old);
                v.set_name(new.to_string());
            }
        }
        // Now rename in the body
        // self.body.borrow_mut().alpha_rename_var(old, new);
    }
}

impl Display for AnalyzedLambda {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(λ{}.{})", self.param_name, self.body.borrow())
    }
}

#[derive(Clone, Debug)]
pub struct AnalyzedApply {
    fun: Rc<RefCell<AnalyzedLambdaExpression>>,
    arg: Rc<RefCell<AnalyzedLambdaExpression>>,
}

impl AnalyzedApply {
    pub fn new(
        fun: Rc<RefCell<AnalyzedLambdaExpression>>,
        arg: Rc<RefCell<AnalyzedLambdaExpression>>,
    ) -> Self {
        Self { fun, arg }
    }

    pub fn fun(&self) -> &Rc<RefCell<AnalyzedLambdaExpression>> {
        &self.fun
    }

    pub fn arg(&self) -> &Rc<RefCell<AnalyzedLambdaExpression>> {
        &self.arg
    }
}

impl Display for AnalyzedApply {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} {})",
            self.fun.borrow().deref(),
            self.arg.borrow().deref()
        )
    }
}

#[derive(Clone, Debug)]
pub enum AnalyzedLambdaExpression {
    Var(AnalyzedVar),
    Lambda(AnalyzedLambda),
    Apply(AnalyzedApply),
}

impl Display for AnalyzedLambdaExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AnalyzedLambdaExpression::Var(v) => write!(f, "{}", v),
            AnalyzedLambdaExpression::Lambda(l) => write!(f, "{}", l),
            AnalyzedLambdaExpression::Apply(a) => write!(f, "{}", a),
        }
    }
}

impl From<AnalyzedLambdaExpression> for LambdaExpression {
    fn from(analyzed: AnalyzedLambdaExpression) -> Self {
        match analyzed {
            AnalyzedLambdaExpression::Var(v) => LambdaExpression::Var(v.name),
            AnalyzedLambdaExpression::Lambda(l) => LambdaExpression::Lambda(
                l.param_name,
                Box::new(LambdaExpression::from(l.body.borrow().clone())),
            ),
            AnalyzedLambdaExpression::Apply(a) => LambdaExpression::Apply(
                Box::new(LambdaExpression::from(a.fun.borrow().clone())),
                Box::new(LambdaExpression::from(a.arg.borrow().clone())),
            ),
        }
    }
}

impl AnalyzedLambdaExpression {
    pub fn alpha_substitute(&mut self, x: &str, val: &Rc<RefCell<AnalyzedLambdaExpression>>) {
        let mut new_name = None;
        if let AnalyzedLambdaExpression::Lambda(l) = &*self {
            let old_name = l.param_name();
            new_name = Some(self.make_fresh_name(old_name, &val.borrow()));
        }
        match self {
            AnalyzedLambdaExpression::Var(v) => {
                // If this var is free and matches x, replace with val (cloning if needed)
                if !v.is_bounded() && v.name() == x {
                    *self = val.borrow().clone();
                }
            }
            AnalyzedLambdaExpression::Lambda(l) => {
                // If the parameter name is exactly x, do not substitute inside the lambda
                if l.param_name() == x {
                    return;
                }

                // if 'param_name' appears as a free var in val,
                // rename it in the lambda to avoid capture.
                if !val.borrow().is_fresh_name(l.param_name()) {
                    let old_name = l.param_name().to_string();
                    // Generate a new name that does not appear free in self or in val
                    let new_name = new_name.unwrap();

                    // Perform the rename on this lambda’s body
                    // e.g. alpha_rename_param mutates l’s param name and body references
                    l.alpha_rename_param(&old_name, &new_name);
                }

                // Continue substituting inside the body
                l.body().borrow_mut().alpha_substitute(x, val);
            }
            AnalyzedLambdaExpression::Apply(a) => {
                a.fun().borrow_mut().alpha_substitute(x, val);
                a.arg().borrow_mut().alpha_substitute(x, val);
            }
        }
    }

    /// Returns true if `candidate` does NOT appear as a free variable in self.
    pub fn is_fresh_name(&self, candidate: &str) -> bool {
        match self {
            AnalyzedLambdaExpression::Var(v) => {
                // If it's free, check name
                if !v.is_bounded() {
                    v.name() != candidate
                } else {
                    // It's a bound var => no capture conflict as a free var
                    true
                }
            }
            AnalyzedLambdaExpression::Lambda(l) => {
                // If the lambda's parameter is the same as candidate, we skip checking inside
                // because candidate is bound within this scope. Otherwise, recurse
                if l.param_name() == candidate {
                    true
                } else {
                    l.body().borrow().is_fresh_name(candidate)
                }
            }
            AnalyzedLambdaExpression::Apply(a) => {
                a.fun().borrow().is_fresh_name(candidate)
                    && a.arg().borrow().is_fresh_name(candidate)
            }
        }
    }

    /// Creates a new parameter name not free in either `self` or `other`.
    /// For example, we can keep appending apostrophes (') or an incrementing index.
    fn make_fresh_name(&self, base: &str, other: &AnalyzedLambdaExpression) -> String {
        let mut candidate = base.to_string() + "'";
        // Keep adjusting candidate if it appears free in either expression
        while !self.is_fresh_name(&candidate) || !other.is_fresh_name(&candidate) {
            candidate.push('\'');
        }
        candidate
    }

    /// A helper that renames only those Var(...) occurrences that match `old` and are bound by this lambda.
    /// Recursively rename every matching bound var from `old` to `new`.
    pub fn alpha_rename_var(&mut self, old: &str, new: &str) {
        match self {
            AnalyzedLambdaExpression::Var(_v) => {
                return;
            }
            AnalyzedLambdaExpression::Lambda(l) => {
                // If the lambda param matches `old`, rename it here
                // (Though we typically do param renaming via alpha_rename_param above)
                if l.param_name() == old {
                    l.set_param_name(new.to_string());
                    for bound in l.bounds() {
                        let mut bound_mut = bound.borrow_mut();
                        let AnalyzedLambdaExpression::Var(ref mut v) = bound_mut.deref_mut() else {
                            panic!("Expected a Var in bounds");
                        };
                        assert_eq!(v.name(), old);
                        v.set_name(new.to_string());
                    }
                } else {
                    // Otherwise, rename inside
                    l.body().borrow_mut().alpha_rename_var(old, new);
                }
            }
            AnalyzedLambdaExpression::Apply(a) => {
                a.fun().borrow_mut().alpha_rename_var(old, new);
                a.arg().borrow_mut().alpha_rename_var(old, new);
            }
        }
    }

    /// Checks if two analyzed lambda expressions are alpha-equivalent.
    /// This relies on the pointer structure for bounded variables (if they reference the
    /// same lambda) and ignores parameter names for lambdas.
    pub fn alpha_equiv(
        a: &Rc<RefCell<AnalyzedLambdaExpression>>,
        b: &Rc<RefCell<AnalyzedLambdaExpression>>,
    ) -> bool {
        let mut visited = HashSet::new();
        alpha_equiv_inner(a, b, &mut visited)
    }
}

/// Internal helper that tracks visited pairs of pointers to avoid infinite recursion.
fn alpha_equiv_inner(
    a: &Rc<RefCell<AnalyzedLambdaExpression>>,
    b: &Rc<RefCell<AnalyzedLambdaExpression>>,
    visited: &mut HashSet<(usize, usize)>,
) -> bool {
    let pa = Rc::as_ptr(a) as usize;
    let pb = Rc::as_ptr(b) as usize;
    // Same pointer => trivially alpha-equivalent
    if pa == pb {
        return true;
    }
    // If we've already seen this pair, assume no mismatch was found before
    if !visited.insert((pa, pb)) {
        return true;
    }

    let a_borrow = a.borrow();
    let b_borrow = b.borrow();
    match (a_borrow.deref(), b_borrow.deref()) {
        (AnalyzedLambdaExpression::Var(v1), AnalyzedLambdaExpression::Var(v2)) => {
            match (v1.is_bounded(), v2.is_bounded()) {
                (false, false) => v1.name() == v2.name(), // both free => compare names
                (true, true) => {
                    // both bounded => check if they reference alpha-equivalent lambdas
                    let (rc_a, rc_b) = (
                        v1.bounded_by().unwrap().expect("should not be freed"),
                        v2.bounded_by().unwrap().expect("should not be freed"),
                    );
                    alpha_equiv_inner(&rc_a, &rc_b, visited)
                }
                _ => false,
            }
        }
        (AnalyzedLambdaExpression::Lambda(l1), AnalyzedLambdaExpression::Lambda(l2)) => {
            // Ignore the param_name; just compare bodies
            alpha_equiv_inner(l1.body(), l2.body(), visited)
        }
        (AnalyzedLambdaExpression::Apply(a1), AnalyzedLambdaExpression::Apply(a2)) => {
            // Compare fun and arg
            alpha_equiv_inner(a1.fun(), a2.fun(), visited)
                && alpha_equiv_inner(a1.arg(), a2.arg(), visited)
        }
        _ => false,
    }
}

#[cfg(test)]
mod alpha_equiv_tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::AnalyzedLambdaExpression;
    fn alpha_equiv(
        a: &Rc<RefCell<AnalyzedLambdaExpression>>,
        b: &Rc<RefCell<AnalyzedLambdaExpression>>,
    ) -> bool {
        AnalyzedLambdaExpression::alpha_equiv(a, b)
    }
    use super::LambdaExpression;

    // 1) Free variables (same name) => alpha-equivalent
    #[test]
    fn test_alpha_var_free_same_name() {
        let e1 = "x".parse::<LambdaExpression>().unwrap().into_analyzed();
        let e2 = "x".parse::<LambdaExpression>().unwrap().into_analyzed();
        assert!(alpha_equiv(&e1, &e2));
    }

    // 2) Free variables (different name) => not alpha-equivalent
    #[test]
    fn test_alpha_var_free_different_name() {
        let e1 = "x".parse::<LambdaExpression>().unwrap().into_analyzed();
        let e2 = "y".parse::<LambdaExpression>().unwrap().into_analyzed();
        assert!(!alpha_equiv(&e1, &e2));
    }

    // 3) Simple lambdas with different parameter names => alpha-equivalent
    #[test]
    fn test_alpha_lambda_simple() {
        let e1 = "λx.x".parse::<LambdaExpression>().unwrap().into_analyzed();
        let e2 = "λy.y".parse::<LambdaExpression>().unwrap().into_analyzed();
        assert!(alpha_equiv(&e1, &e2));
    }

    // 4) Nested lambdas with different parameter names => alpha-equivalent
    //    λx.λy.y vs λp.λq.q
    #[test]
    fn test_alpha_lambda_nested() {
        let e1 = "λx.λy.y"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        let e2 = "λp.λq.q"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        assert!(alpha_equiv(&e1, &e2));
    }

    // 5) Simple application of free variables => alpha-equivalent if same names
    //    (x y) vs (x y)
    #[test]
    fn test_alpha_apply_free_vars() {
        let e1 = "(x y)".parse::<LambdaExpression>().unwrap().into_analyzed();
        let e2 = "(x y)".parse::<LambdaExpression>().unwrap().into_analyzed();
        assert!(alpha_equiv(&e1, &e2));
    }

    // 6) Applying two identical lambdas => alpha-equivalent
    //    ((λx.x) (λy.y)) vs ((λu.u) (λv.v))
    #[test]
    fn test_alpha_apply_identical_lambdas() {
        let e1 = "((λx.x) (λy.y))"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        let e2 = "((λu.u) (λv.v))"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        assert!(alpha_equiv(&e1, &e2));
    }

    // 7) Shadowed variable inside: λx.(λx.x)
    //    vs λp.(λq.q). Should be alpha-equivalent
    #[test]
    fn test_alpha_shadowing() {
        let e1 = "λx.(λx.x)"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        let e2 = "λp.(λq.q)"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        assert!(alpha_equiv(&e1, &e2));
    }

    // 8) Free variable vs. a lambda — not alpha-equivalent
    //    x vs λy.y
    #[test]
    fn test_alpha_free_vs_lambda() {
        let e1 = "x".parse::<LambdaExpression>().unwrap().into_analyzed();
        let e2 = "λy.y".parse::<LambdaExpression>().unwrap().into_analyzed();
        assert!(!alpha_equiv(&e1, &e2));
    }

    // 9) λx.(y x) vs λu.(y u) => alpha-equivalent if 'y' is free
    #[test]
    fn test_alpha_mixed_free_bound() {
        let e1 = "λx.(y x)"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        let e2 = "λu.(y u)"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        assert!(alpha_equiv(&e1, &e2));
    }

    // 10) λx.(x y) vs λx.(y x) => not alpha-equivalent (the free var 'y' is in different positions)
    #[test]
    fn test_alpha_different_structure() {
        let e1 = "λx.(x y)"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        let e2 = "λx.(y x)"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        assert!(!alpha_equiv(&e1, &e2));
    }
}

#[cfg(test)]
mod tests {
    use std::{ops::Deref as _, rc::Rc};

    use super::{AnalyzedLambdaExpression, LambdaExpression};

    macro_rules! assert_eq_ptr {
        ($left:expr, $right:expr) => {
            assert!(
                Rc::ptr_eq(&$left, &$right),
                "Rc::ptr_eq: left={}, right={}",
                $left.borrow().deref(),
                $right.borrow().deref()
            );
        };
        () => {};
    }

    #[test]
    fn test_var_free() {
        let expr = LambdaExpression::Var("x".to_string());
        let analyzed = expr.clone().into_analyzed();
        let analyzed = analyzed.borrow();
        match analyzed.deref() {
            AnalyzedLambdaExpression::Var(v) => {
                assert_eq!(v.name(), "x");
                assert!(v.is_free());
            }
            _ => panic!("Expected a free variable"),
        }
    }

    #[test]
    fn test_var_bound() {
        // (λx.x) => the 'x' is bound inside
        let expr = LambdaExpression::Lambda(
            "x".to_string(),
            Box::new(LambdaExpression::Var("x".to_string())),
        );
        let analyzed = expr.clone().into_analyzed();
        let analyzed_borrow = analyzed.borrow();
        match analyzed_borrow.deref() {
            AnalyzedLambdaExpression::Lambda(l) => {
                // The body should be a Var that is ptr_eq-bounded by l
                let body = l.body().borrow();
                match body.deref() {
                    AnalyzedLambdaExpression::Var(ref v) => {
                        assert_eq!(v.name(), "x");
                        assert!(v.is_bounded());
                        // Check the param name
                        assert_eq!(l.param_name(), "x");
                        let bounded_by = v.bounded_by().unwrap().expect("bounded by");
                        assert_eq_ptr!(bounded_by, analyzed);
                    }
                    _ => panic!("Expected a variable inside the lambda body"),
                }
            }
            _ => panic!("Expected a lambda"),
        }
    }

    #[test]
    fn test_lambda_simple() {
        // λx.x
        let expr = "λx.x".parse::<LambdaExpression>().unwrap();
        let analyzed = expr.into_analyzed();
        let analyzed_borrow = analyzed.borrow();
        match analyzed_borrow.deref() {
            AnalyzedLambdaExpression::Lambda(l) => {
                assert_eq!(l.param_name(), "x");
                let body = l.body().borrow();
                match body.deref() {
                    AnalyzedLambdaExpression::Var(v) => {
                        assert_eq!(v.name(), "x");
                        assert!(v.is_bounded());
                        assert_eq_ptr!(v.bounded_by().unwrap().expect("bounded by"), analyzed);
                    }
                    _ => panic!("Expected var inside lambda"),
                }
            }
            _ => panic!("Expected a lambda"),
        }
    }

    #[test]
    fn test_lambda_nested() {
        // λx.λy.y
        let expr = "λx.λy.y".parse::<LambdaExpression>().unwrap();
        let analyzed = expr.clone().into_analyzed();
        let analyzed_borrow = analyzed.borrow();
        let AnalyzedLambdaExpression::Lambda(l1) = analyzed_borrow.deref() else {
            panic!("Expected a lambda");
        };
        assert_eq!(l1.param_name(), "x");
        let body1 = l1.body().borrow();
        let AnalyzedLambdaExpression::Lambda(l2) = body1.deref() else {
            panic!("Expected a lambda in body");
        };
        assert_eq!(l2.param_name(), "y");
        let body2 = l2.body().borrow();
        let AnalyzedLambdaExpression::Var(v) = body2.deref() else {
            panic!("Expected a var in body");
        };
        assert_eq!(v.name(), "y");
        assert!(v.is_bounded());
        assert_eq_ptr!(&v.bounded_by().unwrap().expect("bounded by"), l1.body());
    }

    #[test]
    fn test_apply_simple() {
        // (x y)
        let expr = LambdaExpression::Apply(
            Box::new(LambdaExpression::Var("x".to_string())),
            Box::new(LambdaExpression::Var("y".to_string())),
        );
        let analyzed = expr.into_analyzed();
        let analyzed_borrow = analyzed.borrow();
        let AnalyzedLambdaExpression::Apply(app) = analyzed_borrow.deref() else {
            panic!("Expected an apply node");
        };
        let fun_borrow = app.fun().borrow();
        let AnalyzedLambdaExpression::Var(v1) = fun_borrow.deref() else {
            panic!("Expected Var for fun");
        };
        assert_eq!(v1.name(), "x");

        let arg_borrow = app.arg().borrow();
        let AnalyzedLambdaExpression::Var(v2) = arg_borrow.deref() else {
            panic!("Expected Var for arg");
        };
        assert_eq!(v2.name(), "y");
    }

    #[test]
    fn test_apply_lambda_var() {
        // (λx.x) y
        let expr = "((λx.x) y)".parse::<LambdaExpression>().unwrap();
        let analyzed = expr.into_analyzed();
        let analyzed_borrow = analyzed.borrow();
        let AnalyzedLambdaExpression::Apply(app) = analyzed_borrow.deref() else {
            panic!("Expected an apply node");
        };

        let fun_borrow = app.fun().borrow();
        let AnalyzedLambdaExpression::Lambda(l) = fun_borrow.deref() else {
            panic!("Expected a lambda for fun");
        };
        assert_eq!(l.param_name(), "x");
        let body_borrow = l.body().borrow();
        let AnalyzedLambdaExpression::Var(v) = body_borrow.deref() else {
            panic!("Expected a var in body");
        };
        assert_eq!(v.name(), "x");
        assert!(v.is_bounded());
        assert_eq_ptr!(v.bounded_by().unwrap().expect("bounded by"), app.fun());

        let arg_borrow = app.arg().borrow();
        let AnalyzedLambdaExpression::Var(v) = arg_borrow.deref() else {
            panic!("Expected a var for arg");
        };
        assert_eq!(v.name(), "y");
        assert!(v.is_free());
    }

    #[test]
    fn test_shadowing() {
        // λx.(λx.x)
        let expr = "λx.(λx.x)".parse::<LambdaExpression>().unwrap();
        let analyzed = expr.clone().into_analyzed();
        let analyzed_borrow = analyzed.borrow();
        let AnalyzedLambdaExpression::Lambda(outer) = analyzed_borrow.deref() else {
            panic!("Expected a lambda (outer)");
        };
        assert_eq!(outer.param_name(), "x");

        let inner_rc = outer.body();
        let inner_body_borrow = inner_rc.borrow();
        let AnalyzedLambdaExpression::Lambda(inner) = inner_body_borrow.deref() else {
            panic!("Expected a nested lambda (inner)");
        };
        assert_eq!(inner.param_name(), "x");

        let inner_body_borrow = inner.body().borrow();
        let AnalyzedLambdaExpression::Var(v) = inner_body_borrow.deref() else {
            panic!("Expected a var in inner body");
        };
        // This var is bound by the inner, not the outer
        assert!(v.is_bounded());
        assert_eq_ptr!(v.bounded_by().unwrap().expect("bounded by"), inner_rc);
    }

    #[test]
    fn test_var_bound_by_outer_lambda() {
        // (λx.(x x)) – here both x's are bound by the outer lambda
        let analyzed = "λx.(x x)"
            .parse::<LambdaExpression>()
            .unwrap()
            .into_analyzed();
        let analyzed_borrow = analyzed.borrow();
        let AnalyzedLambdaExpression::Lambda(l) = analyzed_borrow.deref() else {
            panic!("Expected a lambda");
        };
        assert_eq!(l.param_name(), "x");

        let body_borrow = l.body().borrow();
        let AnalyzedLambdaExpression::Apply(a) = body_borrow.deref() else {
            panic!("Expected an Apply in the lambda body");
        };

        let fun_borrow = a.fun().borrow();
        let arg_borrow = a.arg().borrow();
        match (fun_borrow.deref(), arg_borrow.deref()) {
            (AnalyzedLambdaExpression::Var(v1), AnalyzedLambdaExpression::Var(v2)) => {
                assert_eq!(v1.name(), "x");
                assert_eq!(v2.name(), "x");
                assert!(
                    v1.is_bounded() && v2.is_bounded(),
                    "Both x's should be bound"
                );
                assert_eq_ptr!(v1.bounded_by().unwrap().expect("bounded by"), analyzed);
                assert_eq_ptr!(v2.bounded_by().unwrap().expect("bounded by"), analyzed);
            }
            _ => panic!("Expected Var(x) and Var(x) in the apply"),
        }
    }
}
