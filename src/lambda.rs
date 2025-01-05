use std::{
    cell::RefCell,
    collections::HashMap,
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

    /// Substitute `val` for `x` in `self`
    /// Returns a map of variable names that were renamed to avoid capture
    pub fn substitute(
        &mut self,
        x: String,
        val: LambdaExpression,
    ) -> anyhow::Result<HashMap<String, String>> {
        println!("substitute: {} with {} in {}", x, val, self);
        let mut renamed = HashMap::new();
        self.substitute_inner(x, val, &mut renamed)?;
        // normalize rename map
        let mut renamed_normalized = HashMap::new();
        for key in renamed.keys() {
            let mut val = renamed.get(key).unwrap().clone();
            while renamed.contains_key(&val) {
                val = renamed.get(&val).unwrap().clone();
            }
            renamed_normalized.insert(key, val);
        }
        Ok(renamed)
    }
    pub fn substitute_inner(
        &mut self,
        x: String,
        val: LambdaExpression,
        rename_map: &mut HashMap<String, String>,
    ) -> anyhow::Result<()> {
        match self {
            LambdaExpression::Var(v) if *v == x => {
                *self = val;
            }
            LambdaExpression::Var(v) => {}
            LambdaExpression::Lambda(x2, e) => {
                if *x2 == x {
                    // shadowed; don't substitute
                    return Ok(());
                }
                // If x2 appears free in val, rename x2 to avoid capture
                if !val.is_fresh_name(x2) {
                    let mut fresh_x2 = x2.clone();
                    while !val.is_fresh_name(&fresh_x2) || fresh_x2 == x {
                        fresh_x2.push('\'');
                    }
                    println!("Renaming {} to {} to avoid capture", x2, fresh_x2);
                    rename_map.insert(x2.clone(), fresh_x2.clone());
                    e.alpha_rename(x2, &fresh_x2);
                    *x2 = fresh_x2;
                }
                // Now substitute inside body
                e.substitute(x, val)?;
            }
            LambdaExpression::Apply(fun, arg) => {
                fun.substitute(x.clone(), val.clone())?;
                arg.substitute(x, val)?;
            }
        }

        Ok(())
    }

    pub fn is_fresh_name(&self, x: &str) -> bool {
        match self {
            LambdaExpression::Var(v) => v != x,
            LambdaExpression::Lambda(x2, e) => x2 != x && e.is_fresh_name(x),
            LambdaExpression::Apply(fun, arg) => fun.is_fresh_name(x) && arg.is_fresh_name(x),
        }
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

    pub fn body(&self) -> &Rc<RefCell<AnalyzedLambdaExpression>> {
        &self.body
    }

    pub fn bounds(&self) -> &[Rc<RefCell<AnalyzedLambdaExpression>>] {
        &self.bounds
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
