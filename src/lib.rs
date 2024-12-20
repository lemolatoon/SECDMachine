mod parse;

use std::{fmt::Display, str::FromStr};

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

    pub fn substitute(&mut self, x: String, val: EnvValue) -> anyhow::Result<()> {
        match self {
            LambdaExpression::Var(v) => {
                if *v == x {
                    *self = val.try_into()?;
                }
            }
            LambdaExpression::Lambda(x2, e) => {
                if *x2 == x {
                    anyhow::bail!(
                        "Cannot substitute: {} is tried to substitute with {}: {}",
                        LambdaExpression::Lambda(x2.clone(), e.clone()),
                        x,
                        val
                    );
                }
                e.substitute(x, val)?;
            }
            LambdaExpression::Apply(fun, arg) => {
                fun.substitute(x.clone(), val.clone())?;
                arg.substitute(x, val)?;
            }
        }

        Ok(())
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EnvValue {
    Expr(LambdaExpression),
    Clo(Closure),
}

impl TryFrom<EnvValue> for LambdaExpression {
    type Error = anyhow::Error;
    fn try_from(v: EnvValue) -> Result<Self, Self::Error> {
        match v {
            EnvValue::Expr(e) => Ok(e),
            EnvValue::Clo(c) => c.try_into(),
        }
    }
}

impl Display for EnvValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvValue::Expr(e) => write!(f, "{}", e),
            EnvValue::Clo(c) => write!(f, "{}", c),
        }
    }
}

impl From<StackValue> for EnvValue {
    fn from(v: StackValue) -> Self {
        match v {
            StackValue::Val(e) => EnvValue::Expr(e),
            StackValue::Clo(c) => EnvValue::Clo(c),
        }
    }
}

impl From<EnvValue> for StackValue {
    fn from(v: EnvValue) -> Self {
        match v {
            EnvValue::Expr(e) => StackValue::Val(e),
            EnvValue::Clo(c) => StackValue::Clo(c),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Env {
    var: String,
    val: EnvValue,
}

impl Display for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{}={}>", self.var, self.val)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Closure {
    bv: String,
    body: LambdaExpression,
    env: Vec<Env>,
}

impl Display for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<closure {},{},[", self.bv, self.body)?;
        for e in &self.env {
            write!(f, " {}", e)?;
        }
        write!(f, "]>")
    }
}

impl TryFrom<Closure> for LambdaExpression {
    type Error = anyhow::Error;
    fn try_from(c: Closure) -> Result<Self, Self::Error> {
        let mut initial = LambdaExpression::Lambda(c.bv, Box::new(c.body));
        // Consider env as a list of assignments
        for e in c.env.into_iter().rev() {
            initial.substitute(e.var, e.val)?;
        }

        Ok(initial)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Cont {
    Exp(LambdaExpression),
    AP,
}

impl Display for Cont {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Cont::Exp(e) => write!(f, "{}", e),
            Cont::AP => write!(f, "ap"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum StackValue {
    Val(LambdaExpression),
    Clo(Closure),
}

impl Display for StackValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StackValue::Val(v) => write!(f, "{}", v),
            StackValue::Clo(c) => write!(f, "{}", c),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Dump {
    stack: Vec<StackValue>,
    env: Vec<Env>,
    control: Vec<Cont>,
    dump: Box<DumpValue>,
}

fn format_vec<T: std::fmt::Display>(vec: &[T]) -> String {
    let contents = vec
        .iter()
        .map(|item| format!("{}", item))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{}]", contents)
}
impl Display for Dump {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "<s={}, e={}, c={}, d={}>",
            format_vec(&self.stack),
            format_vec(&self.env),
            format_vec(&self.control),
            self.dump
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DumpValue {
    Dump(Dump),
    Null,
}

impl Display for DumpValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DumpValue::Dump(d) => write!(f, "{}", d),
            DumpValue::Null => write!(f, "D0"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SECDMachine {
    stack: Vec<StackValue>,
    env: Vec<Env>,
    control: Vec<Cont>,
    dump: DumpValue,
}

impl Display for SECDMachine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "<s={:?}, e={:?}, c={:?}, d={}>",
            self.stack, self.env, self.control, self.dump
        )
    }
}

impl SECDMachine {
    pub fn new(exp: LambdaExpression) -> SECDMachine {
        SECDMachine {
            stack: Vec::new(),
            env: Vec::new(),
            control: vec![Cont::Exp(exp)],
            dump: DumpValue::Null,
        }
    }

    pub fn stack(&self) -> &Vec<StackValue> {
        &self.stack
    }

    pub fn env(&self) -> &Vec<Env> {
        &self.env
    }

    pub fn control(&self) -> &Vec<Cont> {
        &self.control
    }

    pub fn dump(&self) -> &DumpValue {
        &self.dump
    }

    pub fn lookup_env(&self, x: impl AsRef<str>) -> EnvValue {
        self.env
            .iter()
            .find_map(|e| {
                if e.var == x.as_ref() {
                    Some(e.val.clone())
                } else {
                    None
                }
            })
            .unwrap_or_else(|| EnvValue::Expr(LambdaExpression::Var(x.as_ref().to_string())))
    }

    pub fn is_done(&self) -> bool {
        self.control.is_empty() && self.dump == DumpValue::Null
    }

    pub fn get_result(&self) -> anyhow::Result<LambdaExpression> {
        if !(self.control.is_empty() && self.dump == DumpValue::Null) {
            anyhow::bail!("Not done yet");
        }
        let c = match self.stack.first().unwrap() {
            StackValue::Val(val) => return Ok(val.clone()),
            StackValue::Clo(c) => c.clone(),
        };

        c.try_into()
    }

    pub fn beta_transform(exp: LambdaExpression) -> anyhow::Result<LambdaExpression> {
        let mut secd = SECDMachine::new(exp);
        while !secd.is_done() {
            secd = secd.next()?;
        }

        secd.get_result()
    }

    pub fn beta_transform_with_log<W: std::fmt::Write>(
        exp: LambdaExpression,
        mut f: W,
    ) -> anyhow::Result<LambdaExpression> {
        let mut secd = SECDMachine::new(exp);
        fn print_pretty<W: std::fmt::Write>(machine: &SECDMachine, f: &mut W) -> std::fmt::Result {
            writeln!(f, "Stack  : {}", format_vec(machine.stack()))?;
            writeln!(f, "Env    : {}", format_vec(machine.env()))?;
            writeln!(f, "Control: {}", format_vec(machine.control()))?;
            writeln!(f, "Dump   : {}", machine.dump())?;

            Ok(())
        }
        print_pretty(&secd, &mut f)?;
        while !secd.is_done() {
            writeln!(f, "------------------------------------")?;
            print_pretty(&secd, &mut f)?;
            secd = secd.next()?;
        }
        writeln!(f, "------------------------------------")?;

        secd.get_result()
    }

    pub fn next(mut self) -> anyhow::Result<Self> {
        // 1. If 𝐶 is null, suppose the current dump 𝐷 is
        // (𝑆’, 𝐸′, 𝐶’, 𝐷′).
        // Then the current state is replaced by the state denoted by
        // (ℎ𝑆 ∶ 𝑆′, 𝐸′, 𝐶’, 𝐷′)
        let Some(hc) = self.control.pop() else {
            let DumpValue::Dump(mut d) = self.dump else {
                // no more control and dump
                return Ok(self);
            };
            if let Some(hs) = self.stack.pop() {
                d.stack.push(hs);
            }
            self.stack = d.stack;
            self.env = d.env;
            self.control = d.control;
            self.dump = *d.dump;
            return Ok(self);
        };

        // 2. If 𝐶 is not null, then ℎ𝐶 is inspected, and:
        match hc {
            // (2a) If ℎ𝐶 is an identifier 𝑋 (whose value relative to 𝐸 occupies the position
            // 𝑙𝑜𝑐𝑎𝑡𝑖𝑜𝑛𝐸𝑋 in 𝐸), then 𝑆 is replaced by
            // 𝑙𝑜𝑐𝑎𝑡𝑖𝑜𝑛𝐸𝑋𝐸: 𝑆
            // and 𝐶 is replaced by 𝑡𝐶.
            // We describe this step as follows: "Scanning 𝑋 causes 𝑙𝑜𝑐𝑎𝑡𝑖𝑜𝑛𝐸𝑋𝐸 to beloaded."
            Cont::Exp(LambdaExpression::Var(x)) => {
                let val = self.lookup_env(&x);
                self.stack.push(val.into());
            }
            // (2b) If ℎ𝐶 is a λ-expression 𝑋, scanning it causes the closure derived from 𝐸 and 𝑋
            // (as indicated above) to be loaded on to the stack.
            Cont::Exp(LambdaExpression::Lambda(x, e)) => {
                self.stack.push(StackValue::Clo(Closure {
                    bv: x,
                    body: *e,
                    env: self.env.clone(),
                }));
            }
            // (2c) If ℎ𝐶 is 𝑎𝑝, scanning it changes 𝑆 as follows:
            // ℎ𝑆 is inspected and:
            Cont::AP => {
                let Some(hs) = self.stack.pop() else {
                    anyhow::bail!("No more stack");
                };
                match hs {
                    // (2cl) If ℎ𝑆 is a closure, derived from 𝐸′ and 𝑋‘,
                    // then: 𝑆 is replaced by the 𝑛𝑢𝑙𝑙𝑖𝑠𝑡,
                    // 𝐸 is replaced by 𝑑𝑒𝑟𝑖𝑣𝑒(𝑎𝑠𝑠𝑜𝑐(𝑏𝑣𝑋′, 2𝑛𝑑𝑆))𝐸′,
                    // 𝐶 is replaced by 𝑢𝑛𝑖𝑡𝑙𝑖𝑠𝑡(𝑏𝑜𝑑𝑦𝑋′),
                    // 𝐷 is replaced by (𝑡(𝑡𝑆), 𝐸, 𝑡𝐶, 𝐷).
                    StackValue::Clo(closure) => {
                        let Some(second_s) = self.stack.pop() else {
                            anyhow::bail!("No more stack");
                        };
                        let dumpstack = self.stack.clone();
                        let dumpenv = self.env.clone();
                        // tC
                        let dumpcontrol = self.control.clone();
                        let dumpdump = self.dump.clone();

                        self.stack.clear();

                        self.env = closure.env.clone();
                        self.env.push(Env {
                            var: closure.bv,
                            val: second_s.into(),
                        });

                        self.control.clear();
                        self.control.push(Cont::Exp(closure.body));

                        self.dump = DumpValue::Dump(Dump {
                            stack: dumpstack,
                            env: dumpenv,
                            control: dumpcontrol,
                            dump: Box::new(dumpdump),
                        });
                    }
                    // (2c2) If ℎ𝑆 is not a closure, then scanning 𝑎𝑝 causes 𝑆 to be replaced by
                    StackValue::Val(first) => {
                        let Some(second_s) = self.stack.pop() else {
                            anyhow::bail!("No more stack");
                        };
                        let StackValue::Val(second_s) = second_s else {
                            anyhow::bail!("Expected Val");
                        };
                        self.stack.push(StackValue::Val(LambdaExpression::Apply(
                            Box::new(first),
                            Box::new(second_s),
                        )));
                    }
                }
            }
            // (2d) If ℎ𝐶 is a combination 𝑋, 𝐶 is replaced by 𝑟𝑎𝑛𝑑𝑋 ∶ (𝑟𝑎𝑡𝑜𝑟𝑋 ∶ (𝑎𝑝 ∶ 𝑡𝐶))
            Cont::Exp(LambdaExpression::Apply(f, x)) => {
                self.control.push(Cont::AP);
                self.control.push(Cont::Exp(*f));
                self.control.push(Cont::Exp(*x));
            }
        }

        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse() {
        let lambda = "λx.x".parse::<LambdaExpression>().unwrap();
        assert_eq!(
            lambda,
            LambdaExpression::Lambda(
                "x".to_string(),
                Box::new(LambdaExpression::Var("x".to_string()))
            )
        );

        let lambda = "λx.λy.y".parse::<LambdaExpression>().unwrap();
        assert_eq!(
            lambda,
            LambdaExpression::Lambda(
                "x".to_string(),
                Box::new(LambdaExpression::Lambda(
                    "y".to_string(),
                    Box::new(LambdaExpression::Var("y".to_string()))
                ))
            )
        );

        let lambda = "((λx.x) a)".parse::<LambdaExpression>().unwrap();
        assert_eq!(
            lambda,
            LambdaExpression::Apply(
                Box::new(LambdaExpression::Lambda(
                    "x".to_string(),
                    Box::new(LambdaExpression::Var("x".to_string()))
                )),
                Box::new(LambdaExpression::Var("a".to_string()))
            )
        );

        let lambda = "(((λx.(λy. y)) ((λx. (x x)) (λx. (x x)))) ((λx. x) a))"
            .parse::<LambdaExpression>()
            .unwrap();
        assert_eq!(
            lambda,
            LambdaExpression::Apply(
                Box::new(LambdaExpression::Apply(
                    Box::new(LambdaExpression::Lambda(
                        "x".to_string(),
                        Box::new(LambdaExpression::Lambda(
                            "y".to_string(),
                            Box::new(LambdaExpression::Var("y".to_string()))
                        ))
                    )),
                    Box::new(LambdaExpression::Apply(
                        Box::new(LambdaExpression::Lambda(
                            "x".to_string(),
                            Box::new(LambdaExpression::Apply(
                                Box::new(LambdaExpression::Var("x".to_string())),
                                Box::new(LambdaExpression::Var("x".to_string()))
                            ))
                        )),
                        Box::new(LambdaExpression::Lambda(
                            "x".to_string(),
                            Box::new(LambdaExpression::Apply(
                                Box::new(LambdaExpression::Var("x".to_string())),
                                Box::new(LambdaExpression::Var("x".to_string()))
                            ))
                        ))
                    ))
                )),
                Box::new(LambdaExpression::Apply(
                    Box::new(LambdaExpression::Lambda(
                        "x".to_string(),
                        Box::new(LambdaExpression::Var("x".to_string()))
                    )),
                    Box::new(LambdaExpression::Var("a".to_string()))
                ))
            )
        );
    }

    #[test]
    fn test_betatransform() {
        let lambda = "λx.x".parse::<LambdaExpression>().unwrap();
        let result = SECDMachine::beta_transform(lambda).unwrap();
        assert_eq!(result, "λx.x".parse::<LambdaExpression>().unwrap());

        let lambda = "λx.λy.y".parse::<LambdaExpression>().unwrap();
        let result = SECDMachine::beta_transform(lambda).unwrap();
        assert_eq!(result, "λx.λy.y".parse::<LambdaExpression>().unwrap());

        let lambda = "((λx.x) a)".parse::<LambdaExpression>().unwrap();
        let result = SECDMachine::beta_transform(lambda).unwrap();
        assert_eq!(result, "a".parse::<LambdaExpression>().unwrap());

        // 1. ((λx.λy.x) a) -> λy.a
        {
            let lambda = "((λx.λy.x) a)".parse::<LambdaExpression>().unwrap();
            let result = SECDMachine::beta_transform(lambda).unwrap();
            assert_eq!(result, "λy.a".parse::<LambdaExpression>().unwrap());
        }

        // 2. ((λx.λy.y) a) -> λy.y
        {
            println!("((λx.λy.y) a) -> λy.y");
            let lambda = "((λx.λy.y) a)".parse::<LambdaExpression>().unwrap();
            let result = SECDMachine::beta_transform(lambda).unwrap();
            // x を a で置換しても y に依存しないため同じ λy.y
            assert_eq!(result, "λy.y".parse::<LambdaExpression>().unwrap());
        }

        // 3. ((λx.x) ((λy.y) b)) -> b
        // (λy.y) b -> b となるため、結果は (λx.x) b -> b
        {
            println!("((λx.x) ((λy.y) b)) -> b");
            let lambda = "((λx.x) ((λy.y) b))".parse::<LambdaExpression>().unwrap();
            let result = SECDMachine::beta_transform(lambda).unwrap();
            assert_eq!(result, "b".parse::<LambdaExpression>().unwrap());
        }

        // 4. ((λx.x) ((λz.z z) (λw.w))) -> λw.w
        // ( (λz.z z) (λw.w) ) -> (λw.w)(λw.w) -> λw.w に簡約されるため
        // 最終的に (λx.x)(λw.w) -> λw.w
        {
            println!("((λx.x) ((λz.z z) (λw.w))) -> λw.w");
            let lambda = "((λx.x) ((λz.z z) (λw.w)))"
                .parse::<LambdaExpression>()
                .unwrap();
            let result = SECDMachine::beta_transform(lambda).unwrap();
            assert_eq!(result, "λw.w".parse::<LambdaExpression>().unwrap());
        }

        // 5. ((λx.(x a)) (λy.y)) -> a
        // まず (λx.(x a)) に (λy.y) を適用: xを(λy.y)で置換すると ((λy.y) a) -> a
        {
            println!("((λx.(x a)) (λy.y)) -> a");
            let lambda = "((λx.(x a)) (λy.y))".parse::<LambdaExpression>().unwrap();
            let result = SECDMachine::beta_transform(lambda).unwrap();
            assert_eq!(result, "a".parse::<LambdaExpression>().unwrap());
        }

        // 6. (((λx.λy.x) (λu.u)) v) -> (λu.u)
        // ( (λx.λy.x) (λu.u) ) -> λy.(λu.u)
        // さらにそれに v を適用: (λy.(λu.u)) v -> λu.u
        {
            println!("(((λx.λy.x) (λu.u)) v) -> (λu.u)");
            let lambda = "(((λx.λy.x) (λu.u)) v)"
                .parse::<LambdaExpression>()
                .unwrap();
            let result = SECDMachine::beta_transform(lambda).unwrap();
            assert_eq!(result, "λu.u".parse::<LambdaExpression>().unwrap());
        }

        // 7. ((λx.(λy.(y x))) a) -> λy.(y a)
        // x を a に置換: λy.(y a)
        {
            println!("((λx.(λy.(y x))) a) -> λy.(y a)");
            let lambda = "((λx.(λy.(y x))) a)".parse::<LambdaExpression>().unwrap();
            let result = SECDMachine::beta_transform(lambda).unwrap();
            assert_eq!(result, "λy.(y a)".parse::<LambdaExpression>().unwrap());
        }

        // 8. (((λx.x) (λy.(y y))) (λz.z)) -> λz.z
        // (λx.x) (λy.(y y)) -> (λy.(y y))
        // ((λy.(y y)) (λz.z)) -> (λz.z)(λz.z) -> λz.z
        {
            println!("(((λx.x) (λy.(y y))) (λz.z)) -> λz.z");
            let lambda = "(((λx.x) (λy.(y y))) (λz.z))"
                .parse::<LambdaExpression>()
                .unwrap();
            let result = SECDMachine::beta_transform(lambda).unwrap();
            assert_eq!(result, "λz.z".parse::<LambdaExpression>().unwrap());
        }

        // 9. ((λx.(λy.y)) (λx.x)) -> λy.y
        // (λx.(λy.y)) に (λx.x) を適用しても λy.y に変わらず。
        {
            println!("((λx.(λy.y)) (λx.x)) -> λy.y");
            let lambda = "((λx.(λy.y)) (λx.x))".parse::<LambdaExpression>().unwrap();
            let result = SECDMachine::beta_transform(lambda).unwrap();
            assert_eq!(result, "λy.y".parse::<LambdaExpression>().unwrap());
        }

        // 10. ((λx.(x (λz.z))) (λy.y)) -> λz.z
        // x を (λy.y) で置換: ( (λy.y) (λz.z) ) -> λz.z
        {
            println!("((λx.(x (λz.z))) (λy.y)) -> λz.z");
            let lambda = "((λx.(x (λz.z))) (λy.y))"
                .parse::<LambdaExpression>()
                .unwrap();
            let result = SECDMachine::beta_transform(lambda).unwrap();
            assert_eq!(result, "λz.z".parse::<LambdaExpression>().unwrap());
        }
    }
}
