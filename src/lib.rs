mod parse;

use std::{
    fmt::Display,
    str::FromStr,
};

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
pub struct Env {
    var: String,
    val: LambdaExpression,
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
            format_vec(&self.stack), format_vec(&self.env), format_vec(&self.control), self.dump
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

    pub fn lookup_env(&self, x: impl AsRef<str>) -> LambdaExpression {
        self.env.iter().find_map(|e| {
            if e.var == x.as_ref() {
                Some(e.val.clone())
            } else {
                None
            }
        }).unwrap_or_else(|| LambdaExpression::Var(x.as_ref().to_string()))
    }

    pub fn is_done(&self) -> bool {
        self.control.is_empty() && self.dump == DumpValue::Null
    }

    pub fn get_result(&self) -> anyhow::Result<LambdaExpression> {
        if self.control.is_empty() && self.dump == DumpValue::Null {
            if self.stack.len() == 1 {
                if let StackValue::Val(val) = self.stack.first().unwrap() {
                    return Ok(val.clone());
                }
            }
        }
        anyhow::bail!("Not done yet");
    }

    pub fn next(mut self) -> anyhow::Result<Self> {
        // 1. If 𝐶 is null, suppose the current dump 𝐷 is
        // (𝑆’, 𝐸′, 𝐶’, 𝐷′).
        // Then the current state is replaced by the state denoted by
        // (ℎ𝑆 ∶ 𝑆′, 𝐸′, 𝐶’, 𝐷′)
        let Some(hc) = self.control.pop() else {
            let DumpValue::Dump(d) = self.dump else {
                // no more control and dump
                return Ok(self);
            };
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
                self.stack.push(StackValue::Val(val.clone()));
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
                        self.env = closure.env.clone();
                        let Some(second_s) = self.stack.pop() else {
                            anyhow::bail!("No more stack");
                        };
                        let StackValue::Val(second_s) = second_s else {
                            anyhow::bail!("Expected Val");
                        };
                        self.env.push(Env {
                            var: closure.bv,
                            val: second_s,
                        });

                        self.control.clear();
                        self.control.push(Cont::Exp(closure.body));

                        self.dump = DumpValue::Dump(Dump {
                            stack: self.stack.clone(),
                            env: self.env.clone(),
                            control: self.control.clone(),
                            dump: Box::new(self.dump.clone()),
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
