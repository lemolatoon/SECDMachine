pub mod lambda;
pub mod parse;
pub mod secd;
pub use lambda::LambdaExpression;
pub use secd::SECDMachine;
#[cfg(test)]
mod tests {
    use secd::SECDMachine;

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

    #[test]
    fn test_renamereduction() {
        let exp = "(\\x.\\y.x) y".parse::<LambdaExpression>().unwrap();
        let result = SECDMachine::beta_transform(exp).unwrap();
        assert_eq!(result, "\\y'.y".parse::<LambdaExpression>().unwrap());
        assert_eq!(
            result,
            LambdaExpression::lambda("y'", LambdaExpression::var("y"))
        );

        // shadowing, no need to rename
        let exp = "((\\x.\\y.x y) (\\y.y))"
            .parse::<LambdaExpression>()
            .unwrap();
        let result = SECDMachine::beta_transform(exp).unwrap();
        let var = |x| LambdaExpression::var(x);
        assert_eq!(
            result,
            LambdaExpression::lambda("y", LambdaExpression::lambda("y", var("y")).apply(var("y")))
        );

        let exp = "((\\x.\\y.x y) (y))".parse::<LambdaExpression>().unwrap();
        let result = SECDMachine::beta_transform(exp).unwrap();
        let var = |x| LambdaExpression::var(x);
        assert_eq!(
            result,
            LambdaExpression::lambda("y'", var("y").apply(var("y'")))
        );

        let succ = "λn.λf.λx.(n f) (f n)".parse::<LambdaExpression>().unwrap();
        let zero = "λf.λx.x".parse::<LambdaExpression>().unwrap();
        let one = succ.clone().apply(zero.clone());
        let mut log = String::new();
        let one_reduced = SECDMachine::beta_transform_with_log(one.clone(), &mut log).unwrap();
        println!("{}", log);

        assert_eq!(
            one_reduced,
            "λf.λx.f x".parse::<LambdaExpression>().unwrap()
        );
    }

    #[test]
    fn test_pred() {
        let succ = "λn.λf.λx.(n f) (f n)".parse::<LambdaExpression>().unwrap();
        assert_eq!(
            succ,
            LambdaExpression::Lambda(
                "n".to_string(),
                Box::new(LambdaExpression::Lambda(
                    "f".to_string(),
                    Box::new(LambdaExpression::Lambda(
                        "x".to_string(),
                        Box::new(LambdaExpression::Apply(
                            Box::new(LambdaExpression::Apply(
                                Box::new(LambdaExpression::Var("n".to_string())),
                                Box::new(LambdaExpression::Var("f".to_string()))
                            )),
                            Box::new(LambdaExpression::Apply(
                                Box::new(LambdaExpression::Var("f".to_string())),
                                Box::new(LambdaExpression::Var("n".to_string()))
                            ))
                        ))
                    ))
                ))
            )
        );

        let pair = "λx.λy.λf.f x y".parse::<LambdaExpression>().unwrap();
        assert_eq!(
            pair,
            LambdaExpression::Lambda(
                "x".to_string(),
                Box::new(LambdaExpression::Lambda(
                    "y".to_string(),
                    Box::new(LambdaExpression::Lambda(
                        "f".to_string(),
                        Box::new(LambdaExpression::Apply(
                            Box::new(LambdaExpression::Apply(
                                Box::new(LambdaExpression::Var("f".to_string())),
                                Box::new(LambdaExpression::Var("x".to_string()))
                            )),
                            Box::new(LambdaExpression::Var("y".to_string()))
                        ))
                    ))
                ))
            )
        );

        let fst = "λp.p (λx.λy.x)".parse::<LambdaExpression>().unwrap();
        assert_eq!(
            fst,
            LambdaExpression::Lambda(
                "p".to_string(),
                Box::new(LambdaExpression::Apply(
                    Box::new(LambdaExpression::Var("p".to_string())),
                    Box::new(LambdaExpression::Lambda(
                        "x".to_string(),
                        Box::new(LambdaExpression::Lambda(
                            "y".to_string(),
                            Box::new(LambdaExpression::Var("x".to_string()))
                        ))
                    ))
                ))
            )
        );

        let snd = "λp.p (λx.λy.y)".parse::<LambdaExpression>().unwrap();
        assert_eq!(
            snd,
            LambdaExpression::Lambda(
                "p".to_string(),
                Box::new(LambdaExpression::Apply(
                    Box::new(LambdaExpression::Var("p".to_string())),
                    Box::new(LambdaExpression::Lambda(
                        "x".to_string(),
                        Box::new(LambdaExpression::Lambda(
                            "y".to_string(),
                            Box::new(LambdaExpression::Var("y".to_string()))
                        ))
                    ))
                ))
            )
        );

        let p = LambdaExpression::var("p");
        let shift = LambdaExpression::lambda(
            "p",
            pair.clone()
                .apply(snd.clone().apply(p.clone()))
                .apply(succ.clone().apply(snd.apply(p))),
        );

        let zero = "λf.λx.x".parse::<LambdaExpression>().unwrap();
        let one = "λf.λx.f x".parse::<LambdaExpression>().unwrap();
        let two = "λf.λx.f (f x)".parse::<LambdaExpression>().unwrap();
        assert_eq!(
            two,
            LambdaExpression::Lambda(
                "f".to_string(),
                Box::new(LambdaExpression::Lambda(
                    "x".to_string(),
                    Box::new(LambdaExpression::Apply(
                        Box::new(LambdaExpression::Var("f".to_string())),
                        Box::new(LambdaExpression::Apply(
                            Box::new(LambdaExpression::Var("f".to_string())),
                            Box::new(LambdaExpression::Var("x".to_string()))
                        ))
                    ))
                ))
            )
        );

        // let result = SECDMachine::beta_transform(
        //     shift
        //         .clone()
        //         .apply(pair.clone().apply(zero.clone()).apply(one.clone())),
        // )
        // .unwrap();

        // assert_eq!(result, pair.clone().apply(one.clone()).apply(two.clone()));

        let pred = LambdaExpression::lambda(
            "n",
            LambdaExpression::var("n")
                .apply(shift.clone())
                .apply(pair.clone().apply(zero.clone()).apply(zero.clone())),
        );

        let reduced_pred = SECDMachine::beta_transform(pred.clone().apply(two.clone())).unwrap();
        println!("pred: {:?}", reduced_pred);
        println!("pred: {}", reduced_pred);
        println!("pred 2: {}", pred.clone().apply(two.clone()));
        println!(
            "pred 2: {}",
            SECDMachine::beta_transform(pred.clone().apply(two.clone())).unwrap()
        );

        let id = pred
            .clone()
            .apply(succ.clone().apply(LambdaExpression::var("x")));
        println!("id: {}", id);
        println!("id 2: {}", SECDMachine::beta_transform(id.clone()).unwrap());
    }
}
