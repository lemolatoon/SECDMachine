pub mod lambda;
pub mod parse;
pub mod secd;
pub use lambda::LambdaExpression;
pub use secd::SECDMachine;
#[cfg(test)]
mod tests {
    use lambda::AnalyzedLambdaExpression;
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

        // 11. (λf.(λx.(((λf.(λx.(f x))) f) (f x))))) -> λf.λx.f (f x)
        {
            println!("(λf.(λx.(((λf.(λx.(f x))) f) (f x))))) -> λf.λx.f (f x)");
            let lambda = "λf.(λx.(((λf.(λx.(f x))) f) (f x)))"
                .parse::<LambdaExpression>()
                .unwrap();
            let (result, log) =
                SECDMachine::beta_reduction_with_body_simplification(lambda).unwrap();
            println!("{}", log);
            assert_eq!(
                result,
                "λf.λx.f (f x)".parse::<LambdaExpression>().unwrap(),
                "result: {}, expected: {}",
                result,
                "λf.λx.f (f x)".parse::<LambdaExpression>().unwrap()
            );
        }
        // 12. f (λf.(λx.(((λf.(λx.(f x))) f) (f x))))) -> f (λf.λx.f (f x))
        {
            println!("f (λf.(λx.(((λf.(λx.(f x))) f) (f x))))) -> f (λf.λx.f (f x))");
            let lambda = "f (λf.(λx.(((λf.(λx.(f x))) f) (f x))))"
                .parse::<LambdaExpression>()
                .unwrap();
            let (result, log) =
                SECDMachine::beta_reduction_with_body_simplification(lambda).unwrap();
            println!("{}", log);
            assert_eq!(
                result,
                "f (λf.λx.f (f x))".parse::<LambdaExpression>().unwrap(),
                "result: {}, expected: {}",
                result,
                "f (λf.λx.f (f x))".parse::<LambdaExpression>().unwrap()
            );
        }

        // 13. (((\x. (x a)) (\x. (x a)) y)) -> (a a) y
        {
            println!("(((\\x. (x a)) (\\x. (x a)) y)) -> (a a) y");
            let lambda = "(((\\x. (x a)) (\\x. (x a)) y))"
                .parse::<LambdaExpression>()
                .unwrap();
            let f = LambdaExpression::lambda(
                "x",
                LambdaExpression::var("x").apply(LambdaExpression::var("a")),
            );
            let lambda_constructed = f.clone().apply(f.clone()).apply(LambdaExpression::var("y"));
            assert_eq!(lambda, lambda_constructed);
            let result = SECDMachine::beta_transform(lambda).unwrap();
            assert_eq!(result, "(a a) y".parse::<LambdaExpression>().unwrap());
        }

        // 14. ((\x. x) ((λn.(λf.(λx.((n f) (f x))))) (λf.(λx.x))))) -> \f.\x.f x
        {
            println!("((\\x.\\y.\\z. x a) ((λn.(λf.(λx.((n f) (f x))))) (λf.(λx.x))))) -> \\y.\\z.\\x.a x");
            let lambda = "((\\x.\\y.\\z. x a) ((λn.(λf.(λx.((n f) (f x))))) (λf.(λx.x))))"
                .parse::<LambdaExpression>()
                .unwrap();
            let (result, _) = SECDMachine::beta_reduction_with_body_simplification(lambda).unwrap();
            assert_eq!(
                result,
                "\\y.\\z.\\x.a x".parse::<LambdaExpression>().unwrap()
            );
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

        let exp = "(\\x.\\y.(y x)) y".parse::<LambdaExpression>().unwrap();
        let result = SECDMachine::beta_transform(exp).unwrap();
        assert_eq!(result, "\\y'.(y' y)".parse::<LambdaExpression>().unwrap());

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

        let succ = "λn.λf.λx.(n f) (f x)".parse::<LambdaExpression>().unwrap();
        let zero = "λf.λx.x".parse::<LambdaExpression>().unwrap();
        let one = succ.clone().apply(zero.clone());
        let (one_reduced, log) =
            SECDMachine::beta_reduction_with_body_simplification(one.clone()).unwrap();
        println!("{}", log);

        assert_eq!(
            one_reduced,
            "λf.λx.f x".parse::<LambdaExpression>().unwrap(),
            "result: {}, expected: {}",
            one_reduced,
            "λf.λx.f x".parse::<LambdaExpression>().unwrap()
        );

        let succ_renamed = "\\n'.\\f'.\\x'.(n' f') (f' x')"
            .parse::<LambdaExpression>()
            .unwrap();
        println!("SUCC RENAMED: {}", succ_renamed);
        let suc_suc_zero = succ_renamed
            .clone()
            .apply(succ.clone().apply(zero.clone()).clone());
        let (suc_suc_zero_reduced, log) =
            SECDMachine::beta_reduction_with_body_simplification(suc_suc_zero.clone()).unwrap();
        println!("========== START SUCC SUCC ZERO ==========");
        println!("{}", log);
        let expected= "λf.λx.f (f x)".parse::<LambdaExpression>().unwrap();
        assert!(
            suc_suc_zero_reduced.alpha_equiv(&expected),
            "result: {}, expected: {}",
            suc_suc_zero_reduced,
            expected,
        );
    }

    #[test]
    fn test_pair() {
        let pair = "λx.λy.λf.f x y".parse::<LambdaExpression>().unwrap();
        let fst = "λp.p (λx.λy.x)".parse::<LambdaExpression>().unwrap();
        let snd = "λp.p (λx.λy.y)".parse::<LambdaExpression>().unwrap();

        let x = "x".parse::<LambdaExpression>().unwrap();
        let y = "y".parse::<LambdaExpression>().unwrap();

        let x_y_pair = pair.clone().apply(x.clone()).apply(y.clone());

        let first_x = fst.clone().apply(x_y_pair.clone());

        let (result, _) =
            SECDMachine::beta_reduction_with_body_simplification(first_x.clone()).unwrap();

        assert_eq!(result, x);

        let x_y_pair = pair.clone().apply(first_x.clone()).apply(y.clone());

        let first_x = fst.clone().apply(x_y_pair.clone());

        let (result, _) =
            SECDMachine::beta_reduction_with_body_simplification(first_x.clone()).unwrap();

        assert_eq!(result, x);

        let x_y_pair = pair.clone().apply(pair.clone()).apply(first_x.clone());

        let first_x = snd.clone().apply(x_y_pair.clone());

        println!("FIRST_X: {}", first_x);

        let (result, _) =
            SECDMachine::beta_reduction_with_body_simplification(first_x.clone()).unwrap();

        assert_eq!(result, x);
    }

    #[test]
    fn test_pred() {
        let succ = "λn.λf.λx.(n f) (f x)".parse::<LambdaExpression>().unwrap();
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
                                Box::new(LambdaExpression::Var("x".to_string()))
                            ))
                        ))
                    ))
                ))
            )
        );

        let zero = "λf.λx.x".parse::<LambdaExpression>().unwrap();
        let one = "λf.λx.f x".parse::<LambdaExpression>().unwrap();
        let two = "λf.λx.f (f x)".parse::<LambdaExpression>().unwrap();

        let (succ_zero, _) =
            SECDMachine::beta_reduction_with_body_simplification(succ.clone().apply(zero.clone()))
                .unwrap();

        assert_eq!(succ_zero, one);

        let (succ_one, _) =
            SECDMachine::beta_reduction_with_body_simplification(succ.clone().apply(one.clone()))
                .unwrap();

        assert_eq!(succ_one, two);

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

        let x_y_pair = pair
            .clone()
            .apply(LambdaExpression::var("x"))
            .apply(LambdaExpression::var("y"));
        let (x_y_pair, _) = SECDMachine::beta_reduction_with_body_simplification(x_y_pair).unwrap();

        let (x_extracted, _) = SECDMachine::beta_reduction_with_body_simplification(
            fst.clone().apply(x_y_pair.clone()),
        )
        .unwrap();

        let (y_extracted, _) = SECDMachine::beta_reduction_with_body_simplification(
            snd.clone().apply(x_y_pair.clone()),
        )
        .unwrap();

        assert_eq!(x_extracted, LambdaExpression::var("x"));
        assert_eq!(y_extracted, LambdaExpression::var("y"));

        let p = LambdaExpression::var("p");
        let shift = LambdaExpression::lambda(
            "p",
            pair.clone()
                .apply(snd.clone().apply(p.clone()))
                .apply(succ.clone().apply(snd.apply(p))),
        );

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

        let (result, log) = SECDMachine::beta_reduction_with_body_simplification(
            shift
                .clone()
                .apply(pair.clone().apply(zero.clone()).apply(one.clone())),
        )
        .unwrap();
        println!("{}", log);

        let (expected, _log) = SECDMachine::beta_reduction_with_body_simplification(
            pair.clone().apply(one.clone()).apply(two.clone()),
        )
        .unwrap();

        assert!(
            AnalyzedLambdaExpression::alpha_equiv(
                &result.clone().into_analyzed(),
                &expected.clone().into_analyzed()
            ),
            "result: {}, expected: {}",
            result,
            expected
        );

        let pred = LambdaExpression::lambda(
            "n",
            fst.clone().apply(
                LambdaExpression::var("n")
                    .apply(shift.clone())
                    .apply(pair.clone().apply(zero.clone()).apply(zero.clone())),
            ),
        );

        let pred_2 = pred.clone().apply(two.clone());
        let (pred_2, _log) = SECDMachine::beta_reduction_with_body_simplification(pred_2).unwrap();

        assert_eq!(pred_2, one);

        let pred_1 = pred.clone().apply(one.clone());

        let (pred_1, _log) = SECDMachine::beta_reduction_with_body_simplification(pred_1).unwrap();
        assert_eq!(pred_1, zero);

        let pred_0 = pred.clone().apply(zero.clone());

        let (pred_0, _log) = SECDMachine::beta_reduction_with_body_simplification(pred_0).unwrap();
        assert_eq!(pred_0, zero);
    }

    #[test]
    fn test_predicate_church_numbers() {
        use super::*;

        let zero = "λf.λx.x".parse::<LambdaExpression>().unwrap();
        let one = "λf.λx.f x".parse::<LambdaExpression>().unwrap();
        let two = "λf.λx.f (f x)".parse::<LambdaExpression>().unwrap();
        let pred = "λn.λf.λx. n (λg.λh. h (g f)) (λu.x) (λu.u)"
            .parse::<LambdaExpression>()
            .unwrap();

        // pred 2 => 1
        let pred_2 = pred.clone().apply(two.clone());
        let (pred_2, _log) = SECDMachine::beta_reduction_with_body_simplification(pred_2).unwrap();
        assert_eq!(pred_2, one, "pred 2 should be 1");

        // pred 1 => 0
        let pred_1 = pred.clone().apply(one.clone());
        let (pred_1, _log) = SECDMachine::beta_reduction_with_body_simplification(pred_1).unwrap();
        assert_eq!(pred_1, zero, "pred 1 should be 0");

        // pred 0 => 0
        let pred_0 = pred.clone().apply(zero.clone());
        let (pred_0, _log) = SECDMachine::beta_reduction_with_body_simplification(pred_0).unwrap();
        assert_eq!(pred_0, zero, "pred 0 should be 0");

        let pred_pred_2 = pred.clone().apply(pred.clone().apply(two.clone()));
        let (pred_pred_2, _log) =
            SECDMachine::beta_reduction_with_body_simplification(pred_pred_2).unwrap();
        assert_eq!(pred_pred_2, zero, "pred (pred 2) should be 0");

        let succ = "λn.λf.λx.(n f) (f x)".parse::<LambdaExpression>().unwrap();
        let succ_pred_2 = succ.clone().apply(pred.clone().apply(two.clone()));
        let (succ_pred_2, _log) =
            SECDMachine::beta_reduction_with_body_simplification(succ_pred_2).unwrap();

        assert_eq!(succ_pred_2, two, "succ (pred 2) should be 2");
    }

    #[test]
    fn test_suc() {
        let church_n = |n| {
            let mut church_n = "λf.λx.".to_string();
            for _ in 0..n {
                church_n.push_str("f (");
            }

            church_n.push_str("x");
            church_n.push_str(&")".repeat(n));
            church_n.parse::<LambdaExpression>().unwrap()
        };

        let succ = || "λn.λf.λx.(n f) (f x)".parse::<LambdaExpression>().unwrap();
        let apply_succ_n_times = |n, mut exp| {
            for _ in 0..n {
                exp = succ().apply(exp);
            }
            exp
        };

        for i in 0..10 {
            let n = church_n(i);
            let n_plus_1_reduced = apply_succ_n_times(i, church_n(0));
            let (n_plus_1_reduced, log) =
                SECDMachine::beta_reduction_with_body_simplification(n_plus_1_reduced).unwrap();
            println!("{}", log);
            assert!(
                n_plus_1_reduced.alpha_equiv(&n),
                "{}: {}\nleft: {}, right: {}",
                i,
                n,
                n_plus_1_reduced,
                n
            );
        }

        let pred = || {
            "λn.λf.λx. n (λg.λh. h (g f)) (λu.x) (λu.u)"
                .parse::<LambdaExpression>()
                .unwrap()
        };
        let apply_pred_n_times = |n, mut exp| {
            for _ in 0..n {
                exp = pred().apply(exp);
            }
            exp
        };
        let zero = || church_n(0);
        for i in 0..10 {
            let n_minus_n = apply_pred_n_times(i, church_n(i));
            let (n_minus_n_reduced, _log) =
                SECDMachine::beta_reduction_with_body_simplification(n_minus_n).unwrap();
            assert!(
                n_minus_n_reduced.alpha_equiv(&zero()),
                "{}: left: {}, right: {}",
                i,
                n_minus_n_reduced,
                zero()
            );
        }
        let plus = || {
            "λm. λn. λf.λx. m f (n f x)"
                .parse::<LambdaExpression>()
                .unwrap()
        };
        let plus_2_3 = plus()
            .apply(church_n(2))
            .apply(church_n(3));
        let five = church_n(5);
        let (plus_2_3_reduced, log) =
            SECDMachine::beta_reduction_with_body_simplification(plus_2_3.clone()).unwrap();
        println!("{}", log);

        assert_eq!(plus_2_3_reduced, five);
        for i in 0..3 {
            for j in 0..3 {
                let m = church_n(i);
                let n = church_n(j);
                let m_plus_n = plus().apply(m).apply(n);
                let (m_plus_n_reduced, _log) =
                    SECDMachine::beta_reduction_with_body_simplification(m_plus_n).unwrap();
                let expected = church_n(i + j);
                assert!(
                    m_plus_n_reduced.alpha_equiv(&expected),
                    "i: {}, j: {}, left: {}, right: {}",
                    i,
                    j,
                    m_plus_n_reduced,
                    expected
                );
            }
        }
    }

    #[test]
    fn test_complicated() {
        let lambda: LambdaExpression = "\\n. (\\x. (x y)) (\\x. (x ((\\x. (x y)) (\\x. (x y)))))"
            .parse()
            .unwrap();

        let (result, log) =
            SECDMachine::beta_reduction_with_body_simplification(lambda.clone()).unwrap();
        println!("{}", log);

        let expected: LambdaExpression = "\\n. (y (y y))".parse().unwrap();
        assert_eq!(result, expected);
    }
}
