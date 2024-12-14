use std::collections::BTreeSet;

use secd_machine::LambdaExpression;

fn run(lambda: LambdaExpression, constants: BTreeSet<String>) -> LambdaExpression {
    let mut secd = secd_machine::SECDMachine::new(lambda, constants);

    println!("{}", secd);
    while !secd.is_done() {
        secd = secd.next().unwrap();

        println!("{}", secd);
    }

    secd.get_result().unwrap()
}

fn main() {
    let lambda = LambdaExpression::Apply(
        Box::new(LambdaExpression::Lambda(
            "x".to_string(),
            Box::new(LambdaExpression::Var("x".to_string())),
        )),
        Box::new(LambdaExpression::Var("a".to_string())),
    );
    let constants = vec!["a".to_string()].into_iter().collect();
    println!("{}", &lambda);
    println!("|");
    println!("v");
    println!("{}", run(lambda, constants));

    let lambda = LambdaExpression::Apply(
        Box::new(LambdaExpression::Lambda(
            "x".to_string(),
            Box::new(LambdaExpression::Lambda(
                "y".to_string(),
                Box::new(LambdaExpression::Var("y".to_string())),
            )),
        )),
        Box::new(LambdaExpression::Apply(
            Box::new(LambdaExpression::Lambda(
                "x".to_string(),
                Box::new(LambdaExpression::Var("x".to_string())),
            )),
            Box::new(LambdaExpression::Var("a".to_string())),
        )),
    );
    let constants = vec!["a".to_string()].into_iter().collect();
    println!("{}", &lambda);
    println!("|");
    println!("v");
    println!("{}", run(lambda, constants));

    let lambda: LambdaExpression = "(((λ𝑥.(λy. y)) ((λ𝑥. (x x)) (λ𝑥. (x x)))) ((λx. x) a))"
        .parse()
        .unwrap();
    let constants = vec!["a".to_string()].into_iter().collect();
    println!("{}", &lambda);
    println!("|");
    println!("v");
    println!("{}", run(lambda, constants));
}
