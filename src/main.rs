use std::io::{self, Write as _};

use secd_machine::LambdaExpression;

fn format_vec<T: std::fmt::Display>(vec: &[T]) -> String {
    let contents = vec
        .iter()
        .map(|item| format!("{}", item))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{}]", contents)
}

fn print_pretty(machine: &secd_machine::SECDMachine) {
    println!("Stack  : {}", format_vec(machine.stack()));
    println!("Env    : {}", format_vec(machine.env()));
    println!("Control: {}", format_vec(machine.control()));
    println!("Dump   : {}", machine.dump());
}

fn run(lambda: LambdaExpression) -> LambdaExpression {
    let mut secd = secd_machine::SECDMachine::new(lambda);

    print_pretty(&secd);
    while !secd.is_done() {
        println!("------------------------------------");
        secd = secd.next().unwrap();
        print_pretty(&secd);
    }
    println!("------------------------------------");

    secd.get_result().unwrap()
}

pub fn run_test() {
    let lambda = LambdaExpression::Apply(
        Box::new(LambdaExpression::Lambda(
            "x".to_string(),
            Box::new(LambdaExpression::Var("x".to_string())),
        )),
        Box::new(LambdaExpression::Var("a".to_string())),
    );
    println!("++++++++++++++++++++++++++++++++++++");
    println!("{}", &lambda);
    println!("{}", run(lambda));
    println!("++++++++++++++++++++++++++++++++++++");

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
    println!("++++++++++++++++++++++++++++++++++++");
    println!("{}", &lambda);
    println!("{}", run(lambda));
    println!("++++++++++++++++++++++++++++++++++++");

    let lambda: LambdaExpression = "(((λ𝑥.(λy. y)) ((λ𝑥. (x x)) (λ𝑥. (x x)))) ((λx. x) a))"
        .parse()
        .unwrap();
    println!("++++++++++++++++++++++++++++++++++++");
    println!("{}", &lambda);
    println!("{}", run(lambda));
    println!("++++++++++++++++++++++++++++++++++++");

    let lambda: LambdaExpression = "((\\x. (x y)) (\\x. (x x)))"
        .parse()
        .unwrap();
    println!("++++++++++++++++++++++++++++++++++++");
    println!("{}", &lambda);
    println!("{}", run(lambda));
    println!("++++++++++++++++++++++++++++++++++++");
}

fn main() {
    run_test();
    loop {
        print!("Enter lambda expression (or type 'exit' to quit): ");
        io::stdout().flush().unwrap();

        let mut input = String::new();
        if io::stdin().read_line(&mut input).is_err() {
            eprintln!("Failed to read input");
            continue;
        }

        let input = input.trim();
        if input.eq_ignore_ascii_case("exit") {
            break;
        }

        match input.parse::<LambdaExpression>() {
            Ok(lambda) => {
                println!("{}", &lambda);
                let result = run(lambda);
                println!("Result: {}", result);
            }
            Err(e) => {
                eprintln!("Error parsing lambda expression: {}", e);
            }
        }
    }
}