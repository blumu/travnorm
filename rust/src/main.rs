
#[macro_use] extern crate lalrpop_util;
lalrpop_mod!(pub lambdaterms); // synthesized by LALRPOP

pub mod ast;

pub mod travnorm;

use crate::travnorm::{traverse, length};
use std::env;

#[test]
fn test_parser() {
    assert!(lambdaterms::TermParser::new().parse(" \\Lambda x . x x").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x . x x) (\Lambda x . x x)").is_ok());
    assert!(lambdaterms::TermParser::new().parse("y z").is_ok());
    assert!(lambdaterms::TermParser::new().parse("(y z) u").is_ok());
    assert!(lambdaterms::TermParser::new().parse("y z u").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x . x x) w").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x . x x) (w z)").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(y z) u (\Lambda x . x x)").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(y z) u (\Lambda x . x x) (\Lambda x . x x)").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"\Lambda x y . x y ").is_ok());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x y . x y) (\Lambda x . x x)").is_ok());


    assert!(lambdaterms::TermParser::new().parse("(λx y . x y) (λ x . x x)").is_ok());
    assert!(lambdaterms::TermParser::new().parse("(λ x y . x y) (λ x . x x)").is_ok());

    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda x y . x y) \Lambda x . x x").is_err());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda  . x y)").is_err());
    assert!(lambdaterms::TermParser::new().parse(r"(\Lambda  . x y)").is_err());
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let sample_term = "(λu.u(x u))(λv.v y)";

    let t_as_string : &str=
        if args.len() > 1 {
            &args[1]
        } else {
            sample_term
        };

    println!("Parsing lambda term {}", t_as_string);

    let t = lambdaterms::TermParser::new().parse(t_as_string);

    match t {
        Err(e) =>
            println!(
                "Could not parse the term `{}`. Error: {}", t_as_string,e
            ),
        Ok(t) => {
            let n = length(t);
            println!("term has length {}", n);
        }
    }

}
