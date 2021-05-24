
#[macro_use] extern crate lalrpop_util;
lalrpop_mod!(pub lambdaterms); // synthesized by LALRPOP
lalrpop_mod!(pub alt_lambdaterms); // synthesized by LALRPOP


pub mod ast;

pub mod traversal;

pub mod term;

use crate::term::{HasLength};
use std::env;

#[cfg(test)]
mod parser_tests;

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

    //let t = lambdaterms::TermParser::new().parse(t_as_string);
    let parsed = alt_lambdaterms::TermParser::new().parse(t_as_string);

    match parsed {
        Err(e) =>
            println!(
                "Could not parse the term `{}`. Error: {}", t_as_string,e
            ),
        Ok(term) => {
            let n = term.length();
            println!("term has length {}", n);

            println!("===== Evaluation without name resolution");
            traversal::evaluate_and_print_normal_form(&term);

        }
    }

}
