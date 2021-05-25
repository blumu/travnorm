
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

    let sample_term =
        //r"(λu.u(x u))(λv.v y)"
        r"(λ t . t (λ n a x . n (λ s z . a s (x s z))) (λ a . a) (λ z0 . z0) ) (λ s2 z2 . s2 (s2 z2))"
        //r"(λ x . x y) (λ z . z w)"
        ;

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

            println!("===== Evaluation with name resolution");
            traversal::evaluate_resolve_print_normal_form(&term);

        }
    }

}
