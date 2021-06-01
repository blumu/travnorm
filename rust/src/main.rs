
#[macro_use] extern crate lalrpop_util;
lalrpop_mod!(pub lambdaterms); // synthesized by LALRPOP
lalrpop_mod!(pub alt_lambdaterms); // synthesized by LALRPOP


pub mod ast;

pub mod traversal;

pub mod term;

use std::env;
use std::io::{self, BufRead};
use crate::term::{HasLength};

#[cfg(test)]
mod parser_tests;

struct Commands {
    enumerate : bool,
    normalize : bool,
    normalize_resolve : bool,
    configuration : traversal::Configuration
}

fn usage(exe_path : &str) {
    println!("Syntax:");
    println!("  {} <OPTIONS> -", exe_path);
    println!("  {} <OPTIONS> \"<lambda term>\"", exe_path);
    println!("where <OPTIONS> can be a combination of:");
    println!("    --enumerate             enumerate all traversals");
    println!("    --normalize             normalize the term (default)");
    println!("    --normalize_resolve     normalize the term with name resolution");
    println!("    --verbose [0|1|2|3]     set verbosity level");
    println!("    --no-pumping            do not pump out internal ghost copy-cat occurrences.");
    println!("                            Note: this yields very long traversals as defined in the paper.");
    println!("Pass '-' as a parameter to read from the lambda term from standard input. ");
    println!("Pass a lambda term in double-quotes to read the lambda term from the command-line arguments. ")
}

fn usage_and_exit(exe_path : &str) -> ! {
  usage(&exe_path);
  std::process::exit(1);
}

fn main() {
  let mut args: Vec<String> = env::args().collect();

  let exe_path = args.remove(0);

  let mut commands = Commands {
    enumerate : false,
    normalize : false,
    normalize_resolve : false,
    configuration : traversal::Configuration::default()
  };

  while !args.is_empty() {
    match args.first() {
      None => break,
      Some(arg) if arg.eq_ignore_ascii_case("--enumerate") => commands.enumerate = true,
      Some(arg) if arg.eq_ignore_ascii_case("--normalize") => commands.normalize = true,
      Some(arg) if arg.eq_ignore_ascii_case("--normalize_resolve") => commands.normalize_resolve = true,
      Some(arg) if arg.eq_ignore_ascii_case("--no-pumping") => commands.configuration.pump_out_copycat_ghosts = false,
      Some(arg) if arg.eq_ignore_ascii_case("--verbose") => {
        args.remove(0);
        match args.first() {
          None => {
            eprintln!("Missing argument for --verbose");
            usage_and_exit(&exe_path);
          },
          Some(value) => {
              match value.parse::<u32>() {
              Ok(0) => {
                commands.configuration.verbose = false;
                commands.configuration.very_verbose = false;
                commands.configuration.debug = false;
              },
              Ok(1) => {
                commands.configuration.verbose = true;
                commands.configuration.very_verbose = false;
                commands.configuration.debug = false;
              },
              Ok(_) => {
                commands.configuration.verbose = true;
                commands.configuration.very_verbose = true;
                commands.configuration.debug = true;
              },
              Err(e) => {
                eprintln!("Invalid argument for --verbose: {}", e);
                usage_and_exit(&exe_path);
              }
            }
          }
        }
      },
      Some(arg) if arg.starts_with("--") => {
        eprintln!("Unrecognized switch: {}", arg);
        usage_and_exit(&exe_path);
      },
      _ => break
    };
    args.remove(0);
  }
 if !commands.normalize_resolve
  && !commands.enumerate
  && !commands.normalize  {
      println!("No command specified, defaulting to normalization with name resolution.");
      commands.normalize_resolve = true
  }
 let t_as_string =
      match args.first() {
          None => {
              println!("Reading input lambda term from standard input");
              let stdin = io::stdin();
              let line = stdin.lock()
                  .lines()
                  .next()
                  .expect("there was no next line")
                  .expect("the line could not be read");
              line
          }
          Some(term_arg) => {
              println!("Reading input lambda term from command-line argument");
              term_arg.to_owned()
         }
      };
 println!("Parsing lambda term '{}'", &t_as_string);
 let parsed = alt_lambdaterms::TermParser::new().parse(&t_as_string);
 match parsed {
      Err(e) =>
          println!(
              "Could not parse the term `{}`. Error: {}", t_as_string,e
          ),
      Ok(term) => {
          let n = term.length();
          println!("term has length {}", n);
         if commands.enumerate {
              println!("===== Enumerate all traversals");
              traversal::enumerate_all_traversals(&commands.configuration, &term);
          }
          if commands.normalize {
              println!("===== Evaluation without name resolution");
              traversal::evaluate_and_print_normal_form(&commands.configuration,&term);
          }
         if commands.normalize_resolve {
              println!("===== Evaluation with name resolution");
              traversal::evaluate_resolve_print_normal_form(&commands.configuration,&term);
          }
     }
  }
}
