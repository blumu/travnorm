use crate::ast::{LambdaTerm};


enum AlternatingAst<T> {
    Var{ name:T, arguments: Vec<AlternatingAstAbs<T>> },
    App { operator :AlternatingAstAbs<T>, operands: Vec<AlternatingAstAbs<T>>},
    Abs{ bound_variables : Vec<String>, body:AppOrVar<T> }
}

struct AlternatingAstAbs<T> {
    bound_variables : Vec<String>,
    body:AppOrVar<T>
}

struct AlternatingAstApp<T> {
  operator :AlternatingAstAbs<T>,
  operands: Vec<AlternatingAstAbs<T>>
}


enum AppOrVar<T> {
  App( Box<AlternatingAstApp<T>> ),
  Var( T)
}

pub fn length (t:LambdaTerm) -> i32 {
  match t {
    LambdaTerm::Variable(_) => 1,

    LambdaTerm::App(u, v) => 1 + traverse(*u) + traverse(*v),

    LambdaTerm::Lambda(_, body) => traverse(*body)
  }
}


pub fn traverse (t:LambdaTerm) -> i32 {
  match t {
    LambdaTerm::Variable(s) => 1,

    LambdaTerm::App(u, v) => 1 + traverse(*u) + traverse(*v),

    LambdaTerm::Lambda(names, body) => traverse(*body)
  }
}