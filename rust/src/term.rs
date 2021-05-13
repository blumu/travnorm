use crate::ast;

pub fn length<T> (t:ast::standard::Term<T>) -> i32 {
  match t {
    ast::standard::Term::Variable(_) => 1,

    ast::standard::Term::App((u, v)) => 1 + length(*u) + length(*v),

    ast::standard::Term::Abs((_, body)) => length(*body)
  }
}