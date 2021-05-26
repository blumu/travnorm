use crate::ast;

pub trait HasLength {
  fn length (&self) -> isize;
}

mod standard {
  pub fn len<T> (t:&super::ast::standard::Term<T>) -> isize {
    match t {
      super::ast::standard::Term::Var(_) => 1,

      super::ast::standard::Term::App((u, v)) => len(u)+ len(&v),

      super::ast::standard::Term::Abs((_, body)) => len(body)
    }
  }
}

impl<T> HasLength for ast::standard::Term<T>{
  fn length (&self) -> isize { standard::len(&self) }
}

pub mod alternating {
  fn len_app_var<T> (t:&super::ast::alternating::AppOrVar<T>) -> isize {
    match t {
      super::ast::alternating::AppOrVar::Var(v) =>
        1 + v.arguments.iter().map(|l| len_abs(l)).sum::<isize>(),

      super::ast::alternating::AppOrVar::App(a) =>
        1 + len_abs(&a.operator)
        + a.operands.iter().map(|l| len_abs(l)).sum::<isize>(),

    }
  }

  pub fn len_abs<T> (t:&super::ast::alternating::Term<T>) -> isize {
    1 + len_app_var(&t.body)
  }
}


impl<T> HasLength for ast::alternating::Term<T>{
  fn length (&self) -> isize {
    alternating::len_abs(&self)
  }
}