use crate::ast;

pub trait HasLength {
  fn length (&self) -> isize;
}

mod standard {
  pub fn len<T> (t:&super::ast::standard::Term<T>) -> isize {
    match t {
      super::ast::standard::Term::Variable(_) => 1,

      super::ast::standard::Term::App((u, v)) => len(u)+ len(&v),

      super::ast::standard::Term::Abs((_, body)) => len(body)
    }
  }
}

impl<T> HasLength for ast::standard::Term<T>{
  fn length (&self) -> isize { standard::len(&self) }
}

pub mod alternating_rc {
  fn len_app_var<T> (t:&super::ast::alternating_rc::AppOrVar<T>) -> isize {
    match t {
      super::ast::alternating_rc::AppOrVar::Var(v) =>
        1 + v.arguments.iter().map(|l| len_abs(l)).sum::<isize>(),

      super::ast::alternating_rc::AppOrVar::App(a) =>
        1 + len_abs(&a.operator)
        + a.operands.iter().map(|l| len_abs(l)).sum::<isize>(),

    }
  }

  pub fn len_abs<T> (t:&super::ast::alternating_rc::Term<T>) -> isize {
    1 + len_app_var(&t.body)
  }
}


impl<T> HasLength for ast::alternating_rc::Term<T>{
  fn length (&self) -> isize {
    alternating_rc::len_abs(&self)
  }
}