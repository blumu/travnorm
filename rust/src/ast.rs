use std::string::String;

pub type Var<T> = T;

pub type Abs<T> = (Vec<T>, Box<LmdTerm<T>>);

pub type App<T> = (Box<LmdTerm<T>>, Box<LmdTerm<T>>);


pub enum LmdTerm<T> {
    Variable(Var<T>),
    App(App<T>),
    Abs(Abs<T>)
}

pub type LambdaTerm = LmdTerm<String>;


mod alternating {
  enum Term<T> {
    Var { name:T, arguments: Vec<Abs<T>> },
    App { operator :Abs<T>, operands: Vec<Abs<T>>},
    Abs { bound_variables : Vec<String>, body:AppOrVar<T> }
  }

  struct Abs<T> {
    bound_variables : Vec<String>,
    body:AppOrVar<T>
  }

  struct App<T> {
    operator :Abs<T>,
    operands: Vec<Abs<T>>
  }


  enum AppOrVar<T> {
    App( Box<App<T>> ),
    Var( T )
  }
}
