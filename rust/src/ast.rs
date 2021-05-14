pub mod standard {
  pub type Var<T> = T;

  pub type Abs<T> = (Vec<T>, Box<Term<T>>);

  pub type App<T> = (Box<Term<T>>, Box<Term<T>>);

  pub enum Term<T> {
      Variable(Var<T>),
      App(App<T>),
      Abs(Abs<T>)
  }

  pub type LambdaTerm = Term<String>;

}

pub mod alternating {

  #[derive(Clone)]
  pub struct Var<T> {
    pub name:T,
    pub arguments: Vec<Abs<T>>
  }

  #[derive(Clone)]
  pub struct Abs<T> {
    pub bound_variables : Vec<T>,
    pub body:AppOrVar<T>
  }

  #[derive(Clone)]
  pub struct App<T> {
    pub operator : Abs<T>,
    pub operands: Vec<Abs<T>>
  }

  #[derive(Clone)]
  pub enum AppOrVar<T> {
    App( Box<App<T>> ),
    Var( T )
  }

  pub enum Term<T> {
    Var (Var<T>),
    App(App<T>),
    Abs (Abs<T>)
  }

  pub type LambdaTerm = Term<String>;


}



pub mod alternating_rc {
  use std::rc::Rc;

  #[derive(Clone)]
  pub struct Var<T> {
    pub name:T,
    pub arguments: Vec<Rc<Abs<T>>>
  }

  #[derive(Clone)]
  pub struct Abs<T> {
    pub bound_variables : Vec<T>,
    pub body:AppOrVar<T>
  }

  #[derive(Clone)]
  pub struct App<T> {
    pub operator : Rc<Abs<T>>,
    pub operands: Vec<Rc<Abs<T>>>
  }

  #[derive(Clone)]
  pub enum AppOrVar<T> {
    App( Rc<App<T>> ),
    Var( T )
  }

  pub enum Term<T> {
    Var (Var<T>),
    App (App<T>),
    Abs (Abs<T>)
  }

  pub type LambdaTerm = Term<String>;


}
