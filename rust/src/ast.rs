/// Various AST representations of lambda terms
/// parameterized by a 'name referencing type' `T`.

/// Variable identifier used to declare names in lambda nodes
pub type Identifier = String;

/// A standard AST for lambda terms where consecutive lambda nodes can be combined
/// into a single abstraction node.
/// Type parameter:
/// ===============
/// `T` represents the 'name referencing` type used in variable nodes.
///    It could be just the variable name itself (referring to a free variable or a name declared in another lambda node)
///    or any other pointer encoding (e.g. DeBruijn index,...)
pub mod standard {

  pub type Var<T> = T;

  pub type Abs<T> = (Vec<super::Identifier>, Box<Term<T>>);

  pub type App<T> = (Box<Term<T>>, Box<Term<T>>);

  pub enum Term<T> {
      Var(Var<T>),
      App(App<T>),
      Abs(Abs<T>)
  }

  /// A lambda term AST type where variables are referenced by their string identifier
  pub type LambdaTerm = Term<super::Identifier>;

}


/// A AST where each level of the tree alternates between lambda nodes and variable/application nodes.
/// Think of it as taking the standard AST and merging all consecutive abstractions
/// and consecutive applications into single nodes.
///
/// AST nodes are reference counted (Rc<_>) to allow for node referencing
/// from other part of the program (e.g. in sequences of nodes).
///
/// Type parameter:
/// ===============
/// `T` represents the 'name referencing` type used in variable nodes.
///    It could be just the variable name itself (referring to a free variable or a name declared in another lambda node)
///    or any other pointer encoding (e.g. DeBruijn index,...)

pub mod alternating {
  use std::rc::Rc;

  #[derive(Clone)]
  pub struct Var<T> {
    pub name:T,
    pub arguments: Vec<Rc<Abs<T>>>
  }

  #[derive(Clone)]
  pub struct Abs<T> {
    pub bound_variables : Vec<super::Identifier>,
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
    Var( Rc<Var<T>> )
  }

  pub type Term<T> = Abs<T>;

  pub type LambdaTerm = Term<super::Identifier>;

}
