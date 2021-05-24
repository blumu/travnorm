/// Traversing lambda terms in Rust
/// William Blum, May 2021
///

use crate::traversal::TermBranching::{Abs, Var, App};
use crate::traversal::Generalized::{Structural, Ghost};

use crate::ast::{ alternating_rc as ast, Identifier };
use std::cmp;
use std::rc::Rc;

// if true then print additional logging
const VERBOSE :bool = false;

// if true print traversal after every single extension
const VERY_VERBOSE :bool = false;

////////// Justified sequences

/// Ghosts variable node
#[derive(Clone)]
pub struct GhostVarNode { }

/// Ghost abstraction node
#[derive(Clone)]
pub struct GhostAbsNode {
  /// List of bound variable names: always empty in a traversal prior to taking the core projection
  bound_variables : Vec<Identifier>
}

/// Generalizing the concept of node or occurrences.
/// Type `S` represents a 'structural' form
/// Type `G` represents a 'ghost' form
#[derive(Clone, Copy)]
pub enum Generalized<S, G> {
  Structural(S),
  Ghost(G)
}

/// A generalized lambda node is either
/// - a structural lambda node
/// - a ghost lambda  node
type GeneralizedAbsNode<T> = Generalized<Rc<ast::Abs<T>>, Rc<GhostAbsNode>>;


/// A justification pointer
#[derive(Clone, Copy)]
pub struct Pointer {
  /// distance from the justifier in the sequence
  distance : usize,
  /// and pointer's label
  label : isize
}

/// Node scope
/// Internal node: nodes hereditarily enabled by an @-node
/// External node: nodes hereditarily enabled by the tree root
#[derive(PartialEq, Eq)]
#[derive(Clone, Copy)]
enum Scope {
  Internal,
  External
}

/// A structure that store the scope of the underlying node
/// alongside the justification pointer.
///
/// This is used to cache the scope (external or internal) for efficiency reasons.
/// (The scope is recoverable from the hereditary occurrence justification in the sequence.)
#[derive(Clone, Copy)]
struct JustificationWithScope {
  /// Justification pointer.
  pointer : Pointer,
  /// the scope of the occurrence
  scope : Scope
}

/// An occurrence of a node of type N (without justification pointer)
#[derive(Clone)]
pub struct UnjustifiedOccurrence<N> {
   node : Rc<N>
}

/// An node occurrence with an associated justification pointer.
/// - For a lambda-node distinct from the root: points to its parent-node
/// - For an internal variable: point to the occurrence of the lambda-node in the P-view binding the variable.
#[derive(Clone)]
pub struct JustifiedOccurrence<N> {
  /// the occurring node from the term tree
  node : Rc<N>,
  /// justification pointer and scope
  j : JustificationWithScope
}

#[derive(Clone)]
pub struct MaybeJustifiedOccurrence<N> {
  /// the occurring node from the term tree
  node : Rc<N>,
  /// An optional justification pointer. None for an occurrence of an initial node.
  j : Option<JustificationWithScope>
}

/// A generalized occurrence of a variable node is either
/// - a justified occurrence of a structural variable node
/// - a justified occurrence of a ghost variable node
type VarOccurrence<T> = Generalized<JustifiedOccurrence<ast::Var<T>>, JustifiedOccurrence<GhostVarNode>>;

/// A generalized occurrence of an abstraction node is either
/// - a justified occurrence of a structural lambda node (or unjustified occurrence of the root lambda node)
/// - a justified occurrence of a ghost lambda node
type AbsOccurrence<T> = Generalized<MaybeJustifiedOccurrence<ast::Abs<T>>, JustifiedOccurrence<GhostAbsNode>>;

type AppOccurrence<T> = UnjustifiedOccurrence<ast::App<T>>;

/// Generic enum to help create types discriminating over the three possible lambda term node types
#[derive(Clone, Copy)]
pub enum TermBranching<V,L,A> {
  /// Variable
  Var(V),
  /// Lambda abstraction
  Abs(L),
  //// Application
  App(A)
}


/// Occurrence of a node in a justified sequence
type Occurrence<T> = TermBranching<VarOccurrence<T>, AbsOccurrence<T>, AppOccurrence<T>>;

/// A justified sequence of node occurrences
type JustSeq<T> = Vec<Occurrence<T>>;

enum Extension<T> {
    None,
    Single(Occurrence<T>),
    ChoiceOfLambdas(Vec<AbsOccurrence<T>>)
}


trait MayHavePointer {
   fn may_pointer(&self) -> Option<Pointer>;
}

trait HasPointer {
   fn pointer(&self) -> Pointer;
}

impl<S, G> HasPointer for Generalized<JustifiedOccurrence<S>, JustifiedOccurrence<G>> {
  fn pointer(&self) -> Pointer {
    match self {
      Generalized::Structural(jo) => jo.j.pointer,
      Generalized::Ghost(jo) => jo.j.pointer,
    }
  }
}

impl<S> MayHavePointer for JustifiedOccurrence<S> {
  fn may_pointer(&self) -> Option<Pointer> {
    Some(self.j.pointer)
  }
}

impl<S> MayHavePointer for MaybeJustifiedOccurrence<S> {
  fn may_pointer(&self) -> Option<Pointer> {
    self.j.map(|j| j.pointer)
  }
}


impl<S : MayHavePointer, G: MayHavePointer> MayHavePointer for Generalized<S, G> {
  fn may_pointer(&self) -> Option<Pointer> {
    match self {
      Structural(s) => s.may_pointer(),
      Ghost(g) => g.may_pointer(),
    }
  }
}

impl<V : MayHavePointer, L: MayHavePointer, A: MayHavePointer> MayHavePointer for TermBranching<V, L, A> {
  fn may_pointer(&self) -> Option<Pointer> {
    match self {
      Var(v) => v.may_pointer(),
      Abs(l) => l.may_pointer(),
      App(a) => a.may_pointer(),
    }
  }
}


trait HasScope {
   fn scope(&self) -> Scope;
}

impl<T> HasScope for JustifiedOccurrence<T> {
  fn scope(&self) -> Scope { self.j.scope }
}

impl<T> HasScope for MaybeJustifiedOccurrence<T> {
  fn scope(&self) -> Scope {
    match &self.j {
      None => Scope::External,
      Some(j) => j.scope
    }
  }
}

impl<T> HasScope for AppOccurrence<T> {
  fn scope(&self) -> Scope { Scope::Internal }
}

impl<X:HasScope,Y:HasScope> HasScope for Generalized<X,Y> {
  fn scope(&self) -> Scope {
    match self {
      Generalized::Structural(s) => s.scope(),
      Generalized::Ghost(s) => s.scope(),
    }
  }
}

impl<T> HasScope for Occurrence<T> {
  fn scope(&self) -> Scope {
    match &self {
      TermBranching::App(a) => a.scope(),
      TermBranching::Abs(a) => a.scope(),
      TermBranching::Var(v) => v.scope(),
    }
  }
}

/// State of a P-view iterator
pub struct PviewIteration<'a, T> {
  current_pos : i32,
  t: &'a JustSeq<T>,
}

/// Iterate backward over the P-view of a justified sequence
impl<'a, T: Clone> Iterator for PviewIteration<'a, T> {
  type Item = (Occurrence<T>, usize);

  fn next(&mut self) -> Option<(Occurrence<T>, usize)> {
    let i = self.current_pos;

    if i>=0 {
      let last_occurrence : &Occurrence<T> = &self.t[i as usize];
      let k =
        match last_occurrence {
          TermBranching::Var(_) | TermBranching::App(_)
            => 1,

          TermBranching::Abs(Generalized::Structural(o)) =>
            match &o.j {
              None => return None, // initial node => end of P-view
              Some(j) => j.pointer.distance,
            },

          TermBranching::Abs(Generalized::Ghost(g))
            => g.j.pointer.distance,

        };

      self.current_pos -= k as i32;

      Some ((last_occurrence.clone(), k))
    } else {
      None
    }
  }
}

/// Iterate over the P-view of a justified sequence.
///
/// Return the sequence of occurrence in the P-view (read backwards)
/// together with the position deltas between consecutive occurrences in the P-view
fn pview<'a, T>(t: &'a JustSeq<T>) -> PviewIteration<'a, T> {
  PviewIteration { current_pos : t.len() as i32 -1, t : t}
}

/// Trait used to define the arity of a node or an occurrence
trait HasArity {
   fn arity(&self) -> usize;
}

/// Arity of an AST Var node
impl<T> HasArity for ast::Var<T> {
  fn arity(&self) -> usize { self.arguments.len() }
}

/// Arity of an AST node
impl<T> HasArity for ast::Abs<T> {
  fn arity(&self) -> usize { self.bound_variables.len() }
}

/// Arity of an AST node
impl<T> HasArity for ast::App<T> {
  fn arity(&self) -> usize { self.operands.len() }
}

/// Arity of a ghost node
impl HasArity for GhostAbsNode {
  fn arity(&self) -> usize { 0 }
}

impl HasArity for GhostVarNode {
  fn arity(&self) -> usize { 0 }
}

/// Arity of a justified occurrence
impl<T:HasArity> HasArity for JustifiedOccurrence<T> {
  fn arity(&self) -> usize { self.node.arity() }
}

/// Arity of a justified occurrence
impl<T:HasArity> HasArity for UnjustifiedOccurrence<T> {
  fn arity(&self) -> usize { self.node.arity() }
}

/// Arity of an optionally justified occurrence
impl<T:HasArity> HasArity for MaybeJustifiedOccurrence<T> {
  fn arity(&self) -> usize { self.node.arity() }
}

/// Arity of the generalized type
impl<S:HasArity, G:HasArity> HasArity for Generalized<S, G> {
  fn arity(&self) -> usize {
     match self {
      Generalized::Ghost(g) => g.arity(),
      Generalized::Structural(s) => s.arity(),
    }
  }
}

impl<V:HasArity, L:HasArity, A:HasArity> HasArity for TermBranching<V, L, A> {
  fn arity(&self) -> usize {
    match self {
      TermBranching::Var(o) => o.arity(),
      TermBranching::App(o) => o.arity(),
      TermBranching::Abs(o) => o.arity(),
    }
  }
}

/// Dynamic arity of a traversal (ending with an external variable)
fn dynamic_arity<T>(t: &JustSeq<T>) -> usize {
  let mut i :i32 = t.len() as i32 - 1;
  let mut sum = t[i as usize].arity();
  let mut max = sum;
  i = i-1;
  while i >= 0 {
    let o = &t[i as usize];
    let arity = o.arity();
    match o {
      TermBranching::Abs(_) if o.scope() == Scope::External => return max,
      TermBranching::Abs(_) => sum -= arity,
      TermBranching::Var(_) | TermBranching::App(_) => {
          sum += arity;
          max = cmp::max(sum, max)
        }
    }
    i = i-1;
  };
  max
}

/// Ability to instantiate (possibly fictitious) children nodes
trait OnTheFlyChildren<ChildrenType> {
  fn get_or_create_child(&self, child_index: usize) -> ChildrenType;
}


impl<T> OnTheFlyChildren<GeneralizedAbsNode<T>> for VarOccurrence<T> {

  /// Create a generalized (i.e. possibly fictitious) child node of a variable node
  /// associated with the variable occurrence
  /// - `childIndex` the index of the child node to fetch, ranging from
  ///   1 to arity(x) for a variable-node,
  fn get_or_create_child(&self, child_index: usize) -> GeneralizedAbsNode<T> {
    match &self {
      Generalized::Structural(occ) if child_index <= occ.arity() =>
        Generalized::Structural(Rc::clone(&occ.node.arguments[child_index-1])),

      Generalized::Structural(_) |
      Generalized::Ghost(_) =>
        Generalized::Ghost (Rc::new(GhostAbsNode { bound_variables: Vec::new() })),
    }
  }
}


impl<T> OnTheFlyChildren<GeneralizedAbsNode<T>> for AppOccurrence<T> {
  /// Create a generalized (i.e. possibly fictitious) child node of an application node
  /// associated with the @-occurrence
  /// - `childIndex` the index of the child node to fetch, ranging from
  ///   0 to arity(x) for an @-node.///
  fn get_or_create_child(&self, child_index: usize) -> GeneralizedAbsNode<T> {
    if child_index == 0 {
      Generalized::Structural(Rc::clone(&self.node.operator))
    } else if child_index <= self.arity() {
      Generalized::Structural(Rc::clone(&self.node.operands[child_index-1]))
    } else {
      Generalized::Ghost (Rc::new(GhostAbsNode { bound_variables: Vec::new() }))
    }
  }
}

/// Create an occurrence of a child node of a given @/var node occurrence
/// Arguments
/// - `m` occurrence of the parent @ or variable node
/// - `child_index` child index defining the node to create an occurrence of
/// - `distance` distance from the created occurrence to the occurrence `m` in the underlying sequence
fn create_occurrence_of_child_of<O : OnTheFlyChildren<GeneralizedAbsNode<T>> + HasScope, T>(
  m: &O,
  child_index: usize,
  distance: usize
  )
  -> AbsOccurrence<T>
{
  match m.get_or_create_child(child_index) {
    Generalized::Structural(s) =>
      Structural(MaybeJustifiedOccurrence{
        node: Rc::clone(&s),
        j : Some(JustificationWithScope {
          pointer: Pointer { distance: distance, label: child_index as isize },
          scope: m.scope() // has same scope as parent node
        })
      })
    ,
    Generalized::Ghost(g) =>
      Ghost(
        JustifiedOccurrence {
        node: Rc::clone(&g),
        j : JustificationWithScope {
              pointer: Pointer { distance: distance, label: child_index as isize },
              scope: m.scope() // has same scope as parent node
            }
        }),
  }


}

////////// Traversals

/// To support traversals for an AST with variable name references of type T,
/// a function of the following type must be implemented.
///
/// When called, it must locate the binder to the specified variable (with binding reference of type T)
/// and return a justification pointer to the occurrence of the binder.
/// The P-view (which represents the path from the variable node to the tree root, see paper)
/// is provided as an iterable argument that enumerates backwards the occurrence in the P-view.
pub trait BinderLocator<Name> {

  fn locate<'a> (
    reference_to_variable_name : &Name,
    pview: PviewIteration<'a, Name>,
    free_variable_indices: &mut Vec<Identifier>) -> Pointer;

}

/// lookup the index assigned to a free variable, or create one if it is not defined yet
fn lookup_or_create_free_variable_index(
  free_variable_indices: &mut Vec<Identifier>,
  variable_name: &Identifier) -> usize {

  match free_variable_indices.iter().position(|v| v == variable_name) {
    None => {
      free_variable_indices.push(variable_name.clone());

      1 + free_variable_indices.len()
    },

    Some(j) => // create a fresh free variable name
      j + 1
  }
}

//Identifier_find_binder
impl BinderLocator<Identifier> for Identifier {

  /// Implement 'find_binder' for AST where the variable name references
  /// are encoded as simple name identifiers (string)
  ///
  /// With identifier names, the binder is the first lambda node
  /// in the P-view binding that particular variable name.
  /// If no such occurrence exists then it's a free variable
  /// (justified by the tree root--the initial node occurrence in the P-view)
  fn locate<'a> (
    variable_name:&Identifier,
    pview: PviewIteration<'a, Identifier>,
    free_variable_indices: &mut Vec<Identifier>
  ) -> Pointer {
    // read the P-view backward and stop at the first binder containing the variable name
    let mut d = 1;
    for (b, _) in pview {
      match b {
        TermBranching::Abs(Generalized::Structural(a)) => {
          match a.node.bound_variables.iter().position(|v| v == variable_name) {
            Some(i) =>
              return Pointer { distance: d, label: i as isize +1 },
            None => {
                let inc = match a.j {
                  None => 0,
                  Some(j) => j.pointer.distance
                };

                d += inc;
            }
          }
        },

        TermBranching::Abs(Generalized::Ghost(_)) =>
          panic!("find_binder expects structural nodes only"),

        _ => d += 1
      }
    }
    // no binder found: it's a free variable
    return Pointer {
      distance: d,
      label: lookup_or_create_free_variable_index(free_variable_indices, variable_name) as isize }
  }
}


/// Get the list of possible occurrences opening up a new strand
/// in a strand-complete traversal
/// (empty if the traversal is maximal)
fn new_strand_opening_occurrences<T>(
  t: &JustSeq<T>,
  last_occurrence: &VarOccurrence<T>
) -> Vec<AbsOccurrence<T>> {
  let da = dynamic_arity(t);
  let range = 1..(da+1);
  let possible_children : Vec<AbsOccurrence<_>> =
      range
      .map(move |i| create_occurrence_of_child_of(last_occurrence, i, 1))
      .collect();
  possible_children
}

/// Extend a traversal by one more node occurrence.
///
/// The extension follows the traversal rules of the 'normalizing traversals' from the paper
/// The input traversal is not modified, instead it returns the list of possibles node occurrences
/// to traverse, or just void if the traversal is maximal
///
/// Arguments:
///   - `t` the current traversal
///   - `tree_root` the root of the term tree
///   - `free_variable_indices` vector with names of newly created free variables
fn extend_traversal<T : Clone + BinderLocator<T>>(
  tree_root: &ast::Abs<T>,
  t: &JustSeq<T>,
  free_variable_indices: &mut Vec<Identifier>
) -> Extension<T>
{
  if t.is_empty() { // Empty sequence?
    Extension::Single(Abs(
        Generalized::Structural(
          MaybeJustifiedOccurrence {
            node: Rc::new(tree_root.clone()),
            j : None,
          })))
  } else {
    let next_index = t.len();
    let last_index = next_index-1;
    let last_occurrence :&Occurrence<T> = &t[last_index];
    match last_occurrence {
      App(app) =>

        Extension::Single(Abs(
            Generalized::Structural(
              MaybeJustifiedOccurrence {
                node: app.node.operator.clone(), // traverse the operator node
                j : Some(JustificationWithScope {
                  pointer : Pointer { distance:1, label: 0 },
                  scope: Scope::Internal
                })
              }
          ))),

      Var(var) if last_occurrence.scope() == Scope::Internal => {
          // (Var) copy-cat rule
          let just = &var.pointer();
          let child_index = just.label as usize;
          let distance = 2 + just.distance;

          // Occurrence `m` from the paper, is the node preceding the variable occurrence's justifier.
          // Type assertion: by construction traversal verify alternation therefore m is necessarily a variable occurrence
          let m = &t[next_index - distance];

          let jo = match m {
            TermBranching::App(m_a) => { create_occurrence_of_child_of(m_a, child_index, distance) },
            TermBranching::Var(m_v) => { create_occurrence_of_child_of(m_v, child_index, distance) },
            TermBranching::Abs(_) => panic!("Impossible: a variable's justifier predecessor cannot be an abstraction node occurrence."),
          };

          Extension::Single(Abs(jo))
      }

      Var(v) => { // external variable
          let possible_children = new_strand_opening_occurrences(t, v);
          if possible_children.is_empty() {
            Extension::None
          } else {
            Extension::ChoiceOfLambdas(possible_children)
          }
      }

      Abs(Generalized::Structural(abs_node)) => {
          let body_node = &abs_node.node.body;
          // traverse the body of the lambda
          match &body_node {
            ast::AppOrVar::App(body_app) =>
              Extension::Single(App(UnjustifiedOccurrence {
                    node: Rc::clone(body_app),
                  })),

            ast::AppOrVar::Var(body_var) => {
              let p = pview(t);
              let n = &body_var.name;
              let pointer = T::locate(n, p, free_variable_indices);

              let m = &t[next_index - pointer.distance]; // if d= 1 then the justifier is the last occurrence

              Extension::Single(Var(Generalized::Structural(
                JustifiedOccurrence {
                    node: Rc::clone(body_var),
                    j : JustificationWithScope {
                        scope: m.scope(),
                        pointer: Pointer {
                          distance: pointer.distance,
                          label: pointer.label
                    },
                  }})))
            }
        }
      },

      Abs(Generalized::Ghost(g)) => {
        // Traverse the child of the ghost lambda node
        let d = g.j.pointer.distance;
        let m = &t[last_index-d];

        let justifier_distance = d + 2;
        let mu = &t[next_index - justifier_distance];
        let i = g.j.pointer.label;
        if VERY_VERBOSE { println!("[GhostAbs-arity] m: {}, mu: {}, i: {}", m.arity(), mu.arity(), i); };
        Extension::Single(Var(
            Generalized::Ghost(
              JustifiedOccurrence {
                node: Rc::new(GhostVarNode{}),
                j : JustificationWithScope {
                  pointer : Pointer { distance: justifier_distance,
                                        label: mu.arity() as isize + i - m.arity() as isize },
                  scope: mu.scope()
                }
              }
            )
          )
        )
      }
    }
  }
}


fn format_pointer(p: &Pointer) -> String {
  format!("({},{})", p.distance, p.label)
}

fn as_string_list<T:ToString>(v:&Vec<T>) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

/// Format a node occurrence to string.
///
/// Arguments:
///  - `t`: sequence of occurrences in which the occurrence to be formatted appears
///  - `index`: position of the occurrence in the sequence t
///  - `free_variable_indices`: the free variable name-index map
fn format_occurrence<T : ToString>(
   t: &JustSeq<T>,
   index: usize,
   free_variable_indices: &[Identifier])
-> String
{
  let o = &t[index];
  match o {
    TermBranching::Abs(Generalized::Structural(MaybeJustifiedOccurrence{ j : None, node })) =>
      format!("[{}]",as_string_list(&node.bound_variables).join(" ")),

    TermBranching::Abs(Generalized::Structural(MaybeJustifiedOccurrence{ j : Some(j), node })) =>
      format!("[{}]{}", as_string_list(&node.bound_variables).join(" "), format_pointer(&j.pointer)),

    TermBranching::Abs(Generalized::Ghost(jo)) =>
      format!("$[{:?}]{:?}", jo.node.bound_variables, format_pointer(&jo.j.pointer)),

    TermBranching::Var(Generalized::Structural(v)) =>
    {
      let pointer = &v.j.pointer;

      let justifier = &t[index as usize - pointer.distance];
      match justifier {
        App(_) | Var(_) => panic!("A variable's justifier can only be an occurrence of a lambda node."),

        Abs(Generalized::Ghost(_)) => panic!("A structural variable can only be justified by a structural lambda node."),

        Abs(Generalized::Structural(jo)) => {
          let justifier_bound_variables = &jo.node.bound_variables;
          let l = pointer.label as usize;
          let name =
            if l <= justifier_bound_variables.len() {
              justifier_bound_variables[l - 1].to_string()
            } else {
              free_variable_indices[(l - 1 - justifier_bound_variables.len()) as usize].clone()
            };
          name + &format_pointer(pointer)
        }
      }
    },

    TermBranching::App(_) => "@".to_owned(),

    TermBranching::Var(Generalized::Ghost(g)) => format!("#{}", format_pointer(&g.j.pointer))
  }
}

fn format_sequence<T: ToString>(
    t: &JustSeq<T>,
    free_variable_indices:&Vec<Identifier>) -> String
{
  let occ : Vec<String>=
    t.iter()
     .enumerate()
     .map(|(i, _)| format_occurrence(t, i, free_variable_indices))
     .collect();

  occ.join("--")
}

/// State of the core projection iteration
struct CoreProjection<'a, T> {
  /// The input traversal
  t: &'a JustSeq<T>,
  /// List of pending lambdas at this point
  pending_lambdas: Vec<Identifier>,
  /// Position of the current node occurrence in the input traversal
  position : usize
}

/// Iterate over the core projection of a traversal
impl<'a, T : Clone> Iterator for CoreProjection<'a, T> {
  type Item = Occurrence<T>;

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      if self.position == 0 {
        return None
      }

      self.position -= 1;
      let i = self.position;
      let o = &self.t[i];
      match o {
        Abs(o_a) if o_a.scope() == Scope::External => {

          let clone_occurrence = match o_a {
            Generalized::Ghost(g) => {
                Generalized::Ghost(
                  JustifiedOccurrence{
                      j : g.j,
                      node : Rc::new(GhostAbsNode{
                          // unload the pending lambdas onto the node occurrence
                          bound_variables : [ &g.node.bound_variables[..], &self.pending_lambdas[..]].concat(),
                        }),
                      })
            },
            Generalized::Structural(s) => {
                Generalized::Structural(
                  MaybeJustifiedOccurrence{
                      j : s.j,
                      node : Rc::new(ast::Abs{
                        // unload the pending lambdas onto the node occurrence
                        bound_variables : [ &s.node.bound_variables[..], &self.pending_lambdas[..]].concat(),
                        body : s.node.body.clone()
                      })
                  })
            }
          };

          self.pending_lambdas.truncate(0);

          return Some(Abs(clone_occurrence))
        },

        Abs(Generalized::Structural(a)) => {
          self.pending_lambdas = [ &a.node.bound_variables[..], &self.pending_lambdas[..]].concat();
        },

        Abs(Generalized::Ghost(a)) => {
          self.pending_lambdas = [ &a.node.bound_variables[..], &self.pending_lambdas[..]].concat();
        },

        Var(v) if v.scope() == Scope::External => {
          // patch link distance to account for the removed occurrences (underneath the pointer)
          let mut d = v.pointer().distance;
          for j in (i-d)..i {
            if self.t[j].scope() == Scope::Internal {
              d -= 1
            }
          }

          let cloned_occurrence = match v {
            Structural(s) => {
              Structural(
                JustifiedOccurrence {
                    j : JustificationWithScope {
                      pointer: Pointer { distance: d, label: s.j.pointer.label },
                      scope: s.j.scope
                    },
                  node : Rc::clone(&s.node)
                })
            },
            Ghost(g) => {
              Ghost(
                JustifiedOccurrence {
                    j : JustificationWithScope {
                      pointer: Pointer { distance: d, label: g.j.pointer.label },
                      scope: g.j.scope
                    },
                  node : g.node.clone()
                })
            }
          };

          self.pending_lambdas.truncate(0);

          return Some (Var(cloned_occurrence))
        },

        Var(_) | App(_) => {
          // pop arity(o) elements from the left of the array
          let (_, right) = self.pending_lambdas.split_at(o.arity());
          self.pending_lambdas = right.to_vec();
        }
      }
    }
  }
}

/// Return an iterator over the core projection of a traversal
fn core_projection<T>(t: &JustSeq<T>) -> CoreProjection<T> {
  CoreProjection {
    pending_lambdas : Vec::new(),
    t : t,
    position : t.len() // start calculating from the right
  }
}

/// Traverse the next strand of a term from a given traversal.
///
/// Arguments:
///   - `t` the current traversal
///   - `tree_root` the root of the term tree
///   - `free_variable_indices` the indices of all free variables
/// Returns an array of all possible next strands, or an empty vector
/// if the input traversal is complete
fn traverse_next_strand<T : Clone + ToString + BinderLocator<T>>(
  tree_root:&ast::Abs<T>,
  t:&mut JustSeq<T>,
  free_variable_indices: &mut Vec<String>
) -> Extension<T>
 {

  let mut next = extend_traversal(tree_root, t, free_variable_indices);

  while let Extension::Single(o) = next {
    t.push(o); // append the traversed occurrence
    if VERY_VERBOSE {
      println!("extended: {}", format_sequence(t, free_variable_indices))
    }
    next = extend_traversal(tree_root, t, free_variable_indices)
  }

  next
}

fn enumerate_all_traversals<T: Clone + ToString + BinderLocator<T>>(
  tree_root: &ast::Abs<T>,
  t: &mut JustSeq<T>,
  free_variable_indices: &mut Vec<Identifier>,
  depth:usize
) {

  let log_indent = "  ".repeat(depth);

  match traverse_next_strand(tree_root, t, free_variable_indices) {
    Extension::None => {
      println!("{}|Depth:{}|Maximal traversal:{}",
          log_indent,
          depth,
          format_sequence(t, free_variable_indices));

      let mut p : Vec<Occurrence<T>> = core_projection(t).collect();
      p.reverse();

      println!("{}|      {}        projection:{}",
          log_indent,
          " ".repeat(depth.to_string().len()),
          format_sequence(&p, free_variable_indices));
    },

    // traversing the root node, or the single child lambda node of an external variable node
    Extension::Single(o) => {
      if VERBOSE { println!("{}|Depth:{}|External variable reached with single choice: {}",
        log_indent,
        depth,
        format_sequence(t, free_variable_indices)) };

      let mut t2: JustSeq<T> = t.clone();
      let before_length = t2.len();
      t2.push(o);

      if VERBOSE { println!("{}|Depth:{}|Traversal: {}|Occurrence: {}",
        log_indent, depth,
        format_sequence(t, free_variable_indices),
        format_occurrence(&t2, t.len(), free_variable_indices)) };

      enumerate_all_traversals(tree_root, &mut t2, free_variable_indices, depth+1);

      t2.truncate(before_length)

    },

    // previous occurrence is an external variable with multiple non-deterministic choices
    // of children lambda nodes for the next occurrence
    Extension::ChoiceOfLambdas(node_occurrence_choices) => {
      if VERBOSE { println!("{}|Depth:{}|External variable reached with {} branch(es): {}",
        log_indent,
        depth,
        node_occurrence_choices.len(),
        format_sequence(t, free_variable_indices)) };

      for o in node_occurrence_choices {
        let mut t2: JustSeq<T> = t.clone();
        let before_length = t2.len();

        let label = o.may_pointer().unwrap().label;
        t2.push(Abs(o));
        if VERBOSE { println!("{}|Depth:{}|Choice:{}|Traversal: {}|Occurrence: {}",
          log_indent, depth,
          label, // node_occurrence_choices all have a pointer
          format_sequence(t, free_variable_indices),
          format_occurrence(&t2, t.len(), free_variable_indices));
        enumerate_all_traversals(tree_root, &mut t2, free_variable_indices, depth+1);
        t2.truncate(before_length);
       }
      }
    }
  };

}


/// A binder declare a list of bound identifiers
type Binder = Vec<Identifier>;

/// To support pretty-printing of lambda terms AST, the type T must implement name lookup
pub trait NameLookup {
  // Given a list of binders occurring in the path from the root
  // to the variable node, return the name of the variable.
  //
  // If the variable is free then the map 'free_variable_indices' can be used to lookup a
  // free variable name from its 'free variable index'.
  fn lookup(
    &self,
    binders_from_root: &[Binder],
    free_variable_indices: &[Identifier], // read-only
    with_encoding: bool // if true then pretty-print the variable name encoding itself as well as the variable name
  )-> String;
}


impl NameLookup for String {
  fn lookup(
    &self,
    _: &[Binder],
    _: &[Identifier],
    _: bool
  ) -> String {
    // The name of the variable occurrence is just name identifier itself!
    self.to_owned()
  }
}




mod pretty_print {
  use crate::ast::{ alternating_rc as ast, Identifier };

  use super::NameLookup;

  /// Pretty-printing helper type
  struct Pretty {
    pretty_printed: String,
    must_bracket_if_argument: bool
  }

  fn bracketize(t: Pretty) -> String {
    if t.must_bracket_if_argument { format!("({})", t.pretty_printed) } else { t.pretty_printed }
  }

  /// Arguments
  /// =========
  /// `root` Root of the lambda term AST
  /// `with_encoding` if true print variable name reference encoding in addition to resolved names
  /// `free_variable_indices` array that can optionally be used by the variable lookup function to
  /// assign an index to free variables.
  /// This is used for instance, when T is the deBruijn encoding. If `T` is String it's not used.
  pub fn format_lambda_term<T : Clone + NameLookup>(
      root: &ast::Term<T>,
      free_variable_indices: &Vec<Identifier>,
      with_encoding: bool
    ) -> String {
    format_abs(root, free_variable_indices, with_encoding, &mut Vec::new()).pretty_printed
  }

  fn format_var<T : Clone + NameLookup>(
    var: &ast::Var<T>,
    free_variable_indices: &Vec<Identifier>,
    with_encoding: bool,
    binders_from_root: &mut Vec<Vec<String>>
  ) -> Pretty {
    let mut p : String = var.name.lookup(&binders_from_root[..], free_variable_indices, with_encoding).to_owned();

    if !var.arguments.is_empty() {
      p.push_str(" ");
      p.push_str(&mut var.arguments
                    .iter()
                    .map(|x| bracketize(format_abs(x, free_variable_indices, with_encoding, binders_from_root)))
                    .collect::<Vec<String>>()
                    .join(" "));
    }

    Pretty {
      pretty_printed: p,
      must_bracket_if_argument: var.arguments.len() > 0
    }
  }

  fn format_app<T : Clone + NameLookup>(
    app: &ast::App<T>,
    free_variable_indices: &Vec<Identifier>,
    with_encoding: bool,
    binders_from_root: &mut Vec<Vec<String>>
  ) -> Pretty {
      Pretty {
          pretty_printed:
              bracketize(format_abs(&*app.operator, free_variable_indices, with_encoding, binders_from_root))
            + &app.operands
                    .iter()
                    .map(|x| bracketize(format_abs(x, free_variable_indices, with_encoding, binders_from_root)))
                    .collect::<Vec<String>>()
                    .join(" "),
          must_bracket_if_argument: true
      }
  }

  fn format_app_or_var<T : Clone + NameLookup>(
    term: &ast::AppOrVar<T>,
    free_variable_indices: &Vec<Identifier>,
    with_encoding: bool,
    binders_from_root: &mut Vec<Vec<String>>
  ) -> Pretty {
    match term {
      ast::AppOrVar::Var(v) => format_var(v, free_variable_indices,with_encoding,  binders_from_root),
      ast::AppOrVar::App(a) => format_app(a, free_variable_indices, with_encoding, binders_from_root),
    }
  }

  fn format_abs<T : NameLookup + Clone>(
    abs_term: &ast::Abs<T>,
    free_variable_indices: &Vec<Identifier>,
    with_encoding: bool,
    binders_from_root: &mut Vec<Vec<String>>
  ) -> Pretty {

    let binders_count = binders_from_root.len();
    binders_from_root.append(&mut  vec![abs_term.bound_variables.clone()]);

    let body_print = format_app_or_var(&abs_term.body, free_variable_indices, with_encoding, binders_from_root);

    binders_from_root.truncate(binders_count);

    if abs_term.bound_variables.is_empty() {
      Pretty {
        pretty_printed: body_print.pretty_printed,
        must_bracket_if_argument: body_print.must_bracket_if_argument
      }
    } else {
      Pretty {
        pretty_printed: format!(r"\lambda {}.{}", abs_term.bound_variables.join(" "), body_print.pretty_printed),
        must_bracket_if_argument: true
      }
    }
  }

}

/// Enumerate all the traversals of a lambda term term
pub fn evaluate<T : Clone + ToString + NameLookup + BinderLocator<T>>(
  term: &ast::Term<T>
) {
  println!("Traversing {}", pretty_print::format_lambda_term(term, &Vec::new(), false));
  enumerate_all_traversals(term, &mut Vec::new(), &mut Vec::new(), 0)
}

/// A deBruijn-like encoding where the name of a variable occurrence
/// is defined by a pair of integers referencing to the lambda-binder
/// and the index of the name in the lambda-binder
#[derive(Clone)]
struct DeBruijnPair {
  // Depth is the distance from the variable node to its binder node in the path to the tree root
  // (1 for the parent node, and so on)
  depth: usize,
  // Index of the variable name in the lambda-binder
  index: isize
}

impl NameLookup for DeBruijnPair {

    fn lookup(&self,
              binders_from_root: &[Binder],
              free_variable_indices: &[Identifier],
              with_encoding: bool) -> String
    {
      let binder_index = binders_from_root.len() - (self.depth + 1) / 2;
      let binder_bound_variables = &binders_from_root[binder_index];
      let root_bound_variables = &binders_from_root[0];
      let is_bound_by_root = binder_index == 0;
      let free_variable_index = self.index - root_bound_variables.len() as isize - 1;

      let ghost_naming = format!("#({},{})", self.depth, self.index);

      let variable_name =
        if is_bound_by_root && free_variable_index >= 0 {
          &free_variable_indices[free_variable_index as usize]
        } else {
          if self.index as usize > binder_bound_variables.len() {
            // unresolved ghost variable name (should never happen on core-projected traversals)
            &ghost_naming
          } else {
            &binder_bound_variables[self.index as usize - 1]
          }
        };

      // If with_encoding is true then append the deBruijn pair encoding to the variable name
      if with_encoding {
        format!("{}({},{})", variable_name, self.depth, self.index)
      } else {
        variable_name.to_owned()
      }
    }
}



/// Read out the subterm whose root node is the last occurrence of traversal t
/// by recursively extending the traversal strands.
///
/// Arguments:
/// ----------
/// - `t`: a strand-complete traversal
/// - `free_variable_indices` free variable name to index table
/// - `depth` node depth of the last node in the traversal
fn readout<T : Clone + ToString + BinderLocator<T>>(
    root:&ast::Term<T>,
    mut t: &mut JustSeq<T>,
    free_variable_indices: &mut Vec<Identifier>,
    depth: u32
) -> ast::Abs<DeBruijnPair> {

  traverse_next_strand(root, &mut t, free_variable_indices);

  // get the last two nodes from the core projection
  let mut p = core_projection(t);

  // The strand ends with an external variable, call it x
  if let Some(Var(strand_end_var)) = p.next() {
    // The strand starts with an external lambda, call it \lambda y1 .... y_n
    if let Some(Abs(strand_begin_abs)) = p.next(){
      let argument_occurrences = new_strand_opening_occurrences(t, &strand_end_var);

      if VERBOSE {
        if argument_occurrences.is_empty() {
          print!("Strand ended|Maximal    |Depth:{}|Traversal: {}", depth, format_sequence(t, free_variable_indices))
        } else {
          print!("Strand ended|Not maximal|Depth:{}|Traversal: {}", depth, format_sequence(t, free_variable_indices))
        }
      }

      let length_before = t.len();

      ast::Abs {
        bound_variables: match strand_begin_abs {
          Structural(a) => { a.node.bound_variables.clone() },
          Ghost(a) => { a.node.bound_variables.clone() }
        },
        body: ast::AppOrVar::Var(Rc::new(ast::Var{
            // Since the core projection of the traversal is the path to the root (see paper),
            // the depth of the variable is precisely the distance to the justifying node in the core projection.
            name: DeBruijnPair {
              depth: strand_end_var.pointer().distance,
              index: strand_end_var.pointer().label
            },
            arguments: argument_occurrences
                        .iter()
                        .map(|o| {
                                  t.push(Abs(o.clone()));
                                  let r = readout(root, t, free_variable_indices, depth+1);
                                  t.truncate(length_before);
                                  Rc::new(r)
                        })
                        .collect::<Vec<Rc<ast::Abs<DeBruijnPair>>>>()
          }))
        }
    } else {
      panic!("Invalid strand: it should end with an abstraction node.")
    }
  } else {
    panic!("Invalid strand: it should start with a variable node.")
  }

}

/// Evaluate and readout the __name-free__ (deBruijn pairs-based)
/// normal-form of a lambda term.
///
/// This 'read-out' implementation produces an AST with DeBruijn variable references rather than string identifiers.
/// Note therefore, that variable name collision may occur at pretty-printing time if just displaying the variable name
/// without the associated deBruijn pairs.
fn evaluate_and_name_free_readout<T : Clone + ToString + NameLookup + BinderLocator<T>>(
  root:&ast::Term<T>,
  free_variable_indices: &mut Vec<Identifier>
) -> ast::Abs<DeBruijnPair>
{
  println!("Evaluating {}", pretty_print::format_lambda_term(root, free_variable_indices, false));
  readout(root, &mut Vec::new(), free_variable_indices, 0)
}

pub fn evaluate_and_print_normal_form(term: &ast::Term<Identifier>) {
  let mut free_variable_indices : Vec<String> = Vec::new();
  let readout = evaluate_and_name_free_readout::<Identifier>(term, &mut free_variable_indices);
  println!("{}", pretty_print::format_lambda_term::<DeBruijnPair>(&readout, &free_variable_indices, false))
}



/// Binder locator for variable references encoded with DeBruijn pairs.
///
/// Suppose the variable reference is encoded by the DeBruijn pair (b, d) then
/// the variable binder is located in the P-view at the index b starting from the end,
/// while `d` gives the index of the bound variable name.
///
/// Hence, to return the pointer to the binder, this function just walks the P-view backwards
/// for a number of steps given by the first DeBruijn index.
///
impl BinderLocator<DeBruijnPair> for DeBruijnPair {

  fn locate<'a> (
    variable_reference:&DeBruijnPair,
    pview: PviewIteration<'a, DeBruijnPair>,
    _: &mut Vec<Identifier>
  ) -> Pointer {
    let mut enabler_depth = variable_reference.depth;
    let mut distance = 1;
    for (_, d) in pview {
      enabler_depth -= 1;
      if enabler_depth <= 0 {
        break;
      };
      distance += d
    }
    return Pointer { distance: distance, label: variable_reference.index }
  }
}

/// Create a new variable starting with a specified prefix
/// that is fresh according to a given freshness checking function `is_name_clashing`.
fn create_fresh_variable(
    prefix:&str,
    is_name_clashing: &dyn Fn(&Identifier) -> bool) -> String
{
  let mut candidate = prefix.to_owned();
  let mut attempts = 1;
  while is_name_clashing(&candidate) {
    candidate = format!("{}{}", prefix, attempts);
    attempts += 1;
  }
  candidate
}


/*

///////// Name resolution with anti-collision

/// Name-preserving conversion of a deBruijn-based AST into an identifier-based AST.
///
/// Attempt to resolve the naming suggestions assigned by the lambda nodes labels
/// when possible. If causing conflicts, the suggested names might be replaced by
/// fresh names.
///
/// This function implements the *name-preserving* read-out algorithm from the paper,
/// that preserves original variable name when possible.
fn resolveNameAmbiguity (
  binderNode:Abs<DeBruijnPair>,
  free_variable_indices:[Identifier],
  // The list of binders from the root to the last node of t
  // this array gets mutated as bound variable names get renamed to avoid name collision
  // when replacing DeBruijn pairs by variable names.
  binders_from_root: (Abs<DeBruijnPair>| GhostAbsNode)[] //= []
  ) -> Abs<Identifier>
{
  let getBindingIndex = (node: Abs<DeBruijnPair> | GhostAbsNode, variableName: Identifier) => node.bound_variables.indexOf(variableName)
  let isBoundByAbsNode = (node: Abs<DeBruijnPair> | GhostAbsNode, variableName: Identifier) => getBindingIndex(node, variableName) >= 0

  fn nameAlreadyUsedAbove (suggestedName:Identifier, binderNameIndex:number) {
    let freeVariableWithSameName = free_variable_indices.indexOf(suggestedName)>=0

    let upperBinderNodesLookup = binders_from_root.findIndex(binder=> isBoundByAbsNode(binder, suggestedName))
    let nameUsedInStrictUpperBinderNodes = upperBinderNodesLookup >= 0 && upperBinderNodesLookup < binders_from_root.length-1

    let sameBinderNodeLookup = binderNode.bound_variables.indexOf(suggestedName)
    let nameUsedInSameBinderNode = sameBinderNodeLookup >= 0 && sameBinderNodeLookup < binderNameIndex

    return freeVariableWithSameName || nameUsedInStrictUpperBinderNodes || nameUsedInSameBinderNode
  }

  /// Assign permanent bound variable name to the lambda node, one at a time
  binders_from_root.push(binderNode)
  for(let b = 0; b<binderNode.bound_variables.length; b++) {
    let suggestedName = binderNode.bound_variables[b]
    let potentialConflict = nameAlreadyUsedAbove(suggestedName, b)
    if(potentialConflict) {
      // Is there an actual conflict? I.e. is there a variable occurring below
      // the current node in the term tree, whose deBruijn index refers to an upper binding
      // with the same name?
      function hasNamingConflict(
        node:App<DeBruijnPair>|Var<DeBruijnPair>|Abs<DeBruijnPair>,
        depthNotToCross:number
      ) : boolean {
        if(node.kind == "Abs") {
          return hasNamingConflict(node.body, depthNotToCross+1)
        } else if(node.kind == "App") {
          return hasNamingConflict(node.operator, depthNotToCross+1)
          || node.operands.findIndex(o=>hasNamingConflict(o, depthNotToCross+1)) >= 0
        } else { //if (node.kind == "Var")
          // +1 because variable name in lambda-binders start at index 1
          let currentIndexInCurrentBinderNode = b + 1
          let overArcingBinding =
            node.name.depth > depthNotToCross
            || (node.name.depth == depthNotToCross
                && node.name.index<currentIndexInCurrentBinderNode)

          if(overArcingBinding) {
            // We found a variable node with over-arcing binding (i.e. binding lambda occurring above binder 'b')
            // we now lookup it's assigned name to check if there is a name conflict
            let adjustedDeBruijn = new DeBruijnPair(node.name.depth - depthNotToCross + 1, node.name.index)
            let overArcingVariableAssignedName = adjustedDeBruijn.lookupBinderAndName(binders_from_root, free_variable_indices).name

            return (suggestedName == overArcingVariableAssignedName)
                    || node.arguments.findIndex(o=>hasNamingConflict(o, depthNotToCross+1)) >= 0
          } else {
            return node.arguments.findIndex(o=>hasNamingConflict(o, depthNotToCross+1)) >= 0
          }
        }
      }
      if(hasNamingConflict(binderNode.body, 1)) {
        // resolve the conflict by renaming the bound lambda
        let primedVariableName = binderNode.bound_variables[b]+'\''
        binderNode.bound_variables[b] = create_fresh_variable(primedVariableName, suggestion => nameAlreadyUsedAbove(suggestion, b))
      } else {
        // no  conflict with this suggested name: we make it the permanent name.
      }
    } else {
      // no potential conflict with this suggested name: we make it the permanent name.
    }
  }

  let bodyWithVariableNamesAssigned : App<Identifier> | Var<Identifier>
  if(binderNode.body.kind == "App") {
    bodyWithVariableNamesAssigned = {
        kind: "App",
        operator: resolveNameAmbiguity(binderNode.body.operator, free_variable_indices, binders_from_root),
        operands: binderNode.body.operands.map(a => resolveNameAmbiguity(a, free_variable_indices, binders_from_root))
    }
  } else { // if(root.body.kind == "Var") {
    let assignedVariableName = binderNode.body.name.lookupBinderAndName(binders_from_root, free_variable_indices).name
    bodyWithVariableNamesAssigned = {
      kind: "Var",
      name: assignedVariableName,
      arguments: binderNode.body.arguments.map(a => resolveNameAmbiguity(a, free_variable_indices, binders_from_root))
    }
  }
  binders_from_root.pop()
  return {
    kind: "Abs",
    bound_variables: binderNode.bound_variables,
    body:bodyWithVariableNamesAssigned
  }
}

fn evaluate_resolve_print_normal_form(term: Abs<Identifier>) {
  let [readout, free_variable_indices] = evaluate_and_name_free_readout(Identifier_find_binder, term, []);
  let resolvedNameReadout = resolveNameAmbiguity(readout, free_variable_indices, []);
  console.log(format_lambda_term(resolvedNameReadout, false, free_variable_indices).pretty_printed)
}



*/



/*
namespace DeBruijnConversion{
  /// if true then print additional logging
  export let verbose = false
}

function findLastIndex<T>(a: T[], condition: (element: T, index: number) => boolean): undefined | [number, T] {
  for (var i = a.length - 1; i >= 0; i--) {
    let e = a[i]
    if (condition(e, i)) {
      return [i, e]
    }
  }
  return undefined
}

/// Convert an AST of type Abs<Identifier> to an AST of type Abs<DeBruijnPair>
/// NOTE: This is not actually needed in the implementation of the traversal-based normalization procedure
/// it's used for debugging purpose only.
function toDeBruijnAST(
  /// the node of the alternating AST to convert
  node: Abs<Identifier>,
  /// the list of binder nodes from the root
  binders_from_root: Abs<Identifier>[],
  /// map that assigns an index to every free variable seen so far
  free_variable_indices:[Identifier]
): Abs<DeBruijnPair>
{
  var new_binders_from_root = binders_from_root.concat([node])
  let VarOrApp_Node = () : Var<DeBruijnPair> | App<DeBruijnPair> =>
    {
      let bodyNode = node.body
      switch (bodyNode.kind) {
      case "Var":
        let variableName = bodyNode.name
        /// find the variable binder
        let binderLookup = findLastIndex(new_binders_from_root, b => b.boundVariables.indexOf(variableName) >= 0)

        var binder : DeBruijnPair
        if (binderLookup !== undefined) {
          let [binder_index, b] = binderLookup
          let binderDistance = new_binders_from_root.length - binder_index
          binder = new DeBruijnPair(2 * binderDistance - 1, b.boundVariables.indexOf(variableName) + 1)
          DeBruijnConversion.verbose && console.log('binders_from_root:' + new_binders_from_root.map(x => '[' + x.boundVariables.join(' - ') + ']').join('\\') + ' varName:' + variableName + ' binder_index:' + binder_index + ' depth:' + binder.depth + ' binderVarNames:' + b.boundVariables.join('-'))
        }
        // no binder -> x is a free variable and its enabler is the root
        else {
          let j = lookupOrCreatefree_variable_index(free_variable_indices, variableName)
          let root = new_binders_from_root[0]
          binder = new DeBruijnPair(2 * new_binders_from_root.length - 1, root.boundVariables.length + j)
        }
        return {
          kind: "Var",
          name: binder,
          arguments: bodyNode.arguments.map(o => toDeBruijnAST(o, new_binders_from_root, free_variable_indices))
        }
      case "App":
        return {
          kind: "App",
          operator: toDeBruijnAST(bodyNode.operator, new_binders_from_root, free_variable_indices),
          operands: bodyNode.operands.map(o => toDeBruijnAST(o, new_binders_from_root, free_variable_indices))
        }
      }
    }
  return {
    kind: "Abs",
    boundVariables: node.boundVariables,
    body: VarOrApp_Node()
  }
}

/// Pretty-printing of both AST type should produce the same output
fn test(term: ast::Abs<Identifier>) {
  let mut free_variable_indices1 : Vec<String> = Vec::new();
  let readout1 = evaluate_and_name_free_readout::<Identifier>(term, free_variable_indices1);
  let n1 = pretty_print::format_lambda_term(readout1, free_variable_indices1, true);

  println!("n1: {}", n1);

  let free_variable_indices2: Vec<String> = Vec::new();
  let term2 = toDeBruijnAST(term, [], free_variable_indices2);
  let [readout2, _] = evaluate_and_name_free_readout(DeBruijnPair_find_binder, term2, free_variable_indices2)
  let n2 = format_lambda_term(readout2, true, free_variable_indices2).pretty_printed;
  println!("n2: {}", n2);

  if n1 != n2 {
    panic!("Test failed: normalizing both AST types should give the same result")
  }
}
test(neil)
test(varityTwo)


console.log('Test printing a lambda term from the deBruijn AST')
let d = format_lambda_term(toDeBruijnAST(omega, [], []), false).pretty_print
let d2 = format_lambda_term(omega, false).pretty_print
console.log(d)
console.log(d2)
if(d !== d2 ) {
  throw "Pretty printing should give the same result"
}

*/

mod tests {

  #[test]
  fn test_traversals_enumeration () {
    let p = crate::alt_lambdaterms::TermParser::new();
    let neil = p.parse(r"(λ u . u (x u))(λ v . v y)").unwrap();


    println!("===== Enumerating all traversals");
    super::evaluate::<String>(&neil);
  }

  #[test]
  fn test_normalization_by_traversals_namefree () {
    let p = crate::alt_lambdaterms::TermParser::new();

    println!("===== Evaluation without name resolution");

    let neil = p.parse(r"(λ u . u (x u))(λ v . v y)").unwrap();
    super::evaluate_and_print_normal_form(&neil);

    let varity_two = p.parse(r"(λ t . t (λ n a x . n (λ s z . a (s (x s z)))) ( λ a . a) (λ z0 . z0) ) (λ s2 z2 . s2 (s2 z2))").unwrap();
    //super::evaluate_and_print_normal_form(varityTwo);

    //// Don't do this!
    let omega = p.parse(r"(λ x . x x)(λ x . x x)").unwrap();
    // super::evaluate_and_print_normal_form(omega)
  }


  #[test]
  fn test_normalization_by_traversals () {
    let p = crate::alt_lambdaterms::TermParser::new();
    let neil = p.parse(r"(λ u . u (x u))(λ v . v y)").unwrap();

    println!("===== Evaluation with name-preserving resolution");
    // super::evaluate_resolve_print_normal_form(&neil);
    // super::evaluate_resolve_print_normal_form(varityTwo)
  }
}