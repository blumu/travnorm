/// Traversing lambda terms in Rust
/// William Blum, May 2021
///

use crate::traversal::TermBranching::{Abs, Var, App};
use crate::traversal::Generalized::{Structural, Ghost};

use crate::ast::{ alternating as ast, Identifier };
use std::rc::Rc;

// if true then print additional logging
const VERBOSE :bool = false;

// if true print traversal after every single extension
const VERY_VERBOSE :bool = false;

// if true then print additional debugging information
const DEBUG :bool = false;

// Experimental: compress traversals by skipping consecutive occurrences of internal ghost nodes
// traversed with the two copy-cat rules.
const PUMP_COPYCAT_GHOSTS :bool = true;


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

/// A justification pointer
#[derive(Clone, Copy)]
pub struct Pointer {
  /// distance from the justifier in the sequence
  distance : usize,
  /// and pointer's label
  label : usize
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
  current_pos : Option<usize>,
  t: &'a JustSeq<T>,
}

/// Iterate backward over the P-view of a justified sequence
impl<'a, T: Clone> Iterator for PviewIteration<'a, T> {
  type Item = (Occurrence<T>, usize);

  fn next(&mut self) -> Option<(Occurrence<T>, usize)> {
    match self.current_pos {
      None => None,
      Some(i) => {
        let last_occurrence : &Occurrence<T> = &self.t[i];
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

        self.current_pos = Some (i - k);

        Some ((last_occurrence.clone(), k))
      }
    }
  }
}

/// Iterate over the P-view of a justified sequence.
///
/// Return the sequence of occurrence in the P-view (read backwards)
/// together with the position deltas between consecutive occurrences in the P-view
fn pview<'a, T>(t: &'a JustSeq<T>) -> PviewIteration<'a, T> {
  PviewIteration {
      current_pos : if t.is_empty() { None } else { Some(t.len() - 1) },
      t : t
  }
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

/// Dynamic arity of a traversal.
/// Pre-condition: The last node in `t` must end with an external variable occurrence
fn dynamic_arity<T>(t: &JustSeq<T>) -> usize {
  if t.is_empty() {
    panic!("Cannot compute dynamic arity of an empty traversal")
  }

  let mut i = t.len();
  let mut sum : isize = 0;
  let mut max = sum;

  while i >= 1 {
    let o = &t[i-1];
    match o {
      TermBranching::Abs(_) if o.scope() == Scope::External =>
        return max as usize,

      TermBranching::Abs(_) =>
        sum -= o.arity() as isize,

      TermBranching::Var(_) | TermBranching::App(_) => {
        sum += o.arity() as isize;
        if sum > max {
          max = sum
        }
      }
    }
    i = i-1
  };

  max as usize
}

/// Ability to fetch structural children nodes by index
trait HasChildren<T> {
  fn try_get_structural_child(&self, child_index: usize) -> Option<Rc<ast::Abs<T>>>;
}

impl<T> HasChildren<T> for VarOccurrence<T> {
  // Return the requested structural child of a variable-node
  fn try_get_structural_child(&self, child_index: usize) -> Option<Rc<ast::Abs<T>>> {
    match &self {
      Generalized::Structural(occ) if child_index <= occ.arity() =>
        Some(Rc::clone(&occ.node.arguments[child_index-1])),
      Generalized::Structural(_) | Generalized::Ghost(_) => None
    }
  }
}

impl<T> HasChildren<T> for AppOccurrence<T> {
  // Return the requested structural child of an @-node
  fn try_get_structural_child(&self, child_index: usize) -> Option<Rc<ast::Abs<T>>> {
    if child_index == 0 {
      Some(Rc::clone(&self.node.operator))
    } else if child_index <= self.arity() {
      Some(Rc::clone(&self.node.operands[child_index-1]))
    } else {
      None
    }
  }
}

/// Create an occurrence of a generalized (i.e. possibly fictitious) child node
/// of a given @/var node occurrence
/// Arguments
/// - `m` occurrence of the parent @ or variable node
/// - `child_index` the index of the child node to create an occurrence of, ranging from
///   1 to arity(x) for a variable-node,
///   0 to arity(x) for an @-node.
/// - `distance` distance from the created occurrence to the occurrence `m` in the underlying sequence
fn create_occurrence_of_child_of<O : HasChildren<T> + HasScope, T>(
  m: &O,
  child_index: usize,
  distance: usize
  )
  -> AbsOccurrence<T>
{
  match m.try_get_structural_child(child_index) {
    Some(s) =>
      Structural(MaybeJustifiedOccurrence{
        node: Rc::clone(&s),
        j : Some(JustificationWithScope {
          pointer: Pointer { distance: distance, label: child_index },
          scope: m.scope() // has same scope as parent node
        })
      })
    ,
    None =>
      Ghost(
        JustifiedOccurrence {
        node: Rc::clone(&Rc::new(GhostAbsNode { bound_variables: Vec::new() })),
        j : JustificationWithScope {
              pointer: Pointer { distance: distance, label: child_index },
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

      free_variable_indices.len()
    },

    Some(j) => // create a fresh free variable name
      j + 1
  }
}

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
              return Pointer { distance: d, label: i + 1 },
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
    Pointer {
      distance: d,
      label: lookup_or_create_free_variable_index(free_variable_indices, variable_name) }
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
      .map(|i| create_occurrence_of_child_of(last_occurrence, i, 1))
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
          let mut distance = 2 + just.distance;
          let mut child_index = just.label;

          // Occurrence `m` from the paper, is the node preceding the variable occurrence's justifier.
          // Type assertion: by construction traversal verify alternation therefore m is necessarily a variable occurrence
          let mut m = &t[next_index - distance];

          if PUMP_COPYCAT_GHOSTS {

            // Pump the next consecutive (lambda, variable) pairs of occurrences
            // until reaching a structural lambda (either external or internal),
            // an external lambda, or an external variable.

            loop {

              // At each iteration, `m` refers to the justifier of the next lambda occurrence

              if m.scope() == Scope::External {
                // next occurrence is external
                // => stop pumping!
                break
              }

              if child_index <= m.arity() {
                // next occurrence is a structural lambda
                // => stop pumping!
                break
              }

              // We perform one look-ahead (traversing the child of the ghost lambda)
              // to check if the next variable node to traverse is external or internal.
              //
              // We've determined so far that the next occurrence after `t` is
              // a ghost lambda, denoted `{}`, with pointer (child_index, distance).
              //
              // With one more look-ahead using the ghost lambda traversal rule we have that
              // the following occurrence is a ghost variable, denoted `$`
              // with pointer distance `distance+2` and label `mu.arity() + child_index - m.arity()`
              //
              //    t' =  t -- {}(child_index, distance) -- $(mu.arity() + child_index - m.arity(), distance+2)
              //
              // where
              //    - `m` is the justifier of the ghost lambda occurrence in `t`,
              //    - `mu` is the justifier in `t` of the variable occurrence following the ghost lambda;
              //       it is located immediately before `m`.
              let mu = &t[next_index - distance-1];

              if mu.scope() == Scope::External {
                // next variable occurrence is external
                // => stop pumping
                break
              }

              // pump out the (ghost lambda, internal variable) pair
              distance += 2;
              child_index = child_index+ mu.arity() - m.arity();
              m = &t[next_index - distance];
             }
          }

          Extension::Single(Abs(match m {
            TermBranching::App(m_a) => { create_occurrence_of_child_of(m_a, child_index, distance) },
            TermBranching::Var(m_v) => { create_occurrence_of_child_of(m_v, child_index, distance) },
            TermBranching::Abs(_) => panic!("Impossible: a variable's justifier predecessor cannot be an abstraction node occurrence."),
          }))
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
              let pointer = T::locate(&body_var.name, pview(t), free_variable_indices);

              let m = &t[next_index - pointer.distance]; // if distance = 1 then the justifier is the last occurrence

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
        let mut m = &t[last_index-d];

        let mut justifier_distance = d + 2;
        let mut mu = &t[next_index - justifier_distance];
        let mut i = g.j.pointer.label;
        if VERY_VERBOSE { println!("[GhostAbs-arity] m: {}, mu: {}, i: {}", m.arity(), mu.arity(), i); };

        if PUMP_COPYCAT_GHOSTS {
            // Pump the next consecutive (variable, lambda) pairs of occurrences
            // until reaching either:
            //  (i) an external variable
            //  (ii) an internal variable followed by an external lambda
            //  (iii) a variable followed by a *structural* lambda (either external or internal).

          loop {

            // At each iteration, `m` refers to the justifier of the lambda occurrence
            // and `mu` refers to the justifier of the following variable occurrence.

            if mu.scope() == Scope::External {
              // next variable occurrence is external (i
              // => stop pumping!
              break
            }

            let next_child_index = i + mu.arity() - m.arity();

            // We perform one look-ahead to check if the next lambda node to traverse
            // is either external or structural.
            //
            // We've determined so far that the next occurrence after `t` is
            // a ghost variable with pointer `(next_child_index, justifier_distance)`.
            //
            // One more look-ahead using the variable copy-cat rule shows that
            // the following occurrence is a lambda node
            // with pointer `(next_child_index, justifier_distance+2)`
            // pointing to its justifier `next_m`.
            let next_m = &t[next_index - justifier_distance-1];

            if next_m.scope() == Scope::External {
              // next lambda occurrence is external (ii)
              // => stop pumping
              break
            }

            if next_child_index <= next_m.arity() {
              // next occurrence is a structural lambda (iii)
              // => stop pumping!
              break
            }

            // pump out the (ghost lambda, internal variable) pair
            justifier_distance += 2;
            i = next_child_index;
            m = next_m;
            mu = &t[next_index - justifier_distance];
          }
        }

        Extension::Single(Var(
            Generalized::Ghost(
              JustifiedOccurrence {
                node: Rc::new(GhostVarNode{}),
                j : JustificationWithScope {
                  pointer : Pointer { distance: justifier_distance,
                                        label: mu.arity() + i - m.arity() },
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
      format!("{{{}}}{}", as_string_list(&jo.node.bound_variables).join(" "), format_pointer(&jo.j.pointer)),

    TermBranching::Var(Generalized::Structural(v)) =>
    {
      let pointer = &v.j.pointer;

      let justifier = &t[index - pointer.distance];
      match justifier {
        App(_) | Var(_) => panic!("A variable's justifier can only be an occurrence of a lambda node."),

        Abs(Generalized::Ghost(_)) => panic!("A structural variable can only be justified by a structural lambda node."),

        Abs(Generalized::Structural(jo)) => {
          let justifier_bound_variables = &jo.node.bound_variables;
          let l = pointer.label;
          let name =
            if l <= justifier_bound_variables.len() {
              justifier_bound_variables[l - 1].to_string()
            } else {
              let free_var_index = l - 1 - justifier_bound_variables.len();
              if free_var_index < free_variable_indices.len() {
                free_variable_indices[free_var_index].clone()
              } else {
                panic!("Invalid free variable index: {}", free_var_index)
                //format!("@FV_{}@", free_var_index)
              }
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
    free_variable_indices:&[Identifier]) -> String
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
  /// index to name mapping for all free variables
  free_variable_indices: &'a Vec<Identifier>,
  /// List of pending lambdas at this point
  pending_lambdas: Vec<Identifier>,
  /// Position of the current node occurrence in the input traversal
  position : usize
}

/// Iterate over the core projection of a traversal
impl<'a, T : Clone + ToString> Iterator for CoreProjection<'a, T> {
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

          self.pending_lambdas.clear();

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

          self.pending_lambdas.clear();

          return Some (Var(cloned_occurrence))
        },

        Var(_) | App(_) => {
          // pop arity(o) elements from the left of the array
          let arity = o.arity();

          if DEBUG {
            println!("t:{} | o: {} | arity: {} | pending lambdas: {:?}",
              format_sequence(&self.t, &self.free_variable_indices),
              format_occurrence(&self.t, i, &self.free_variable_indices), arity, self.pending_lambdas);
          }

          if self.pending_lambdas.len() >= arity {
            self.pending_lambdas.drain(0..arity);
          } else {
            self.pending_lambdas.clear();
          }
        }
      }
    }
  }
}

/// Return an iterator over the core projection of a traversal
fn core_projection<'a, T>(t: &'a JustSeq<T>, free_variable_indices: &'a Vec<Identifier>) -> CoreProjection<'a, T> {
  CoreProjection {
    pending_lambdas : Vec::new(),
    t : t,
    free_variable_indices : free_variable_indices,
    position : t.len() // start calculating from the right
  }
}

/// Traverse the next strand of a term from a given traversal.
///
/// Arguments:
///   - `t` the current traversal
///   - `tree_root` the root of the term tree
///   - `free_variable_indices` the indices of all free variables
/// Returns an array of all possible next strand openings, or an empty vector
/// if the input traversal is complete.
fn traverse_next_strand<T : Clone + ToString + BinderLocator<T>>(
  tree_root:&ast::Abs<T>,
  t:&mut JustSeq<T>,
  free_variable_indices: &mut Vec<String>
) -> Extension<T>
 {

  let mut next = extend_traversal(tree_root, t, free_variable_indices);

  while let Extension::Single(o) = next {
    t.push(o); // append the traversed occurrence

    if VERY_VERBOSE { println!("extended: {}", format_sequence(t, free_variable_indices)) }

    next = extend_traversal(tree_root, t, free_variable_indices);
  }

  if VERY_VERBOSE { println!("traverse_next_strand completes, l ={}", t.len()) }

  next
}

/// Enumerate and print all the traversals of a lambda term term
/// starting from a given incomplete traversal prefix `t`
fn enumerate_all_traversals_from<T: Clone + ToString + BinderLocator<T>>(
  tree_root: &ast::Abs<T>,
  t: &mut JustSeq<T>,
  free_variable_indices: &mut Vec<Identifier>,
  depth:usize
) {

  let log_indent = "  ".repeat(depth);

  match traverse_next_strand(tree_root, t, free_variable_indices) {
    Extension::None => {
      println!("{}|Depth:{}|Length:{}|Maximal traversal:{}",
          log_indent,
          depth,
          t.len(),
          format_sequence(t, free_variable_indices));

      let mut p : Vec<Occurrence<T>> = core_projection(t, free_variable_indices).collect();
      p.reverse();

      println!("{}|      {}        projection:{}",
          log_indent,
          " ".repeat(depth.to_string().len()),
          format_sequence(&p, free_variable_indices));
    },

    Extension::Single(_) => {
      panic!("Cannot happen: single-choice extensions all unfolded when traversing the strand!")
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
        let label = o.may_pointer().unwrap().label;
        let before_length = t.len();
        t.push(Abs(o));
        if VERBOSE { println!("{}|Depth:{}|Choice:{}|Traversal: {}|Occurrence: {}",
          log_indent, depth,
          label, // node_occurrence_choices all have a pointer
          format_sequence(t, free_variable_indices),
          format_occurrence(t, t.len()-1, free_variable_indices));
        }
        enumerate_all_traversals_from(tree_root, t, free_variable_indices, depth+1);
        t.truncate(before_length);
      }
    }
  }
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
  use crate::ast::{ alternating as ast, Identifier };

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
  /// - `root` Root of the lambda term AST
  ///
  /// - `with_encoding` if true print variable name reference encoding in addition to resolved names.
  /// E.g. when using DeBruijn pair encoding, this would print terms of this form:
  /// `\lambda x x s z.s(1,3) (x(3,1) s(5,3) (x(5,2) s(7,3) z(7,4)))`
  /// where the encoding in bracket helps removed the ambiguity caused by having the same name `x`
  /// shared by two distinct bound variables.
  /// In this example, `x(3,1)` refers to the first bound `x`, while `x(5,2)` refers to the second bound variable `x`.
  ///
  /// - `free_variable_indices` array that can optionally be used by the variable lookup function to
  /// assign an index to free variables.
  /// This is used for instance, when T is the deBruijn encoding. If `T` is String it's not used.
  ///
  ///
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
    binders_from_root: &mut Vec<super::Binder>
  ) -> Pretty {
    let mut p : String = var.name.lookup(binders_from_root, free_variable_indices, with_encoding).to_owned();

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
    binders_from_root: &mut Vec<super::Binder>
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

  fn format_abs<T : NameLookup + Clone>(
    abs_term: &ast::Abs<T>,
    free_variable_indices: &Vec<Identifier>,
    with_encoding: bool,
    binders_from_root: &mut Vec<super::Binder>
  ) -> Pretty {

    binders_from_root.push(abs_term.bound_variables.clone());

    let body_print =
      match &abs_term.body {
        ast::AppOrVar::Var(v) => format_var(v, free_variable_indices,with_encoding,  binders_from_root),
        ast::AppOrVar::App(a) => format_app(a, free_variable_indices, with_encoding, binders_from_root),
      };

    binders_from_root.pop();

    if abs_term.bound_variables.is_empty() {
      Pretty {
        pretty_printed: body_print.pretty_printed,
        must_bracket_if_argument: body_print.must_bracket_if_argument
      }
    } else {
      Pretty {
        pretty_printed: format!(r"λ {}.{}", abs_term.bound_variables.join(" "), body_print.pretty_printed),
        must_bracket_if_argument: true
      }
    }
  }

}

/// Enumerate all the traversals of a lambda term term
pub fn enumerate_all_traversals<T : Clone + ToString + NameLookup + BinderLocator<T>>(
  term: &ast::Term<T>
) {
  println!("Traversing {}", pretty_print::format_lambda_term(term, &Vec::new(), false));
  enumerate_all_traversals_from(term, &mut Vec::new(), &mut Vec::new(), 0)
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
  index: usize
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

      let ghost_naming = format!("#({},{})", self.depth, self.index);

      let free_variable_start_index = root_bound_variables.len() + 1;

      let variable_name =
        if is_bound_by_root && self.index >= free_variable_start_index {
          let free_variable_index = self.index - free_variable_start_index;
          &free_variable_indices[free_variable_index]
        } else {
          if self.index > binder_bound_variables.len() {
            // unresolved ghost variable name (should never happen on core-projected traversals)
            &ghost_naming
          } else {
            &binder_bound_variables[self.index - 1]
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

/// Recursively traverse the term tree and read out its normal form.
///
/// The traversal resumes at the point given by the specified traversal `t`
/// and proceeds by recursively extending the traversal one strand at a time.
///
/// The function returns the normal form of the subterm whose root node is
/// the last occurrence of traversal `t`
///
/// Arguments:
/// ----------
/// - `root` the root of the term tree
/// - `t`: a strand-complete traversal of the tree
/// - `free_variable_indices` free variable name to index table
/// - `depth` node depth of the last node in the traversal
fn traverse_and_readout<T : Clone + ToString + BinderLocator<T>>(
    root:&ast::Term<T>,
    mut t: &mut JustSeq<T>,
    free_variable_indices: &mut Vec<Identifier>,
    depth: u32
) -> ast::Abs<DeBruijnPair> {

  traverse_next_strand(root, &mut t, free_variable_indices);

  // get the last two nodes from the core projection
  let mut p = core_projection(t, free_variable_indices);

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
                                  let r = traverse_and_readout(root, t, free_variable_indices, depth+1);
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

/// Evaluate and readout the *name-free* (deBruijn pairs-based)
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
  // Note that we set the `with_encoding` argument to `true`, since otherwise
  // by printing the variable names only we could create naming conflicts.
  println!("Evaluating {}", pretty_print::format_lambda_term(root, free_variable_indices, true));
  traverse_and_readout(root, &mut Vec::new(), free_variable_indices, 0)
}

/// Evaluate and readout the *name-free* normal form of a lambda term and print out the resulting term
pub fn evaluate_and_print_normal_form(term: &ast::Term<Identifier>) {
  let mut free_variable_indices : Vec<String> = Vec::new();
  let readout = evaluate_and_name_free_readout::<Identifier>(term, &mut free_variable_indices);
  println!("{}", pretty_print::format_lambda_term::<DeBruijnPair>(&readout, &free_variable_indices, true))
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
    variable_reference: &DeBruijnPair,
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
    Pointer { distance: distance, label: variable_reference.index }
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


///////// Name resolution with anti-collision

fn try_get_binding_index(b:&Binder, name:&str) -> Option<usize> {
  b.iter().position(|v| v == name)
}

/// Determine if there is any variable occurring below a given node that would cause a naming conflict
/// if the given suggested name were to be introduced in a lambda node above it? I.e. is there a variable occurring
/// below the current node in the term tree whose deBruijn index refers to an upper binding
/// with the same name?
fn has_naming_conflict (
    binding_index: usize,
    abs_node : &ast::Abs<DeBruijnPair>,
    free_variable_indices: &[Identifier],
    binders_from_root : &[Binder],
    depth_not_to_cross:usize,
    suggested_name:&str ) -> bool
{
  let depth_not_to_cross = depth_not_to_cross + 1;
  match &abs_node.body {
    ast::AppOrVar::App(a) => {
      has_naming_conflict(binding_index, &a.operator, free_variable_indices, binders_from_root, depth_not_to_cross+1, suggested_name)
      || a.operands.iter().position(|o| has_naming_conflict(binding_index, o, free_variable_indices, binders_from_root, depth_not_to_cross+1, suggested_name)).is_some()
    },

    ast::AppOrVar::Var(v) => {
      // Note that `+1` is needed because variable name in lambda-binders start at index 1
      let current_index_in_current_binder_node = binding_index + 1;
      let over_arcing_binding =
        v.name.depth > depth_not_to_cross
        || (v.name.depth == depth_not_to_cross
            && v.name.index < current_index_in_current_binder_node);

      if over_arcing_binding {
        // We found a variable node with over-arcing binding (i.e. binding lambda occurring above binder 'b')
        // we now lookup its assigned name to check if there is a name conflict
        let adjusted_debruijn = DeBruijnPair{ depth : v.name.depth - depth_not_to_cross + 1, index : v.name.index };
        let over_arcing_variable_assigned_name =
          adjusted_debruijn.lookup(binders_from_root, &free_variable_indices, false);

        if suggested_name == over_arcing_variable_assigned_name {
          return true
        }
      }
      v.arguments.iter().position(|o| has_naming_conflict(binding_index, o, free_variable_indices, binders_from_root, depth_not_to_cross+1, suggested_name)).is_some()
    }
  }
}


/// Name-preserving conversion of a deBruijn-based AST into an identifier-based AST.
///
/// Attempt to resolve the naming suggestions assigned by the lambda nodes labels
/// when possible. The suggested names may be replaced by
/// fresh names if causing conflicts.
///
/// This function implements the *name-preserving* read-out algorithm from the paper,
/// that preserves original variable name when possible.
/// Arguments
/// =========
///
/// - `binder_node` the node in the DeBruijn-based AST defining the root node of the subterm to be converted
/// into an identifier-based AST.
/// - `free_variable_indices` the index to name mapping for free variables
/// - `binders_from_root` The list of binders from the root of the tree to the root of the subterm to be converted (itself excluded from that list)
///    The array gets mutated by the function. This is because when converting DeBruijn pairs to string identifiers, in order to
///    avoid potential name collisions, the function will rename some of the bound variable names in lambda nodes.
//
// Returns
// =======
// The AST corresponding to the input DeBruijn-AST where variables names are all resolved as string identifiers.
//
fn resolve_name_ambiguity (
  binder_node : &ast::Abs<DeBruijnPair>,
  free_variable_indices: &[Identifier],
  binders_from_root : &mut Vec<Binder>
  ) -> ast::Abs<Identifier>
{
  let new_binding_names = binder_node.bound_variables.clone();

  let l = new_binding_names.len();

  binders_from_root.push(new_binding_names);

  // Assign permanent bound variable name to the lambda node, one at a time
  for binder_name_index in 0..l {

    // Determine if a specified identifer is already used in any lambda abstraction
    // 'above' the current binding (at index `binder_name_index` in `binders_from_root.last()`).
    //
    // Since in our AST lambda nodes can abstract multiple variable at once, here `above`
    // means either in a lambda node sitting above the current binder `binders_from_root.last()`
    // or in the same binder node but before `binder_name_index`.
    let name_already_declared_above = | suggested_name:&Identifier | {
      if free_variable_indices.contains(&suggested_name) {
        // there exists a free variable with the same name
        true
      } else {
        let is_bound_by_abs_node = |binder : &Binder| try_get_binding_index(binder, suggested_name).is_some();

        let name_already_used_in_strictly_upper_binder_nodes = {
          // test if any binder node higher up in the AST tree binds the variable
          binders_from_root.iter()
            .take(binders_from_root.len()-1)
            .position(&is_bound_by_abs_node)
            .is_some()
        };

        if name_already_used_in_strictly_upper_binder_nodes {
          true
        } else {
          match try_get_binding_index(&binder_node.bound_variables, suggested_name) {
            Some(same_binder_node_lookup) if same_binder_node_lookup < binder_name_index => true, // name already used in the same binder node
            _ => false
          }
        }
      }
    };

    let suggested_name = &binder_node.bound_variables[binder_name_index];

    if name_already_declared_above(suggested_name)
    && has_naming_conflict(binder_name_index, &binder_node, free_variable_indices, binders_from_root, 0, suggested_name) {

      // resolve the conflict by renaming the bound lambda
      let primed_variable_name = &format!("{}'", binder_node.bound_variables[binder_name_index]);

      let fresh_name = create_fresh_variable(
                          primed_variable_name,
                          &name_already_declared_above);

      binders_from_root.last_mut().unwrap()[binder_name_index] = fresh_name;
    } else {
      // no  conflict with this suggested name: we make it the permanent name.
    }
  }

  let converted_body =
    // create the body of the lambda node with name assigned to all variable occurrences
    match &binder_node.body {
      ast::AppOrVar::App(binder_body_app) => {
        ast::AppOrVar::App(Rc::new(ast::App{
          operator: Rc::new(resolve_name_ambiguity(&binder_body_app.operator, free_variable_indices, binders_from_root)),
          operands: binder_body_app.operands.iter().map(|a| Rc::new(resolve_name_ambiguity(a, free_variable_indices, binders_from_root))).collect()
        }))
      },
      ast::AppOrVar::Var(binder_body_var) => {
        ast::AppOrVar::Var(Rc::new(ast::Var {
            name: binder_body_var.name.lookup(binders_from_root, &free_variable_indices, false),
            arguments: binder_body_var.arguments.iter().map(|a| Rc::new(resolve_name_ambiguity(a, free_variable_indices, binders_from_root))).collect()
          }
        ))
      }
    };

  ast::Abs {
    bound_variables: binders_from_root.pop().unwrap(),
    body: converted_body
  }

}

/// Evaluate and readout the normal form of a lambda term with variable identifier
/// fully resolved and print out the resulting term
pub fn evaluate_resolve_print_normal_form(term: &ast::Abs<Identifier>) {
  let mut free_variable_indices = Vec::new();
  let readout = evaluate_and_name_free_readout::<Identifier>(term, &mut free_variable_indices);
  let resolved_name_readout = resolve_name_ambiguity(&readout, &free_variable_indices, &mut Vec::new());
  println!("Normalized term: {}", pretty_print::format_lambda_term(&resolved_name_readout, &free_variable_indices, false))
}


#[cfg(test)]
mod tests {
  const VARITY_TWO :&str = r"(λ t . t (λ n a x . n (λ s z . a s (x s z))) (λ a . a) (λ z0 . z0)) (λ s2 z2 . s2 (s2 z2))";
  const OMEGA :&str = r"(λ x . x x)(λ x . x x)";
  const NEIL : &str = r"(λ u . u (x u))(λ v . v y)";

  #[test]
  fn test_traversals_enumeration () {
    let p = crate::alt_lambdaterms::TermParser::new();


    println!("===== Enumerating all traversals");
    let neil = p.parse(NEIL).unwrap();
    super::enumerate_all_traversals::<String>(&neil);

    let varity_two = p.parse(VARITY_TWO).unwrap();
    super::enumerate_all_traversals::<String>(&varity_two);
  }


  #[test]
  fn test_normalization_by_traversals_name_free () {
    let p = crate::alt_lambdaterms::TermParser::new();

    println!("===== Evaluation without name resolution");

    let neil = p.parse(NEIL).unwrap();
    super::evaluate_and_print_normal_form(&neil);

    let varity_two = p.parse(VARITY_TWO).unwrap();
    super::evaluate_and_print_normal_form(&varity_two);

    let omega = p.parse(OMEGA).unwrap();
    println!("Traversing {}", super::pretty_print::format_lambda_term(&omega, &Vec::new(), false));

    //// Don't do this, it will run literally forever!
    // super::evaluate_and_print_normal_form(omega)
  }


  #[test]
  fn test_normalization_by_traversals () {
    let p = crate::alt_lambdaterms::TermParser::new();
    let neil = p.parse(NEIL).unwrap();

    println!("===== Evaluation with name-preserving resolution");
    super::evaluate_resolve_print_normal_form(&neil);

    let varity_two = p.parse(VARITY_TWO).unwrap();
    super::evaluate_resolve_print_normal_form(&varity_two);
  }
}