/// Traversing lambda terms in Rust
/// William Blum, May 2021
///
//use crate::ast::{LmdTerm};
use crate::travnorm::TermBranching::{Abs, Var, App};
use crate::travnorm::Generalized::{Structural, Ghost};

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
struct GhostVarNode { }

/// Ghost abstraction node
#[derive(Clone)]
struct GhostAbsNode {
  /// List of bound variable names: always empty in a traversal prior to taking the core projection
  bound_variables : Vec<Identifier>
}

/// Generalizing the concept of node or occurrences.
/// Type `S` represents a 'structural' form
/// Type `G` represents a 'ghost' form
#[derive(Clone, Copy)]
enum Generalized<S, G> {
  Structural(S),
  Ghost(G)
}

/// A generalized lambda node is either
/// - a structural lambda node
/// - a ghost lambda  node
type GeneralizedAbsNode<T> = Generalized<Rc<ast::Abs<T>>, Rc<GhostAbsNode>>;

/// A justification pointer
#[derive(Clone, Copy)]
struct Pointer {
  /// distance from the justifier in the sequence
  distance : usize,
  /// and pointer's label
  label : i32
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
struct UnjustifiedOccurrence<N> {
   node : Rc<N>
}

/// An node occurrence with an associated justification pointer.
/// - For a lambda-node distinct from the root: points to its parent-node
/// - For an internal variable: point to the occurrence of the lambda-node in the P-view binding the variable.
#[derive(Clone)]
struct JustifiedOccurrence<N> {
  /// the occurring node from the term tree
  node : Rc<N>,
  /// justification pointer and scope
  j : JustificationWithScope
}

#[derive(Clone)]
struct MaybeJustifiedOccurrence<N> {
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
enum TermBranching<V,L,A> {
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

/// Occurrence of structural nodes
//type StructuralOccurrence<T> = TermBranching<JustifiedOccurrence<ast::Var<T>>, MaybeJustifiedOccurrence<ast::Abs<T>>, AppOccurrence<T>>;


enum Extension<T> {
    None,
    Single(Occurrence<T>),
    Choice(Vec<JustifiedOccurrence<GeneralizedAbsNode<T>>>)
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
struct PviewIteration<'a, T> {
  current_pos : i32,
  t: &'a JustSeq<T>,
}

/// Iterate backward over the P-view of a justified sequence
impl<'a, T: Clone> Iterator for PviewIteration<'a, T> {
  type Item = (Occurrence<T>, usize);

  fn next(&mut self) -> Option<(Occurrence<T>, usize)> {
    let i = self.current_pos;

    if i>=0 {
      let last_occurrence : Occurrence<T> = self.t[i as usize];
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
      Generalized::Structural(occ) =>
        if child_index <= occ.arity() {
          GeneralizedAbsNode::Structural(Rc::clone(&occ.node.arguments[child_index-1]))
        } else {
          GeneralizedAbsNode::Ghost(Rc::new(GhostAbsNode {
            bound_variables: Vec::new()
          }))
        }

      Generalized::Ghost(_) =>
        GeneralizedAbsNode::Ghost (Rc::new(GhostAbsNode { bound_variables: Vec::new() })),
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
      GeneralizedAbsNode::Structural(Rc::clone(&self.node.operator))
    } else if child_index <= self.arity() {
      GeneralizedAbsNode::Structural(Rc::clone(&self.node.operands[child_index-1]))
    } else {
      GeneralizedAbsNode::Ghost (Rc::new(GhostAbsNode { bound_variables: Vec::new() }))
    }
  }
}

/// Create an occurrence of a child node of a given node occurrence
/// Arguments
/// - `m` occurrence of the parent node
/// - `childIndex` child index defining the node to create an occurrence of
/// - `distance` distance from the occurrence of the node m in the sequence
fn create_occurrence_of_child_of<O : OnTheFlyChildren<GeneralizedAbsNode<T>> + HasScope, T>(
  m: &O,
  child_index: usize,
  distance: usize
  )
  -> JustifiedOccurrence<GeneralizedAbsNode<T>>
{
  JustifiedOccurrence {
    node: Rc::new(m.get_or_create_child(child_index) ),
    j : JustificationWithScope {
          pointer: Pointer { distance: distance, label: child_index as i32 },
          scope: m.scope() // has same scope as parent node
        }
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
trait BinderLocator<Name> {

  fn locate<'a> (
    reference_to_variable_name : &Name,
    pview: PviewIteration<'a, Name>,
    free_variable_indices: &Vec<Identifier>) -> Pointer;

}

/// lookup the index assigned to a free variable, or create one if it is not defined yet
fn lookup_or_create_free_variable_index(
  free_variable_indices: &Vec<Identifier>,
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
    free_variable_indices: &Vec<Identifier>
  ) -> Pointer {
    // read the P-view backward and stop at the first binder containing the variable name
    let mut d = 1;
    for (b, _) in pview {
      match b {
        TermBranching::Abs(Generalized::Structural(a)) => {
          match a.node.bound_variables.iter().position(|v| v == variable_name) {
            Some(i) =>
              return Pointer { distance: d, label: i as i32 +1 },
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
      label: lookup_or_create_free_variable_index(free_variable_indices, variable_name) as i32 }
  }
}

/// Extend a traversal by one more node occurrence.
///
/// The extension follows the traversal rules of the 'normalizing traversals' from the paper
/// The input traversal is not modified, instead it returns the list of possibles node occurrences
/// to traverse, or just void if the traversal is maximal
///
/// Arguments:
///   - `t` the current traversal
///   - `treeRoot` the root of the term tree
///   - `free_variable_indices` vector with names of newly created free variables
fn extend_traversal<T : BinderLocator<T>>(
  treeRoot: &ast::Abs<T>,
  t: &JustSeq<T>,
  free_variable_indices: &Vec<Identifier>
) -> Extension<T>
{
  if t.is_empty() { // Empty sequence?
    Extension::Single(
      TermBranching::Abs(
        Generalized::Structural(
          MaybeJustifiedOccurrence {
            node: Rc::new(*treeRoot),
            j : None,
          })))
  } else {
    let nextIndex = t.len();
    let lastIndex = nextIndex-1;
    let last_occurrence :&Occurrence<T> = &t[lastIndex];
    match last_occurrence {
      App(app) =>

        Extension::Single(
          TermBranching::Abs(
            Generalized::Structural(
              MaybeJustifiedOccurrence {
                node: app.node.operator, // traverse the operator node
                j : Some(JustificationWithScope {
                  pointer : Pointer { distance:1, label: 0 },
                  scope: Scope::Internal
                })
              }
          ))),

      Var(var) if last_occurrence.scope() == Scope::Internal =>{
          // (Var) copy-cat rule
          let just = &var.pointer();
          let child_index = just.label as usize;
          let distance = 2 + just.distance;

          // Occurrence `m` from the paper, is the node preceding the variable occurrence's justifier.
          // Type assertion: by construction traversal verify alternation therefore m is necessarily a variable occurrence
          let m = t[nextIndex - distance];

          let jo = match m {
            TermBranching::App(m_a) => { create_occurrence_of_child_of(&m_a, child_index, distance) },
            TermBranching::Var(m_v) => { create_occurrence_of_child_of(&m_v, child_index, distance) },
            TermBranching::Abs(m_a) => panic!("Impossible: a variable's justifier predecessor cannot be an abstraction node occurrence."),
          };

          let a = match jo {
            JustifiedOccurrence { node: n, j: j} =>
              match *n {
                  Generalized::Structural(ns) => Generalized::Structural(MaybeJustifiedOccurrence{node: ns, j: Some(j)}),
                  Generalized::Ghost(ng) => Generalized::Ghost(JustifiedOccurrence{node: ng, j: j})
              }
          };

          Extension::Single(TermBranching::Abs(a))
      }

      Var(v) => // external variable
      {
          // Get the list of possible occurrences opening up a new strand
          // in a strand-complete traversal
          // (empty if the traversal is maximal)
          let da = dynamic_arity(t);
          let range = 1..(da+1);
          let possible_children : Vec<JustifiedOccurrence<_>> =
              range
              .map(move |i| create_occurrence_of_child_of(v, i, 1))
              .collect();

          if possible_children.is_empty() {
            Extension::None
          } else {
            Extension::Choice(possible_children)
          }
      }

      Abs(Generalized::Structural(abs_node)) => {
          let bodyNode = abs_node.node.body;
          // traverse the body of the lambda
          match &bodyNode {
            ast::AppOrVar::App(body_app) =>
              Extension::Single(App(UnjustifiedOccurrence {
                    node: Rc::clone(body_app),
                  })),

            ast::AppOrVar::Var(body_var) => {
              let p = pview(t);
              let n = body_var.name;
              let pointer = T::locate(&n, p, free_variable_indices);

              let m = &t[nextIndex - pointer.distance]; // if d= 1 then the justifier is the last occurrence

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
        //let m = t[lastIndex-last_occurrence.justifier.distance];
        let d = g.j.pointer.distance;
        let m = t[lastIndex-d];

        let justifierDistance = d + 2;
        let mu = t[nextIndex - justifierDistance];
        let i = g.j.pointer.label;
        VERY_VERBOSE && println!("[GhostAbs-arity] m: {}, mu: {}, i: {}", m.arity(), mu.arity(), i);
        Extension::Single(
          Var(
            Generalized::Ghost(
              JustifiedOccurrence {
                node: Rc::new(GhostVarNode{}),
                j : JustificationWithScope {
                  pointer : Pointer { distance: justifierDistance,
                                        label: mu.arity() as i32 + i - m.arity() as i32 },
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

fn as_string_list<T:ToString>(v:Vec<T>) -> Vec<String> {
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
  let o = t[index];
  match o {
    TermBranching::Abs(Generalized::Structural(MaybeJustifiedOccurrence{ j : None, node : node })) =>
      format!("[{}]",as_string_list(node.bound_variables).join(" ")),

    TermBranching::Abs(Generalized::Structural(MaybeJustifiedOccurrence{ j : Some(j), node : node })) =>
      format!("[{}]{}", as_string_list(node.bound_variables).join(" "), format_pointer(&j.pointer)),

    TermBranching::Abs(Generalized::Ghost(jo)) =>
      format!("$[{:?}]{:?}", jo.node.bound_variables, format_pointer(&jo.j.pointer)),

    TermBranching::Var(Generalized::Structural(v)) =>
    {
      let pointer = &v.j.pointer;

      let justifier = &t[index as usize - pointer.distance];
      match justifier {
        App(_) | Var(_) => panic!("A variable's justifier can only be an occurrence of a lambda node."),

        Abs(Generalized::Ghost(jo)) => panic!("A structural variable can only be justified by a structural lambda node."),

        Abs(Generalized::Structural(jo)) => {
          let justifier_bound_variables = jo.node.bound_variables;
          let l = pointer.label as usize;
          let name =
            if l <= justifier_bound_variables.len() {
              justifier_bound_variables[l - 1].to_string()
            } else {
              free_variable_indices[(l - 1 - justifier_bound_variables.len()) as usize]
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
     .map(|(i, o)| format_occurrence(t, i, free_variable_indices))
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

  fn next(&mut self) -> Option<Occurrence<T>> {
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
                        bound_variables : [ g.node.bound_variables, self.pending_lambdas].concat(),
                      }),
                    })
           },
           Generalized::Structural(s) => {
              Generalized::Structural(
                MaybeJustifiedOccurrence{
                    j : s.j,
                    node : Rc::new(ast::Abs{
                      // unload the pending lambdas onto the node occurrence
                      bound_variables : [ s.node.bound_variables, self.pending_lambdas].concat(),
                      body : s.node.body
                    })
                })
          }
         };

         self.pending_lambdas.truncate(0);

         Some(Abs(clone_occurrence))
      },

      Abs(Generalized::Structural(a)) => {
         self.pending_lambdas = [ a.node.bound_variables, self.pending_lambdas].concat();
         None
      },

      Abs(Generalized::Ghost(a)) => {
        self.pending_lambdas = [ a.node.bound_variables, self.pending_lambdas].concat();
         None
      },

      Var(v) if v.scope() == Scope::External => {
         // patch link distance to account for the removed occurrences (underneath the pointer)
         let d = v.pointer().distance;
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
                node : s.node
              })
           },
           Ghost(g) => {
            Ghost(
              JustifiedOccurrence {
                  j : JustificationWithScope {
                    pointer: Pointer { distance: d, label: g.j.pointer.label },
                    scope: g.j.scope
                  },
                node : g.node
              })
           }
         };

         self.pending_lambdas.truncate(0);

         Some (Var(cloned_occurrence))
      },

      Var(_) | App(_) => {
        // pop arity(o) elements from the left of the array
        let (left, right) = self.pending_lambdas.split_at(o.arity());
        self.pending_lambdas = right.to_vec();
        None
      }
    }
  }
}

/// Return an iterator over the core projection of a traversal
fn core_projection<T>(t: &JustSeq<T>) -> CoreProjection<T> {
  CoreProjection {
    pending_lambdas : Vec::new(),
    t : t,
    position : t.len()-1 // start calculating from the right
  }
}

/// Traverse the next strand of a term from a given traversal.
///
/// Arguments:
///   - `t` the current traversal
///   - `treeRoot` the root of the term tree
///   - `free_variable_indices` the indices of all free variables
/// Returns an array of all possible next strands, or an empty vector
/// if the input traversal is complete
pub fn traverse_next_strand<T : BinderLocator<T>>(
  treeRoot:&ast::Abs<T>,
  t:&JustSeq<T>,
  free_variable_indices: &Vec<String>
) -> Extension<T>
 {

  let next = extend_traversal(treeRoot, t, free_variable_indices);

  while let Extension::Single(o) = next {
    t.push(o); // append the traversed occurrence
    if VERY_VERBOSE {
      println!("extended: {}", format_sequence(t, free_variable_indices))
    }
    next = extend_traversal(treeRoot, t, free_variable_indices)
  }

  return next
}

fn enumerate_all_traversals<T:BinderLocator<T>>(
  treeRoot: &ast::Abs<T>,
  t: &JustSeq<T>,
  free_variable_indices: &Vec<Identifier>,
  depth:usize
) {

  let indentLog = "  ".repeat(depth);

  let next = traverse_next_strand(treeRoot, t, free_variable_indices);

  let node_choices =
    match next {
      Extension::None => {
        println!("{}|Depth:{}|Maximal traversal:{}",
            indentLog,
            depth,
            format_sequence(t, free_variable_indices));
        let p = core_projection(t).iter().rev().collect();
        println!("{}|      {}        projection:{}",
            indentLog,
            " ".repeat(depth.to_string().len()),
            format_sequence(p, free_variable_indices));
        return;
      },

      // external variable with single choice
      Extension::Single(s) => [s],

      // external variable with multiple non-deterministic choices
      Extension::Choice(node_choices) => node_choices
    };

  VERBOSE && println!("{}|Depth:{}|External variable reached with {} branch(es): {}",
    indentLog,
    depth,
    node_choices.len(),
    format_sequence(t, free_variable_indices));

  for o in node_choices {
    let t2: JustSeq<T> = t.append(o);
    VERBOSE && println!("{}|Depth:{}|Choice:{}|Traversal: {}|Occurrence: {}",
      indentLog, depth, o.justifier.label,
      format_sequence(t, free_variable_indices),
      format_occurrence(t2, t.len(), free_variable_indices));
    enumerate_all_traversals(treeRoot, t2, free_variable_indices, depth+1)
  }

}


/// A binder is defined by the list of identifier that it binds
struct Binder {
   boundVariables : Vec<Identifier>
}

/// To support pretty-printing, the type T must implement name lookup
trait NameLookup {
  // Given a list of binders occurring in the path from the root
  // to the variable node, return the name of the variable
  // If the variable is free then the map
  // 'free_variable_indices' can be used to lookup a free variable name from its 'free variable index'
  fn lookup(
    bindersFromRoot: [Binder],
    free_variable_indices: &[Identifier], // read-only
    withEncoding: bool // if true then pretty-print the variable name encoding itself as well as the variable name
  )-> String;
}


/// Pretty-printing helper type
struct Pretty {
  prettyPrint: String,
  mustBracketIfArgument: bool
}

fn bracketize(t: Pretty) -> String {
  if t.mustBracketIfArgument { format!("({})", t.prettyPrint) } else { t.prettyPrint }
}

fn printLambdaTerm<T : NameLookup>(
  r: ast::Abs<T>,
  // print variable name reference encoding in addition to resolved names
  withEncoding: bool,
  // optional array use to assign indices to free variables (used with the deBruijn encoding)
  freeVariableIndices: &Vec<Identifier>
) -> Pretty {

  fn printSubterm(
    t: LambdaAST<T>,
    bindersFromRoot: ast::Abs<T>[]
  ) -> Pretty {
    match (t.kind) {
      case "Var":
        return {
          prettyPrint: (t.name.lookup(bindersFromRoot, freeVariableIndices, withEncoding))
            + (t.arguments.length == 0
              ? ""
              : " " + t.arguments.map(x => bracketize(printSubterm(x, bindersFromRoot))).join(' ')),
          mustBracketIfArgument: t.arguments.length > 0
        }
      case "App":
        return {
          prettyPrint: bracketize(printSubterm(t.operator, bindersFromRoot))
            + t.operands.map(x => bracketize(printSubterm(x, bindersFromRoot))).join(' '),
          mustBracketIfArgument: true
        }
      case "Abs":
        let bodyPrint = printSubterm(t.body, bindersFromRoot.concat(t))
        return (t.boundVariables.length == 0)
          ? {
            prettyPrint: bodyPrint.prettyPrint,
            mustBracketIfArgument: bodyPrint.mustBracketIfArgument
          }
          : {
            prettyPrint: r"\lambda" + t.boundVariables.join(" ") + "." + bodyPrint.prettyPrint,
            mustBracketIfArgument: true
          }
    }
  }
  return printSubterm(r, [])
}

/// Evaluate the term with term tree root treeRoot
fn evaluate<T : NameLookup + BinderLocator>(
  term: ast::Abs<T>
) {
  println!("Traversing {}", printLambdaTerm(term, false, []).prettyPrint);
  enumerate_all_traversals(&term, [], [], 0)
}


fn test () {
  println!("===== Enumerating all traversals");
  evaluate(neil); // <Identifier>
}


/// Evaluate and readout the **name-free** normal-form.
/// This 'read-out' implementation produces an AST with DeBruijn variable references (rather than identifiers).
/// Variable name collision can occur if pretty-printing the term by just looking up variable name
/// without displaying the associated deBruijn pairs.
fn evaluateAndReadout<T : NameLookup + BinderLocator>(
  root:ast::Abs<T>,
  free_variable_indices: &[Identifier]
) -> Vec<(ast::Abs<DeBruijnPair>, [Identifier])>
{
  println!("Evaluating {}", printLambdaTerm(root, false, free_variable_indices).prettyPrint);

  // Read out the subterm at ending at the last node of traversal t
  fn readout(
      // A strand-complete traversal
      t: JustSeq<T>,
      depth: u32
  ) -> ast::Abs<DeBruijnPair> {

    traverse_next_strand<T>(find_binder, root, t, free_variable_indices);

    // get the last two nodes from the core projection
    let p = core_projection(t);
    // The strand ends with an external variable, call it x
    let strandEndVar = p.next().value as VarOccurrence<T>;
     // The strand starts with an external lambda, call it \lambda y1 .... y_n
    let strandBeginAbs = p.next().value as AbsOccurrence<T>;

    let argumentOccurrences = newStrandOpeningOccurrences(t, strandEndVar);
    if argumentOccurrences.length == 0 {
      VERBOSE && console.log("Strand ended|Maximal    |Depth:" + depth + "|Traversal: " + format_sequence(t, free_variable_indices))
    } else {
      VERBOSE && console.log("Strand ended|Not maximal|Depth:" + depth + "|Traversal: " + format_sequence(t, free_variable_indices))
    }

    {
      kind: "Abs",
      boundVariables: strandBeginAbs.node.boundVariables,
      body:
        {
          kind: "Var",
          // Since the core projection of the traversal is the path to the root (see paper),
          // the depth of the variable is precisely the distance to the justifying node in the core projection.
          name: new DeBruijnPair(strandEndVar.justifier.distance, strandEndVar.justifier.label),
          arguments: argumentOccurrences.map(o => readout(t.concat(o), depth+1))
        }
    }
  }

  return [readout([], 0), free_variable_indices]
}

fn evaluateAndPrintNormalForm(term: ast::Abs<Identifier>) {
  let (readout, free_variable_indices) = evaluateAndReadout<Identifier>(term, []);
  println!(printLambdaTerm(readout, false, free_variable_indices).prettyPrint)
}

/*


/// When using name identifier, the binder is the first lambda node
/// in the P-view binding that particular variable name.
/// If no such occurrence exists then it's a free variable
/// (justified by the tree root--the initial node occurrence in the P-view)
fn DeBruijnPair_find_binder<T>(
  variableName: DeBruijnPair,
  pview: PviewIteration<T>, // IterableIterator<[Occurrence<T>, number]>,
  free_variable_indices: &[Identifier]
) -> Pointer {
  let mut enablerDepth: i32 = variableName.depth;
  let mut distance = 1;
  for (_, d) in pview {
    enablerDepth -= 1;
    if enablerDepth <= 0 {
      break;
    };
    distance += d
  }
  return Pointer { distance: distance, label: variableName.index }
}


console.log("===== Evaluation without name resolution")
evaluateAndPrintNormalForm(neil)
evaluateAndPrintNormalForm(varityTwo)


/// Pretty-printing of both AST type should produce the same output
function test(term: Abs<identifier>) {
  let [readout1, free_variable_indices1] = evaluateAndReadout(Identifier_find_binder, term, [])
  let n1 = printLambdaTerm(readout1, true, free_variable_indices1).prettyPrint
  console.log("n1: " + n1)

  var free_variable_indices2: identifier[] = []
  var term2 = toDeBruijnAST(term, [], free_variable_indices2)
  let [readout2, _] = evaluateAndReadout(DeBruijnPair_find_binder, term2, free_variable_indices2)
  let n2 = printLambdaTerm(readout2, true, free_variable_indices2).prettyPrint
  console.log("n2: " + n2)

  if(n1 !== n2) throw "Test failed: normalizing both AST types should give the same result"
}

test(neil)
test(varityTwo)

/// Don't do this!
// evaluateAndPrintNormalForm(omega)

/// Create a new variable with specified prefix
/// that is fresh for the specified list of existing variable names
function freshVariableWithPrefix(prefix:string, isNameClashing:(name:identifier) => boolean)
{
  let candidate = prefix
  let attempts = 1
  while (isNameClashing(candidate)) {
    candidate = prefix + attempts
    attempts++
  }
  return candidate
}

///////// Name resolution with anti-collision

/// Name-preserving conversion of a deBruijn-based AST into an identifier-based AST.
///
/// Attempt to resolve the naming suggestions assigned by the lambda nodes labels
/// when possible. If causing conflicts, the suggested names might be replaced by
/// fresh names.
///
/// This function implements the *name-preserving* read-out algorithm from the paper,
/// that preserves original variable name when possible.
function resolveNameAmbiguity (
  binderNode:Abs<DeBruijnPair>,
  free_variable_indices:identifier[],
  // The list of binders from the root to the last node of t
  // this array gets mutated as bound variable names get renamed to avoid name collision
  // when replacing DeBruijn pairs by variable names.
  bindersFromRoot: (Abs<DeBruijnPair>| GhostAbsNode)[] //= []
  ) :Abs<identifier>
{
  let getBindingIndex = (node: Abs<DeBruijnPair> | GhostAbsNode, variableName: identifier) => node.boundVariables.indexOf(variableName)
  let isBoundByAbsNode = (node: Abs<DeBruijnPair> | GhostAbsNode, variableName: identifier) => getBindingIndex(node, variableName) >= 0

  function nameAlreadyUsedAbove (suggestedName:identifier, binderNameIndex:number) {
    let freeVariableWithSameName = free_variable_indices.indexOf(suggestedName)>=0

    let upperBinderNodesLookup = bindersFromRoot.findIndex(binder=> isBoundByAbsNode(binder, suggestedName))
    let nameUsedInStrictUpperBinderNodes = upperBinderNodesLookup >= 0 && upperBinderNodesLookup < bindersFromRoot.length-1

    let sameBinderNodeLookup = binderNode.boundVariables.indexOf(suggestedName)
    let nameUsedInSameBinderNode = sameBinderNodeLookup >= 0 && sameBinderNodeLookup < binderNameIndex

    return freeVariableWithSameName || nameUsedInStrictUpperBinderNodes || nameUsedInSameBinderNode
  }

  /// Assign permanent bound variable name to the lambda node, one at a time
  bindersFromRoot.push(binderNode)
  for(let b = 0; b<binderNode.boundVariables.length; b++) {
    let suggestedName = binderNode.boundVariables[b]
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
            let overArcingVariableAssignedName = adjustedDeBruijn.lookupBinderAndName(bindersFromRoot, free_variable_indices).name

            return (suggestedName == overArcingVariableAssignedName)
                    || node.arguments.findIndex(o=>hasNamingConflict(o, depthNotToCross+1)) >= 0
          } else {
            return node.arguments.findIndex(o=>hasNamingConflict(o, depthNotToCross+1)) >= 0
          }
        }
      }
      if(hasNamingConflict(binderNode.body, 1)) {
        // resolve the conflict by renaming the bound lambda
        let primedVariableName = binderNode.boundVariables[b]+'\''
        binderNode.boundVariables[b] = freshVariableWithPrefix(primedVariableName, suggestion => nameAlreadyUsedAbove(suggestion, b))
      } else {
        // no  conflict with this suggested name: we make it the permanent name.
      }
    } else {
      // no potential conflict with this suggested name: we make it the permanent name.
    }
  }

  let bodyWithVariableNamesAssigned : App<identifier> | Var<identifier>
  if(binderNode.body.kind == "App") {
    bodyWithVariableNamesAssigned = {
        kind: "App",
        operator: resolveNameAmbiguity(binderNode.body.operator, free_variable_indices, bindersFromRoot),
        operands: binderNode.body.operands.map(a => resolveNameAmbiguity(a, free_variable_indices, bindersFromRoot))
    }
  } else { // if(root.body.kind == "Var") {
    let assignedVariableName = binderNode.body.name.lookupBinderAndName(bindersFromRoot, free_variable_indices).name
    bodyWithVariableNamesAssigned = {
      kind: "Var",
      name: assignedVariableName,
      arguments: binderNode.body.arguments.map(a => resolveNameAmbiguity(a, free_variable_indices, bindersFromRoot))
    }
  }
  bindersFromRoot.pop()
  return {
    kind: "Abs",
    boundVariables: binderNode.boundVariables,
    body:bodyWithVariableNamesAssigned
  }
}

function evaluateResolveAndPrintNormalForm(term: Abs<identifier>) {
  let [readout, free_variable_indices] = evaluateAndReadout(Identifier_find_binder, term, [])
  let resolvedNameReadout = resolveNameAmbiguity(readout, free_variable_indices, [])
  console.log(printLambdaTerm(resolvedNameReadout, false, free_variable_indices).prettyPrint)
}

console.log("===== Evaluation with name-preserving resolution")
evaluateResolveAndPrintNormalForm(neil)
evaluateResolveAndPrintNormalForm(varityTwo)

*/