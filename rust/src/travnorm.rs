/// Traversing lambda terms in Rust
/// William Blum, May 2021
///
//use crate::ast::{LmdTerm};
use crate::ast::{ alternating_rc as ast};
use std::cmp;
use std::rc::Rc;

// if true then print additional logging
const VERBOSE :bool = false;

// if true print traversal after every single extension
const VERY_VERBOSE :bool = false;


// trait TraversableAst {
//   type VarType =
// }

////////// Justified sequences

/// Variable identifier type
type Identifier = String;

/// Ghosts variable node
struct GhostVarNode { }

/// Ghost abstraction node
struct GhostAbsNode {
  /// List of bound variable names: always empty in a traversal, but needed for the core projection calculation
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

/// A generalized abstraction node (i.e. either structural or ghost lambda node)
type GeneralizedAbsNode<T> = Generalized<Rc<ast::Abs<T>>, Rc<GhostAbsNode>>;

/// A justification pointer
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
struct JustificationWithScope {
  /// Justification pointer.
  justifier : Pointer,
  /// the scope of the occurrence
  scope : Scope
}

/// An occurrence of a node of type N (without justification pointer)
struct UnjustifiedOccurrence<N> {
   node : Rc<N>
}

/// An node occurrence with an associated justification pointer.
/// - For a lambda-node distinct from the root: points to its parent-node
/// - For an internal variable: point to the occurrence of the lambda-node in the P-view binding the variable.
struct JustifiedOccurrence<N> {
  /// the occurring node from the term tree
  node : Rc<N>,
  /// justification pointer and scope
  j : JustificationWithScope
}

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
type JustSeq<'a, T> = Vec<&'a Occurrence<T>>;

/// Occurrence of structural nodes
//type StructuralOccurrence<T> = TermBranching<JustifiedOccurrence<ast::Var<T>>, MaybeJustifiedOccurrence<ast::Abs<T>>, AppOccurrence<T>>;

/// A generalized lambda node is either
/// - a structural lambda node
/// - a ghost lambda  node
type GeneralizedAbs<T> = Generalized<Rc<ast::Abs<T>>, Rc<GhostAbsNode>>;

enum Extension<T> {
   Single(Occurrence<T>),
   Choice(Vec<JustifiedOccurrence<GeneralizedAbs<T>>>)
}

trait HasScope {
   fn scope(&self) -> Scope;
}

impl<'a, T> HasScope for JustifiedOccurrence<T> {
  fn scope(&self) -> Scope { self.j.scope }
}

impl<'a, T> HasScope for MaybeJustifiedOccurrence<T> {
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
  current_pos : usize,
  t: JustSeq<'a, T>,
}

/// Iterate backward over the P-view of a justified sequence
impl<'a, T> Iterator for PviewIteration<'a, T> {
  type Item = (&'a Occurrence<T>, usize);

  fn next(&mut self) -> Option<(&'a Occurrence<T>, usize)> {
    let i :i32 = self.current_pos as i32;

    if i>=0 {
      let last_occurrence: &Occurrence<T> = &self.t[i as usize];
      let k =
        match last_occurrence {
          TermBranching::Var(_) | TermBranching::App(_)
            => 1,

          TermBranching::Abs(Generalized::Structural(o)) =>
            match &o.j {
              None => return None, // initial node => end of P-view
              Some(j) => j.justifier.distance,
            },

          TermBranching::Abs(Generalized::Ghost(g))
            => g.j.justifier.distance,

        };

      self.current_pos -= k;

      Some ((last_occurrence, k))
    } else {
      None
    }
  }
}

/// Iterate over the P-view of a justified sequence.
///
/// Return the sequence of occurrence in the P-view (read backwards)
/// together with the position deltas between consecutive occurrences in the P-view
fn pview<T>(t: JustSeq<T>) -> PviewIteration<T> {
  PviewIteration { current_pos : t.len()-1, t : t}
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
fn dynamic_arity<'a, T>(t: JustSeq<'a, T>) -> usize {
  let mut i :i32 = t.len() as i32 - 1;
  let mut sum = t[i as usize].arity();
  let mut max = sum;
  i = i-1;
  while i >= 0 {
    let o = &t[i as usize];
    match o {
      TermBranching::Abs(_) if o.scope() == Scope::External => return max,
      TermBranching::Abs(_) => sum -= o.arity(),
      TermBranching::Var(_) | TermBranching::App(_) => {
          sum += o.arity();
          max = cmp::max(sum, max)
        }
    }
    i = i-1;
  };
  max
}

enum VarOrAppOccurrence<'a, T> {
  VarO (&'a VarOccurrence<T>),
  AppO (&'a AppOccurrence<T>)
}

/// Given an occurrence of a variable or application node, returns
/// the (generalized) child node for the specified child index.
///
/// Arguments:
/// - `o` the node occurrence
/// - `childIndex` the index of the child node to fetch, ranging from
///   1 to arity(x) for a variable-node,
///   0 to arity(x) for an @-node.
fn child_of<'a, T>(o: VarOrAppOccurrence<'a, T>, child_index: usize) -> GeneralizedAbsNode<T> {
  match o {
    VarOrAppOccurrence::VarO(Generalized::Structural(occ)) =>
      if child_index <= occ.arity() {
        GeneralizedAbsNode::Structural(Rc::clone(&occ.node.arguments[child_index-1]))
      } else {
        GeneralizedAbsNode::Ghost(Rc::new(GhostAbsNode {
          bound_variables: Vec::new()
        }))
      }

    VarOrAppOccurrence::VarO(Generalized::Ghost(_)) =>
      GeneralizedAbsNode::Ghost (Rc::new(GhostAbsNode { bound_variables: Vec::new() })),

    VarOrAppOccurrence::AppO(o) =>
      if child_index == 0 {
        GeneralizedAbsNode::Structural(Rc::clone(&o.node.operator))
      } else if child_index <= o.arity() {
        GeneralizedAbsNode::Structural(Rc::clone(&o.node.operands[child_index-1]))
      } else {
        GeneralizedAbsNode::Ghost (Rc::new(GhostAbsNode { bound_variables: Vec::new() }))
      }
  }
}

/// Arguments
/// - `m` occurrence of the parent node
/// - `childIndex` child index defining the node to create an occurrence of
/// - `distance` distance from the occurrence of the node m in the sequence
fn create_occurrence_of_child_of<T>(
  m: VarOrAppOccurrence<T>,
  child_index: usize,
  distance: usize
  )
  -> JustifiedOccurrence<GeneralizedAbs<T>>
{

  let s = match &m {
    VarOrAppOccurrence::VarO (v) => v.scope(),
    VarOrAppOccurrence::AppO (a) => a.scope()
  };

  let n = Rc::new(child_of(m, child_index));

  JustifiedOccurrence {
    node: n,
    j : JustificationWithScope {
          justifier: Pointer { distance: distance, label: child_index as i32 },
          scope: s // has same scope as parent node
        }
    }
}

/// Return the list of possible occurrences opening up a new strand
/// in a strand-complete traversal
/// Returns void if the traversal is maximal
fn new_strand_opening_occurrences<'a, T>(
  t: JustSeq<'a, T>,
  last_occurrence: VarOccurrence<T>
)  -> Vec<JustifiedOccurrence<GeneralizedAbs<T>>>
{
  let da = dynamic_arity(t);
  let range = 1..(da+1);
  let possible_children =
      range.map(move |i| create_occurrence_of_child_of(VarOrAppOccurrence::VarO(&last_occurrence), i, 1)).collect();

  possible_children
}

/*

// /// Extend a traversal by one more node
// ///
// /// Arguments:
// ///   - `t` the current traversal
// ///   - `treeRoot` the root of the term tree
// pub fn extend<T> (
//     treeRoot:&LmdTerm<T> ,
//     t:&JustSeq<T>,
//     freeVariableIndices: Vec<String>
//   ) -> Node {
//   match t {
//     LmdTerm::Variable(s) => 1,

//     LmdTerm::App((u, v)) => 1 //+ traverse(*u) + traverse(*v),

//     LmdTerm::Abs(names, body) => 0// traverse(*body)
//   }
// }

////////// Traversals

/// To support traversals for an AST with variable name references of type T,
/// a function of the following type must be implemented.
///
/// When called, it must locate the binder to the specified variable (with binding reference of type T)
/// and return a justification pointer to the occurrence of the binder.
/// The P-view (which represents the path from the variable node to the tree root, see paper)
/// is provided as an iterable argument that enumerates backwards the occurrence in the P-view.
trait BinderLocator<T> {

  fn locate (variableNameReference:T, pview: IterableIterator<(Occurrence<T>, u32)>, freeVariableIndices: Vec<Identifier>) -> Pointer;

}


/// Implement 'findBinder' for AST where the variable name references
/// are encoded as simple name identifiers (string)
///
/// With identifier names, the binder is the first lambda node
/// in the P-view binding that particular variable name.
/// If no such occurrence exists then it's a free variable
/// (justified by the tree root--the initial node occurrence in the P-view)
fn Identifier_findBinder<T> (
  variableName:Identifier,
  pview: Vec<(Occurrence<T>, usize)>,
  freeVariableIndices: Vec<Identifier>
) {
  // read the P-view backward and stop at the first binder containing the variable name
  let d = 1
  for (let [b, _] of pview) {
    match b {
      Abs(_) => {
        let i = b.node.boundVariables.indexOf(variableName)
        if i>-1 {
          return { distance: d, label: i+1 }
        } else {
            let inc = match b {
              Abs(Structural(Init(_))) -> 0
              _ => b.justifier.distance
            }

            d += inc
        }
      },

      _ => d++
  }
  // no binder found: it's a free variable
  return {
    distance: d,
    label: lookupOrCreateFreeVariableIndex(freeVariableIndices, variableName) }
}

/// When using name identifier, the binder is the first lambda node
/// in the P-view binding that particular variable name.
/// If no such occurrence exists then it's a free variable
/// (justified by the tree root--the initial node occurrence in the P-view)
fn DeBruijnPair_findBinder<T>(
  variableName: DeBruijnPair,
  pview: IterableIterator<[Occurrence<T>, number]>,
  freeVariableIndices: identifier[]
) {
  let enablerDepth: number = variableName.depth
  var distance = 1
  for (let [_, d] of pview) {
    enablerDepth--
    if (enablerDepth <= 0) {
      break;
    }
    distance += d
  }
  return { distance: distance, label: variableName.index }
}


/// Extend a traversal using the traversal rules of the 'normalizing traversals' from the paper
/// The input traversal is not modified, instead it returns the list of possibles node occurrences
/// to traverse, or just void if the traversal is maximal
fn extendTraversal<T>(
  findBinder: LocateBinder<T>,
  treeRoot: Abs<T>,
  t: JustSeq<T>,
  freeVariableIndices: identifier[]
): Extension<T>
{
  let nextIndex = t.length
  let lastIndex = t.length-1
  let lastOccurrence = t[lastIndex]

  if (lastOccurrence === undefined) { /// Empty sequence?
    {
      node: treeRoot,
      justifier : undefined,
      scope: Scope.External
    }
  } else {
    match lastOccurrence {
      App(_) => {
          node: lastOccurrence.node.operator, // traverse the operator node
          justifier : { distance:1, label: 0 },
          scope: Scope.Internal
        }
      Var(_) =>
        if lastOccurrence.scope() == Internal {
          // (Var) copy-cat rule
          let distance = 2+lastOccurrence.justifier.distance
          // Occurrence `m` from the paper, is the node preceding the variable occurrence's justifier.
          // Type assertion: by construction traversal verify alternation therefore m is necessarily a variable occurrence
          let m = t[nextIndex - distance] as VarOccurrence<T> | AppOccurrence<T>
          create_occurrence_of_child_of(m, lastOccurrence.justifier.label, distance)
        } else { /// external variable
          newStrandOpeningOccurrences(t, lastOccurrence)
        },
      Abs(Structural(_)) => {
          let bodyNode = lastOccurrence.node.body
          if (bodyNode.kind == "App") {
            {
              node: bodyNode, // traverse the body of the lambda
              scope: Scope.Internal,
              justifier: undefined
            }
          } else {
            let pointer = findBinder(bodyNode.name, pview(t), freeVariableIndices)

            let m = t[nextIndex - pointer.distance] // if d= 1 then the justifier is the last occurrence
            {
              node: bodyNode, // traverse the body of the lambda
              justifier: {
                distance: pointer.distance,
                label: pointer.label
              },
              scope: m.scope()
            }
          }
      },
      Abs(Ghost(_)) => {
        // Traverse the child of the ghost lambda node
        let m = t[lastIndex-lastOccurrence.justifier.distance]

        let justifierDistance = lastOccurrence.justifier.distance + 2
        let mu = t[nextIndex - justifierDistance]
        let i = lastOccurrence.justifier.label
        veryVerbose && console.log("[GhostAbs-arity] m:" + arity(m) + ", mu:" + arity(mu) + ", i:" + i)
        {
          node: GhostVarNode,
          justifier : { distance: justifierDistance,
                        label: arity(mu) + i - arity(m) },
          scope: mu.scope()
        }
      }
    }
  }
}

fn printPointer(p: Pointer) {
  return '(' + p.distance + ',' + p.label + ')'
}

fn printOccurrence<T>(t: JustSeq<T>, o: Occurrence<T>, index: u32, freeVariableIndex: identifier[]) : String {
  match o with {
  Abs(Structural(Init(_))) =>
    '[' + o.node.boundVariables.join(' ') + ']',

  Abs(Structural(_)) =>
    '[' + o.node.boundVariables.join(' ') + ']' + printPointer(o.justifier),

  Var(Structural(_)) =>
    let j = t[index - o.justifier.distance].node as Abs<T>
    let name =
      (o.justifier.label <= j.boundVariables.length)
      ? j.boundVariables[o.justifier.label - 1]
        : freeVariableIndex[o.justifier.label - 1 - j.boundVariables.length]
    name + printPointer(o.justifier),

  App(_) =>
    '@'
  },

  Abs(Ghost(_)) => "$[" + o.node.boundVariables + "]" + printPointer(o.justifier),

  Var(Ghost(_)) => '#' + printPointer(o.justifier)
}

fn printSequence<T>(t: JustSeq<T>, freeVariableIndex:identifier[]) {
  return t.map((o, i) => printOccurrence(t, o, i, freeVariableIndex)).join("--")
}

/// core projection
fn* coreProjection<T>(t: JustSeq<T>) {
  let pendingLambdas: identifier[] = []
  for (let i = t.length - 1; i >= 0; i--) {
    let o = t[i]
    match o {
      Abs(_) if o.scope() == External => {
         let cloneOccurrence = Object.assign({}, o)
         cloneOccurrence.node = Object.assign({}, o.node)
         cloneOccurrence.node.boundVariables = o.node.boundVariables.concat(pendingLambdas)
         yield cloneOccurrence
         pendingLambdas = []
      },
      Abs(_) => {
         pendingLambdas = o.node.boundVariables.concat(pendingLambdas)
      },

      Var(_) if o.scope() == External => {
         // patch link distance to account for removed occurrences
         var d = o.justifier.distance
         for (let j = i - d; j<i; j++) {
           if t[j].scope() == Internal {
             d--
           }
         }
         let cloneOccurrence = Object.assign({}, o)
         cloneOccurrence.justifier = { distance: d, label: o.justifier.label }
         yield cloneOccurrence
         pendingLambdas = []
      },

      Var(_) => {
         pendingLambdas.splice(0, arity(o)) // pop arity(o) elements from the left of the array
      }
      App(_) => {
        pendingLambdas.splice(0, arity(o)) // pop arity(o) elements from the left of the array
      }
  }
}


/// Traverse the next strand of a term from a given traversal.
///
/// Arguments:
///   - `t` the current traversal
///   - `treeRoot` the root of the term tree
///   - `freeVariableIndices` the indices of all free variables
/// Returns an array of all possible next strands, or an empty vector
/// if the input traversal is complete
pub fn traverseNextStrand(
  treeRoot:&LambdaTerm ,
  t:&Traversal,
  freeVariableIndices: Vec<String>
) // -> Node
 {

  let next = extend(treeRoot, t, freeVariableIndices);

  while let o = Extension<T>::single(next) {
    t.push(o) // append the traversed occurrence
    if veryVerbose {
      println!("extended: {}", printSequence(t, freeVariableIndices))
    }
    next = extendTraversal(findBinder, treeRoot, t, freeVariableIndices)
  }

  return next
}


fn enumerateAllTraversals<T>(
  findBinder: LocateBinder<T>,
  treeRoot: Abs<T>,
  t: JustSeq<T>,
  freeVariableIndices: identifier[],
  depth:number = 0
) {
  let next = traverseNextStrand(findBinder, treeRoot, t, freeVariableIndices)

  let indentLog = "  ".repeat(depth)

  if(next.length > 0) {
    // external variable with multiple non-deterministic choices
    verbose && console.log(indentLog + "|Depth:" + depth + "|External variable reached with " + next.length + " branch(es):" + printSequence(t, freeVariableIndices))
    for (let o of next) {
      let t2: JustSeq<T> = t.concat(o)
      verbose && console.log(indentLog + "|Depth:" + depth + "|Choice:" + o.justifier.label + "|Traversal: " + printSequence(t, freeVariableIndices) + " |Occurrence: " + printOccurrence(t2, o, t.length, freeVariableIndices))
      enumerateAllTraversals(findBinder, treeRoot, t2, freeVariableIndices, depth+1)
    }
  } else {
    console.log(indentLog + "|Depth:" + depth + "|Maximal traversal:" + printSequence(t, freeVariableIndices))
    let p = Array.from(coreProjection(t))
    p.reverse()
    console.log(indentLog + "|      " + ' '.repeat(depth.toString().length) + "        projection:" + printSequence(p, freeVariableIndices))
  }
}

/// Evaluate the term with term tree root treeRoot
fn evaluate<T extends NameLookup>(
  findBinder: LocateBinder<T>,
  term: Abs<T>
) {
  println!("Traversing {}", printLambdaTerm(term, false).prettyPrint)
  enumerateAllTraversals(findBinder, term, [], [])
}

console.log("===== Enumerating all traversals")
evaluate(Identifier_findBinder, neil)


/// Evaluate and readout the **name-free** normal-form.
/// This 'read-out' implementation produces an AST with DeBruijn variable references (rather than identifiers).
/// Variable name collision can occur if pretty-printing the term by just looking up variable name
/// without displaying the associated deBruijn pairs.
fn evaluateAndReadout<T extends NameLookup>(
  findBinder: LocateBinder<T>,
  root:Abs<T>,
  freeVariableIndices: identifier[] = []
) : [Abs<DeBruijnPair>, identifier[]]
{
  println!("Evaluating {}", printLambdaTerm(root, false, freeVariableIndices).prettyPrint)

  /// Read out the subterm at ending at the last node of traversal t
  fn readout(
      // A strand-complete traversal
      t: JustSeq<T>,
      depth: number
  ): Abs<DeBruijnPair> {
    traverseNextStrand<T>(findBinder, root, t, freeVariableIndices)

    // get the last two nodes from the core projection
    var p = coreProjection(t)
    // The strand ends with an external variable, call it x
    let strandEndVar = p.next().value as VarOccurrence<T>
     // The strand starts with an external lambda, call it \lambda y1 .... y_n
    let strandBeginAbs = p.next().value as AbsOccurrence<T>

    let argumentOccurrences = newStrandOpeningOccurrences(t, strandEndVar)
    if (argumentOccurrences.length == 0) {
      verbose && console.log("Strand ended|Maximal    |Depth:" + depth + "|Traversal: " + printSequence(t, freeVariableIndices))
    } else {
      verbose && console.log("Strand ended|Not maximal|Depth:" + depth + "|Traversal: " + printSequence(t, freeVariableIndices))
    }

    return {
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

  return [readout([], 0), freeVariableIndices]
}

fn evaluateAndPrintNormalForm(term: Abs<identifier>) {
  let [readout, freeVariableIndices] = evaluateAndReadout(Identifier_findBinder, term)
  console.log(printLambdaTerm(readout, false, freeVariableIndices).prettyPrint)
}

/*

console.log("===== Evaluation without name resolution")
evaluateAndPrintNormalForm(neil)
evaluateAndPrintNormalForm(varityTwo)


/// Pretty-printing of both AST type should produce the same output
function test(term: Abs<identifier>) {
  let [readout1, freeVariableIndices1] = evaluateAndReadout(Identifier_findBinder, term)
  let n1 = printLambdaTerm(readout1, true, freeVariableIndices1).prettyPrint
  console.log("n1: " + n1)

  var freeVariableIndex2: identifier[] = []
  var term2 = toDeBruijnAST(term, [], freeVariableIndex2)
  let [readout2, _] = evaluateAndReadout(DeBruijnPair_findBinder, term2, freeVariableIndex2)
  let n2 = printLambdaTerm(readout2, true, freeVariableIndex2).prettyPrint
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
  freeVariableIndices:identifier[],
  // The list of binders from the root to the last node of t
  // this array gets mutated as bound variable names get renamed to avoid name collision
  // when replacing DeBruijn pairs by variable names.
  bindersFromRoot: (Abs<DeBruijnPair>| GhostAbsNode)[] //= []
  ) :Abs<identifier>
{
  let getBindingIndex = (node: Abs<DeBruijnPair> | GhostAbsNode, variableName: identifier) => node.boundVariables.indexOf(variableName)
  let isBoundByAbsNode = (node: Abs<DeBruijnPair> | GhostAbsNode, variableName: identifier) => getBindingIndex(node, variableName) >= 0

  function nameAlreadyUsedAbove (suggestedName:identifier, binderNameIndex:number) {
    let freeVariableWithSameName = freeVariableIndices.indexOf(suggestedName)>=0

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
            let overArcingVariableAssignedName = adjustedDeBruijn.lookupBinderAndName(bindersFromRoot, freeVariableIndices).name

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
        operator: resolveNameAmbiguity(binderNode.body.operator, freeVariableIndices, bindersFromRoot),
        operands: binderNode.body.operands.map(a => resolveNameAmbiguity(a, freeVariableIndices, bindersFromRoot))
    }
  } else { // if(root.body.kind == "Var") {
    let assignedVariableName = binderNode.body.name.lookupBinderAndName(bindersFromRoot, freeVariableIndices).name
    bodyWithVariableNamesAssigned = {
      kind: "Var",
      name: assignedVariableName,
      arguments: binderNode.body.arguments.map(a => resolveNameAmbiguity(a, freeVariableIndices, bindersFromRoot))
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
  let [readout, freeVariableIndices] = evaluateAndReadout(Identifier_findBinder, term)
  let resolvedNameReadout = resolveNameAmbiguity(readout, freeVariableIndices, [])
  console.log(printLambdaTerm(resolvedNameReadout, false, freeVariableIndices).prettyPrint)
}

console.log("===== Evaluation with name-preserving resolution")
evaluateResolveAndPrintNormalForm(neil)
evaluateResolveAndPrintNormalForm(varityTwo)

*/
*/