use crate::ast::{LmdTerm, App, Abs, Var};

// if true then print additional logging
const verbose :bool = false;

// if true print traversal after every single extension
const veryVerbose :bool = false;

////////// Justified sequences

type Identifier = String;

/// Ghosts variable node
struct GhostVarNode {
}

/// Ghost abstraction node
struct GhostAbsNode {
  /// List of bound variable names: always empty in a traversal, but needed for the core projection calculation
  bound_variables : Vec<Identifier>
}

/// Generalizing the concept of node or occurrences.
/// Type `S` represents a 'structural' form
/// Type `G` represents a 'ghost' form
enum Generalized<S, G> {
  Structural(S),
  Ghost(G)
}

/// A generalized abstraction node (i.e. either structural or ghost lambda node)
type GeneralizedAbsNode<T> = Generalized<AbsNode<T>, GhostAbsNode>;

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
enum Scope { Internal, External }


trait Justification {
  fn justifier(&self) -> Option<Pointer>;
}

/// An occurrence of a node of type N (without justification pointer)
struct NodeOccurrence<N> {
   node : N
}

/// Occurrence with a justification pointer.
///   - For a lambda-node distinct from the root: points to its parent-node
///   - For an internal variable: point to the occurrence of the lambda-node in the P-view binding the variable.
///
/// We cache the scope (external or internal) of the underlying node in the occurrence itself
/// (The scope is recoverable from the hereditary justification of the occurrence in the sequence.)
struct JustifiedOccurrence<N> {
  node : N,
  justifier : Pointer,
  scope : &mut Scope
}

// impl<N> Justification for JustifiedOccurrence<N> {
//   fn justifier(&self) -> Option<Pointer> {
//     Some (self.justifier)
//   }
// }

enum StructuralAbsOccurrence<T> {
  NonInit(JustifiedOccurrence<Abs<T>>),
  Init(NodeOccurrence<Abs<T>>)
}

// impl<T> Justification for StructuralAbsOccurrence<T> {
//   fn justifier(&self) -> Option<Pointer> {
//     match self {
//       StructuralAbsOccurrence::Init(_) => None,
//       StructuralAbsOccurrence::NonInit(j) => j.justifier()
//     }
//   }
// }

type AppOccurrence<T> = NodeOccurrence<App<T>>;

enum StructuralOccurrence<T> {
  Abs(StructuralAbsOccurrence<T>),
  Var(JustifiedOccurrence<Var<T>>),
  App(AppOccurrence<T>)
}


type GeneralizedAbsNode<T> = Generalized<AbsNode<T>, GhostAbsNode>;

/// A generalized occurrence of an abstraction node is either
/// - an occurrence of a structural lambda node
/// - an justified occurrence of a ghost lambda node
type AbsOccurrence<T> = Generalized<StructuralAbsOccurrence<T>, JustifiedOccurrence<GhostAbsNode>>;


// impl<T> Justification for AbsOccurrence<T> {
//   fn justifier(&self) -> Option<Pointer> {
//     match self {
//       AbsOccurrence::Structural(j) => j.justifier(),
//       AbsOccurrence::Ghost(j) => j.justifier()
//     }
//   }
// }


/// A generalized occurrence of a variable node is either
/// - an occurrence of a structural variable node
/// - an justified occurrence of a ghost variable node
type VarOccurrence<T> = Generalized<Var<T>, JustifiedOccurrence<GhostVarNode>>;

/// Occurrence of a node in a justified sequence
enum Occurrence<T> {
   Abs(AbsOccurrence<T>),
   Var(VarOccurrence<T>),
   App(AppOccurrence<T>)
}

/// A generalized lambda node is either
/// - a structural lambda node
/// - a ghost lambda  node
type AbsStructuralOrGhost<T> = Generalized<Abs<T>, GhostAbsNode>;


enum Extension<T> {
   Single(Occurrence<T>),
   Choice(Vec<JustifiedOccurrence<AbsStructuralOrGhost<T>>>)
}

fn isAbstractionOccurrence<T>(o: Occurrence<T>) -> bool {
  match o {
    Occurrence::Abs(_) => true,
    _ => false
  }
}

fn isVariableOccurrence<T>(o: Occurrence<T>) -> bool {
  match o {
    Occurrence::Var(_) => true,
    _ => false
  }
}

fn isApplicationOccurrence<T>(o: Occurrence<T>) -> bool {
  match o {
    Occurrence::App(_) =>  true,
    _ => false
  }
}

fn isStructuralOccurrence<T>(o: Occurrence<T>) -> bool {
  match o {
    Occurrence::Var(Generalized::Structural(_))
    | Occurrence::Abs(Generalized::Structural(_))
    | Occurrence::App(_) => true,
    _ => false
  }
}

fn isInitialOccurrence<T>(o: Occurrence<T>) -> bool {
  match o {
    Occurrence::Abs(Generalized::Structural(StructuralAbsOccurrence::Init(_)))
    | Occurrence::App(_) => true,
    _ => false
  }
}

fn scopeFromOccurrence<T> (o: Occurrence<T>) -> Scope {
   match o {
    Occurrence::App(_) => Scope::Internal,

    Occurrence::Abs(Generalized::Structural(StructuralAbsOccurrence::Init(_))) => Scope::External,
    Occurrence::Abs(Generalized::Structural(StructuralAbsOccurrence::NonInit(jo))) => jo.scope,
    Occurrence::Abs(Generalized::Ghost(jo)) => jo.scope,

    Occurrence::Var(Generalized::Structural(o)) => o.scope,
    Occurrence::Var(Generalized::Ghost(o)) => o.scope,
  }
}

fn isInternal<T>(o: Occurrence<T>) -> bool {
  return scopeFromOccurrence(o) == Scope::Internal
}

fn isExternal<T>(o: Occurrence<T>) -> bool {
  return scopeFromOccurrence(o) == Scope::External
}

/// A justified sequence of node occurrences
type JustSeq<T> = Vec<Occurrence<T>>;


pub fn length<T> (t:LmdTerm<T>) -> i32 {
  match t {
    LmdTerm::Variable(_) => 1,

    LmdTerm::App((u, v)) => 1 + length(*u) + length(*v),

    LmdTerm::Abs((_, body)) => length(*body)
  }
}


/// State of a P-view iterator
struct PviewIteration<T> {
  current_pos : usize,
  t: JustSeq<T>,
}

/// Iterate backward over the P-view of a justified sequence
impl<T> Iterator for PviewIteration<T> {
  type Item = (Occurrence<T>, usize);

  fn next(&mut self) -> Option<(Occurrence<T>, usize)> {
    let i = self.current_pos;

    if i>=0 {
      let lastOccurrence = self.t[i];

      let k =
        match lastOccurrence {
          Occurrence::Var(_) | Occurrence::App(_)
            => 1,

          Occurrence::Abs(Generalized::Structural(StructuralAbsOccurrence::Init(_)))
            => return None, // initial node => end of P-view

          Occurrence::Abs(Generalized::Structural(StructuralAbsOccurrence::NonInit(a)))
            => a.justifier.distance,

          Occurrence::Abs(Generalized::Ghost(g))
            => g.justifier.distance,

        };

      self.current_pos -= k;
      Some ((lastOccurrence, k))
    } else {
      None
    }
  }
}

/// Iterate over the P-view of a justified sequence.
///
/// Return the sequence of occurrence in the P-view (read backwards)
/// together with the position deltas between consecutive occurrences in the P-view
fn pview<T>(t: JustSeq<T>) {
  PviewIteration { current_pos : t.len()-1, t : t}
}

/// Arity of a node occurrence
fn arity<T>(o: Occurrence<T>) -> i32 {
  match o {
    Var(Ghost(_)) |
    Abs(Ghost(_)) => 0,

    Var(Structural(o)) => o.node.arguments.length,
    Abs(Structural(o)) => o.node.boundVariables.length,

    App(o) => o.node.operands.length
  }
}

/// Dynamic arity of a traversal (ending with an external variable)
fn dynamicArity<T>(t: JustSeq<T>) -> i32 {
  let mut i = t.length - 1;
  let sum = arity(t[i]);
  let mut max = sum;
  i = i-1;
  while (i >= 0) {
    let o = t[i];
    if (isAbstractionOccurrence(o)) {
      if (isExternal(o)) {
        return max
      } else {
        sum -= arity(o)
      }
    } else if (isVariableOccurrence(o) || isApplicationOccurrence(o)) {
      sum += arity(o);
      max = Math.max(sum, max)
    }
    i = i-1;
  };
  max
}

/// childIndex ranges from
///   1 to arity(x) for a variable-node
///   0 to arity(x) for an @-node
fn childOf<T>(o: VarOccurrence<T> | AppOccurrence<T>, childIndex: number) -> Abs<T> | GhostAbsNode {
  switch (o.node.kind) {
  GhostVarNode =>
    return GhostAbsNode { boundVariables: [] }
  case "Var":
    return childIndex <= arity(o)
      ? o.node.arguments[childIndex-1]
      : GhostAbsNode { boundVariables: [] }
  case "App":
    return (childIndex == 0) ? o.node.operator :
      childIndex <= arity(o)
        ? o.node.operands[childIndex-1]
        : GhostAbsNode { boundVariables: [] }
  }
}

fn createOccurrenceOfChildOf<T>(
  /// occurrence of the parent node
  m: VarOccurrence<T> | AppOccurrence<T>,
  /// child index defining the node to create an occurrence of
  childIndex: number,
  /// distance from the occurrence of the node m in the sequence
  distance: number
  )
  -> JustifiedOccurrence<Abs<T> | GhostAbsNode>
{
  let c : Abs<T> | GhostAbsNode = childOf(m, childIndex)
  let justifier = { distance: distance, label: childIndex }
  let scope = scopeFromOccurrence(m)
  // The common sub-expression below cannot be simplified due to
  // TypeScript type checker inability to distribute generic types
  return (c.kind == "Abs")
    ? { node: c, justifier: justifier, scope: scope }
    : { node: c, justifier: justifier, scope: scope }
}

/// Return the list of possible occurrences opening up a new strand
/// in a strand-complete traversal
/// Returns void if the traversal is maximal
fn newStrandOpeningOccurrences<T>(
  t: JustSeq<T>,
  lastOccurrence: VarOccurrence<T>
): (JustifiedOccurrence<Abs<T>> | JustifiedOccurrence<GhostAbsNode>)[] {
  let da = dynamicArity(t)
  var possibleChildren =
      Array.apply(null, Array(da))
        .map((_, i) => createOccurrenceOfChildOf(lastOccurrence, i + 1, 1))
  return possibleChildren
}



/// Extend a traversal by one more node
///
/// Arguments:
///   - `t` the current traversal
///   - `treeRoot` the root of the term tree
pub fn extend<T> (
    treeRoot:&LmdTerm<T> ,
    t:&JustSeq<T>,
    freeVariableIndices: Vec<String>
  ) -> Node {
  match t {
    LmdTerm::Variable(s) => 1,

    LmdTerm::App((u, v)) => 1 //+ traverse(*u) + traverse(*v),

    LmdTerm::Abs(names, body) => 0// traverse(*body)
  }
}

////////// Traversals

/// To support traversals for an AST with variable name references of type T,
/// a function of the following type must be implemented.
///
/// The P-view (which represents the path from the variable node to the tree root, see paper)
/// is provided as an iterable that enumerates backwards the occurrence in the P-view.
/// The function must locate the binder to the specified variable (with binding reference of type T)
/// and return a justification pointer to the occurrence of the binder.
type LocateBinder<T> = (variableNameReference:T, pview: IterableIterator<[Occurrence<T>, number]>, freeVariableIndices: identifier[]) => Pointer

/// Implement 'findBinder' for AST where the variable name references
/// are encoded as simple name identifiers (string)
///
/// With identifier names, the binder is the first lambda node
/// in the P-view binding that particular variable name.
/// If no such occurrence exists then it's a free variable
/// (justified by the tree root--the initial node occurrence in the P-view)
fn Identifier_findBinder<T> (
  variableName:identifier,
  pview: IterableIterator<[Occurrence<T>, number]>,
  freeVariableIndices: identifier[]
) {
  // read the P-view backward and stop at the first binder containing the variable name
  let d = 1
  for (let [b, _] of pview) {
    if(isAbstractionOccurrence(b)) {
      let i = b.node.boundVariables.indexOf(variableName)
      if(i>-1) {
        return { distance: d, label: i+1 }
      }
      d += isInitialOccurrence(b) ? 0 : b.justifier.distance
    } else {
      d++
    }
  }
  // no binder found: it's a free variable
  return { distance: d, label: lookupOrCreateFreeVariableIndex(freeVariableIndices, variableName) }
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

type Extension<T> = Occurrence<T> | (JustifiedOccurrence<Abs<T>> | JustifiedOccurrence<GhostAbsNode>)[]

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
    return {
      node: treeRoot,
      justifier : undefined,
      scope: Scope.External
    }
  } else if (isApplicationOccurrence(lastOccurrence) ){
    return {
      node: lastOccurrence.node.operator, // traverse the operator node
      justifier : { distance:1, label: 0 },
      scope: Scope.Internal
    }
  } else if (isVariableOccurrence(lastOccurrence)) {
    if (isInternal(lastOccurrence)) {
      // (Var) copy-cat rule
      let distance = 2+lastOccurrence.justifier.distance
      // Occurrence `m` from the paper, is the node preceding the variable occurrence's justifier.
      // Type assertion: by construction traversal verify alternation therefore m is necessarily a variable occurrence
      let m = t[nextIndex - distance] as VarOccurrence<T> | AppOccurrence<T>
      return createOccurrenceOfChildOf(m, lastOccurrence.justifier.label, distance)
    } else { /// external variable
      return newStrandOpeningOccurrences(t, lastOccurrence)
    }
  } else { // if (isAbstractionOccurrence(lastOccurrence)) {
    if(isStructuralOccurrence(lastOccurrence)) {
      let bodyNode = lastOccurrence.node.body
      if (bodyNode.kind == "App") {
        return {
          node: bodyNode, // traverse the body of the lambda
          scope: Scope.Internal,
          justifier: undefined
        }
      } else {
        let pointer = findBinder(bodyNode.name, pview(t), freeVariableIndices)

        let m = t[nextIndex - pointer.distance] // if d= 1 then the justifier is the last occurrence
        return {
          node: bodyNode, // traverse the body of the lambda
          justifier: {
            distance: pointer.distance,
            label: pointer.label
          },
          scope: scopeFromOccurrence(m)
        }
      }
    } else { /// Traverse the child of the ghost lambda node
      let m = t[lastIndex-lastOccurrence.justifier.distance]

      let justifierDistance = lastOccurrence.justifier.distance + 2
      let mu = t[nextIndex - justifierDistance]
      let i = lastOccurrence.justifier.label
      veryVerbose && console.log("[GhostAbs-arity] m:" + arity(m) + ", mu:" + arity(mu) + ", i:" + i)
      return {
        node: GhostVarNode,
        justifier : { distance: justifierDistance,
                      label: arity(mu) + i - arity(m) },
        scope: scopeFromOccurrence(mu)
      }
    }
  }
}

fn printPointer(p: Pointer) {
  return '(' + p.distance + ',' + p.label + ')'
}

fn printOccurrence<T>(t: JustSeq<T>, o: Occurrence<T>, index: number, freeVariableIndex: identifier[]) : string {
  if(isStructuralOccurrence(o)){
    if(isAbstractionOccurrence(o)) {
      return '[' + o.node.boundVariables.join(' ') + ']' + (isInitialOccurrence(o) ? "" : printPointer(o.justifier))
    } else if (isVariableOccurrence(o)) {
      let j = t[index - o.justifier.distance].node as Abs<T>
      let name =
        (o.justifier.label <= j.boundVariables.length)
        ? j.boundVariables[o.justifier.label - 1]
          : freeVariableIndex[o.justifier.label - 1 - j.boundVariables.length]
      return name + printPointer(o.justifier)
    } else { //if (isApplicationOccurrence(o)) {
      return '@'
    }
  } else { // ghost
    if(isAbstractionOccurrence(o)) {
      return "$[" + o.node.boundVariables + "]" + printPointer(o.justifier)
    } else {
      return '#' + printPointer(o.justifier)
    }
  }
}

fn printSequence<T>(t: JustSeq<T>, freeVariableIndex:identifier[]) {
  return t.map((o, i) => printOccurrence(t, o, i, freeVariableIndex)).join("--")
}

/// core projection
fn* coreProjection<T>(t: JustSeq<T>) {
  var pendingLambdas: identifier[] = []
  for (let i = t.length - 1; i >= 0; i--) {
    let o = t[i]
    if (isAbstractionOccurrence(o)) {
       if (isExternal(o)) {
         let cloneOccurrence = Object.assign({}, o)
         cloneOccurrence.node = Object.assign({}, o.node)
         cloneOccurrence.node.boundVariables = o.node.boundVariables.concat(pendingLambdas)
         yield cloneOccurrence
         pendingLambdas = []
       } else {
         pendingLambdas = o.node.boundVariables.concat(pendingLambdas)
       }
    } else if (isVariableOccurrence(o)) {
       if (isExternal(o)) {
         // patch link distance to account for removed occurrences
         var d = o.justifier.distance
         for (let j = i - d; j<i; j++) {
           if(isInternal(t[j])) {
             d--
           }
         }
         let cloneOccurrence = Object.assign({}, o)
         cloneOccurrence.justifier = { distance: d, label: o.justifier.label }
         yield cloneOccurrence
         pendingLambdas = []
       } else {
         pendingLambdas.splice(0, arity(o)) // pop arity(o) elements from the left of the array
       }
    } else if(isApplicationOccurrence(o)){
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
      // console.log("extended:" + printSequence(t, freeVariableIndices))
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
      verbose && console.log(indentLog + "|Depth:" + depth + "|Choice:" + o.justifier.label + "|Trav: " + printSequence(t, freeVariableIndices) + " |Occurrence: " + printOccurrence(t2, o, t.length, freeVariableIndices))
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
  function readout(
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
      verbose && console.log("Strand ended|Maximal    |Depth:" + depth + "|Trav: " + printSequence(t, freeVariableIndices))
    } else {
      verbose && console.log("Strand ended|Not maximal|Depth:" + depth + "|Trav: " + printSequence(t, freeVariableIndices))
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

function evaluateAndPrintNormalForm(term: Abs<identifier>) {
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