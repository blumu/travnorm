/// if true then print additional logging
let verbose = false
/// If true then print out the deBruijn pairs even for non-ghost variables when reading-out sequences
let printDeBruijnPairs = true

/// Variable names
type identifier = string

////////////// Lambda term with alternating AST
/// The type T represents the type used to label variable nodes
/// It can be for instance just 'string' or a deBruijn index
type Var<T> = { kind: "Var", name: T, arguments: Abs<T>[] }
type App<T> = { kind: "App", operator: Abs<T>, operands: Abs<T>[] }
type Abs<T> = { kind: "Abs", boundVariables: identifier[], body: App<T> | Var<T> }

type LambdaAST<T> = Var<T> | App<T> | Abs<T>

/// To support pretty-printing, the type T must implement name lookup
interface NameLookup {
  // Given a list of binders occurring in the path from the root
  // to the variable node, return the name of the variable
  // If the type T encodes free variables with indices, then the map
  // 'freeVariableIndices' can be used to lookup free variable names for free variable indices
  lookup<T>(bindersFromRoot: Abs<T>[],
        freeVariableIndices:identifier[] // readonly
        ): string
}

/// Pretty-printing helper type
type Pretty =
  {
    prettyPrint: string
    mustBracketIfArgument: boolean
  }

function bracketize(t: Pretty): string {
  return t.mustBracketIfArgument ? '(' + t.prettyPrint + ')' : t.prettyPrint
}

function printLambdaTerm<T extends NameLookup>(
  r: Abs<T>,
  // optional array use to assign indices to free variables (used with the deBruijn encoding)
  freeVariableIndices:identifier[] = []
): Pretty {

  function printSubterm(
    t: LambdaAST<T>,
    bindersFromRoot: Abs<T>[]
  ): Pretty {
    switch(t.kind) {
    case "Var":
      return  {
        prettyPrint: (t.name.lookup(bindersFromRoot, freeVariableIndices))
                     + (t.arguments.length == 0
                        ? ''
                        : ' ' + t.arguments.map(x => bracketize(printSubterm(x, bindersFromRoot))).join(' ')),
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
              prettyPrint: '\lambda ' + t.boundVariables.join(' ') + '.' + bodyPrint.prettyPrint,
              mustBracketIfArgument: true
          }
    }
  }
  return printSubterm(r, [])
}

/////// Parsing combinators to easily define lambda-terms with AST of type Abs<identifier>

function isSingletonAST<T>(t: T | LambdaAST<T> | LambdaAST<T>[]): t is LambdaAST<T> {
  return (t as LambdaAST<T>).kind !== undefined
}
function isLambdaASTArray<T>(t: LambdaAST<T> | LambdaAST<T>[] | T): t is LambdaAST<T>[] {
  return (t as LambdaAST<T>[]).map !== undefined // this feels like a hack, cannot find a better way to do this than duck-type checking...
}
function isOfVariableNameType<T>(t: LambdaAST<T> | LambdaAST<T>[] | T): t is T {
  return !isSingletonAST(t) && !isLambdaASTArray(t)
}

function abs<T> (variables: identifier[], body: LambdaAST<T> | T): Abs<T> {
  let applicationBody: LambdaAST<T> = isOfVariableNameType(body) ? { kind: "Var", name: body, arguments: [] } : body

  return applicationBody.kind == "Abs"
    ? { kind: "Abs", boundVariables: variables.concat(applicationBody.boundVariables), body: applicationBody.body }
    : { kind: "Abs", boundVariables: variables, body: applicationBody }
}

function app<T> (operator: Abs<T> | T, operands: Abs<T> | Abs<T>[] | T = []): Abs<T> {
  let unappliedVar = (name: T): Abs<T> => { return { kind: "Abs", boundVariables: [], body: { kind: "Var", name: name, arguments: [] } } }

  let isDummy = (t: Abs<T>): boolean => t.boundVariables.length == 0

  // If operator is just an identifier then convert it into a variable node
  let operatorAsAbs: Abs<T> = isOfVariableNameType<T>(operator) ? unappliedVar(operator) : operator

  // If operand is just an identifier then convert it into a variable node
  let rands = isOfVariableNameType(operands) ? unappliedVar(operands) : operands

  // if single operand then make it into a singleton array
  let randsAsArray = isSingletonAST(rands) ? [rands] : rands

  if (isDummy(operatorAsAbs)) {
    return operatorAsAbs.body.kind == "App"
      // combine consecutive application
      ? { kind: "Abs", boundVariables: [], body: { kind: "App", operator: operatorAsAbs.body.operator, operands: operatorAsAbs.body.operands.concat(randsAsArray) } }
      // combine consecutive application
      : { kind: "Abs", boundVariables: [], body: { kind: "Var", name: operatorAsAbs.body.name, arguments: operatorAsAbs.body.arguments.concat(randsAsArray) } }
  } else {
    return { kind: "Abs", boundVariables: [], body: { kind: "App", operator: operatorAsAbs, operands: randsAsArray } }
  }
}

////////////////// Alternating-AST with variable named with string identifiers.

// An implementation of variable labels where the variable
// name is specified in every node of the tree
// by the name identifier itself
declare interface String {
  lookup<T>(bindersFromRoot: Abs<T>[], freeVariableIndices: identifier[]): string
}

String.prototype.lookup = function<T> (bindersFromRoot: Abs<T>[], freeVariableIndices: identifier[]) {
  // The name of the variable occurrence is just name identifier itself!
  return this.toString()
}

/// Alternating-AST with variable named with string identifiers
/// The alternating-AST of a lambda term always starts with a lambda node
type AltLambda = Abs<identifier>

//////////
/// Term examples

let identity = abs(['x'], 'x')
let delta = abs(['x'], app('x', 'x'))
var omega = app(delta, delta)

/// Neil Jones's example: J = (\u.u(x u))(\v.v y)
let neil =
  app(abs(['u'], app('u', app('x', 'u'))),
    abs(['v'], app('v', 'y')))

let varity =
  abs(['t'], app('t', [abs(['n', 'a', 'x'], app('n', abs(['s','z'], app('a', [ app('s'), app('x', [app('s'), app('z')])])))),
                      abs(['a'], 'a'),
                      abs(['z0'], 'z0')
                    ] ))

let two = abs(['s2', 'z2'], app('s2', app('s2', 'z2')))

let varityTwo = app(varity, two)

console.log(printLambdaTerm(identity).prettyPrint)
console.log(printLambdaTerm(omega).prettyPrint)
console.log(printLambdaTerm(neil).prettyPrint)
console.log(printLambdaTerm(varityTwo).prettyPrint)
//////////

function findLastIndex<T>(a: T[], condition: (element: T, index: number) => boolean): undefined | [number, T] {
  for (var i = a.length - 1; i >= 0; i--) {
    let e = a[i]
    if (condition(e, i)) {
      return [i, e]
    }
  }
  return undefined
}

/// A deBruijn-like encoding where the name of a variable occurrence
/// is defined by a pair of integers referencing to the lambda-binder
/// and the index of the name in the lambda-binder
class DeBruijnPair implements NameLookup {
  // Depth is the distance from the variable node to its binder node in the path to the tree root
  // (1 for the parent node, and so on)
  depth: number = 0
  // Index of the variable name in the lambda-binder
  index: number = 0

  constructor(depth:number, index:number) {
    this.depth = depth
    this.index = index
  }

  /// Lookup name of a bound variable.
  /// If the variable is bound, return the binder and the name of the variable ([Abs<DeBruijnPair>, identifier])
  /// If it's a free variable, return the name of the free variable (identifier)
  lookupBinderAndName<T>(
    bindersFromRoot: (Abs<T>|GhostAbsNode)[],
    freeVariableIndices: identifier[]
  ): { binder: Abs<T> | GhostAbsNode | undefined, name: identifier }
    {
    let binderIndex = bindersFromRoot.length - (this.depth + 1) / 2
    let binder = bindersFromRoot[binderIndex]
    let root = bindersFromRoot[0]
    let isBoundByRoot = binderIndex == 0
    let freeVariableIndex = this.index - root.boundVariables.length - 1
    if (isBoundByRoot && freeVariableIndex >= 0) {
      return { binder: undefined, name: freeVariableIndices[freeVariableIndex] }
    } else {
      let resolvedName =
        this.index > binder.boundVariables.length
        ?
        // unresolved ghost variable name (should never happen on core-projected traversals)
         '#(' + this.depth + ',' + this.index + ')'
        : binder.boundVariables[this.index - 1]
      return { binder: binder, name: resolvedName }
    }
  }

  lookup<T>(bindersFromRoot: Abs<T>[], freeVariableIndices: identifier[]): string {
    let binderAndName = this.lookupBinderAndName(bindersFromRoot, freeVariableIndices)
    return binderAndName.name + (printDeBruijnPairs ? '(' + this.depth + ',' + this.index + ')' : '')
  }

}

/// Convert an AST of type Abs<identifier> to an AST of type Abs<DeBruijnPair>
function toDeBruijnAST(
  /// the node of the alternating AST to convert
  node: Abs<identifier>,
  /// the list of binder nodes from the root
  bindersFromRoot: Abs<identifier>[],
  /// map that assigns an index to every free variable seen so far
  freeVariableIndices:identifier[]
): Abs<DeBruijnPair>
{
  var newBindersFromRoot = bindersFromRoot.concat([node])
  let VarOrApp_Node = () : Var<DeBruijnPair> | App<DeBruijnPair> =>
    {
      let bodyNode = node.body
      switch (bodyNode.kind) {
      case "Var":
        let variableName = bodyNode.name
        /// find the variable binder
        let binderLookup = findLastIndex(newBindersFromRoot, b => b.boundVariables.indexOf(variableName) >= 0)

        var binder : DeBruijnPair
        if (binderLookup !== undefined) {
          let [binderIndex, b] = binderLookup
          let binderDistance = newBindersFromRoot.length - binderIndex
          binder = new DeBruijnPair(2 * binderDistance - 1, b.boundVariables.indexOf(variableName) + 1)
          verbose && console.log('bindersFromRoot:' + newBindersFromRoot.map(x => '[' + x.boundVariables.join(' - ') + ']').join('\\') + ' varName:' + variableName + ' binderIndex:' + binderIndex + ' depth:' + binder.depth + ' binderVarNames:' + b.boundVariables.join('-'))
        }
        // no binder -> x is a free variable and its enabler is the root
        else {
          let j = lookupOrCreateFreeVariableIndex(freeVariableIndices, variableName)
          let root = newBindersFromRoot[0]
          binder = new DeBruijnPair(2 * newBindersFromRoot.length - 1, root.boundVariables.length + j)
        }
        return {
          kind: "Var",
          name: binder,
          arguments: bodyNode.arguments.map(o => toDeBruijnAST(o, newBindersFromRoot, freeVariableIndices))
        }
      case "App":
        return {
          kind: "App",
          operator: toDeBruijnAST(bodyNode.operator, newBindersFromRoot, freeVariableIndices),
          operands: bodyNode.operands.map(o => toDeBruijnAST(o, newBindersFromRoot, freeVariableIndices))
        }
      }
    }
  return {
    kind: "Abs",
    boundVariables: node.boundVariables,
    body: VarOrApp_Node()
  }
}


console.log('Test printing a lambda term from the deBruijn AST')
printDeBruijnPairs = false
let d = printLambdaTerm(toDeBruijnAST(omega, [], [])).prettyPrint
let d2 = printLambdaTerm(omega).prettyPrint
printDeBruijnPairs = true
console.log(d)
console.log(d2)
if(d !== d2 ) {
  throw "Pretty printing should give the same result"
}

////////// Justified sequences

/// A justification pointer
type Pointer = {
  /// distance from the justifier in the sequence
  distance: number
  /// and pointer's label
  label: number
}

/// Ghosts variable node
type GhostVarNode  = {
  kind: 'GhostVar'
}

/// Ghost abstraction node
type GhostAbsNode = {
  kind: 'GhostAbs',
  /// list of bound variable names: not used for traversal but needed: for core projection calculation
  boundVariables: identifier[]
}

/// Occurrence of a ghosts variable node
type GhostVarOccurrence = {
  node: GhostVarNode
  /// Pointer to the justifying occurrence
  justifier: Pointer
}

/// Occurrence of a ghosts abstraction
type GhostAbsOccurrence = {
  node: GhostAbsNode,
  /// Pointer to the justifying occurrence
  justifier: Pointer
}

type GhostOccurrence = GhostVarOccurrence | GhostAbsOccurrence

type AbsOccurrence<T> = {
  node: Abs<T>
  /// Pointer to the justifying occurrence (of the parent-node)
  justifier: Pointer | "Initial"
}

type VarOccurrence<T> = {
  node: Var<T>
  /// Pointer to the justifying lambda-occurrence
  justifier: Pointer
}

type AppOccurrence<T> = {
  node: App<T>
}

type StructuralOccurrence<T> = AbsOccurrence<T> | VarOccurrence<T> | AppOccurrence<T>

/// Node scope
enum Scope {
  /// Internal node: nodes hereditarily enabled by an @-node
  Internal,
  /// External node: nodes hereditarily enabled by the tree root
  External
}

/// Cache the scope (external or internal) of the underlying node in the occurrence itself
/// (Note: the scope is recoverable from the hereditary justification of the occurrence in the sequence ).
type OccWithScope<N> = N & {
  scope: Scope
}

/// An node occurrence in a justified sequence
type Occurrence<T> = OccWithScope<GhostOccurrence | StructuralOccurrence<T>>

/// lookup the index assigned to a free variable, or create one if it is not defined yet
function lookupOrCreateFreeVariableIndex(freeVariableIndices: string[], variableName: string) {
  let j = freeVariableIndices.indexOf(variableName)
  return (j < 0)
    // create a fresh free variable name
    ? freeVariableIndices.push(variableName)
    : j + 1
}

function isAbstractionOccurrence<T>(n: Occurrence<T>): n is OccWithScope<AbsOccurrence<T> | GhostAbsOccurrence> {
  return n.node.kind == 'GhostAbs' || n.node.kind == 'Abs'
}
function isVariableOccurrence<T>(n: Occurrence<T>): n is OccWithScope<VarOccurrence<T> | GhostVarOccurrence> {
  return n.node.kind == 'GhostVar' || n.node.kind == 'Var'
}
function isApplicationOccurrence<T>(n: Occurrence<T>): n is OccWithScope<AppOccurrence<T>> {
  return n.node.kind == 'App'
}
function isStructuralOccurrence<T>(t: Occurrence<T>): t is OccWithScope<StructuralOccurrence<T>> {
  return t.node.kind !== 'GhostVar' && t.node.kind !== 'GhostAbs'
}

function isInternal<T> (o: Occurrence<T>) { return o.scope == Scope.Internal }
function isExternal<T> (o: Occurrence<T>) { return o.scope == Scope.External }

/// A justified sequence of node occurrences
type JustSeq<T> = Occurrence<T>[]

/// Iterate over the P-view of a justified sequence
/// Return the sequence of occurrence in the P-view (read backwards)
/// together with the position deltas between consecutive occurrences in the P-view
function* pview<T>(t: JustSeq<T>): IterableIterator<[Occurrence<T>, number]> {
  var i = t.length-1
  while(i>=0){
    let lastOccurrence = t[i]

    let k = 1
    if (isVariableOccurrence(lastOccurrence)
    || isApplicationOccurrence(lastOccurrence)) {
      k = 1
    } else if (isAbstractionOccurrence(lastOccurrence)) {
      if (lastOccurrence.justifier == "Initial") {
        return // initial node => end of P-view
      } else {
        k = lastOccurrence.justifier.distance
      }
    }
    yield [lastOccurrence, k]
    i -= k
  }
}

/// Arity of a node occurrence
function arity<T>(o: GhostOccurrence | StructuralOccurrence<T>) : number {
  switch (o.node.kind) {
    case "GhostAbs":
    case "GhostVar":
      return 0
    case "App":
      return o.node.operands.length
    case "Var":
      return o.node.arguments.length
    case "Abs":
      return o.node.boundVariables.length
  }
}

/// Dynamic arity of a traversal (ending with an external variable)
function dynamicArity<T>(t: JustSeq<T>) : number {
  var i = t.length - 1
  var sum = arity(t[i])
  var max = sum
  i--;
  while (i >= 0) {
    let o = t[i]
    if (isAbstractionOccurrence(o)) {
      if (isExternal(o)) {
        return max
      } else {
        sum -= arity(o)
      }
    } else if (isVariableOccurrence(o) || isApplicationOccurrence(o)) {
      sum += arity(o)
      max = Math.max(sum, max)
    }
    i--
  }
  return max
}

/// childIndex ranges from
///   1 to arity(x) for a variable-node
///   0 to arity(x) for an @-node
function childOf<T>(o: (GhostVarOccurrence | VarOccurrence<T> | AppOccurrence<T>), childIndex: number): Abs<T> | GhostAbsNode {
  switch (o.node.kind) {
  case "GhostVar":
    return { kind: "GhostAbs", boundVariables: [] }
  case "Var":
    return childIndex <= arity(o)
      ? o.node.arguments[childIndex-1]
      : { kind: "GhostAbs", boundVariables: [] }
  case "App":
    return (childIndex == 0) ? o.node.operator :
      childIndex <= arity(o)
        ? o.node.operands[childIndex-1]
        : { kind: "GhostAbs", boundVariables: [] }
  }
}

function createOccurrenceOfChildOf<T>(
  /// occurrence of the parent node
  m: OccWithScope<GhostVarOccurrence | VarOccurrence<T> | AppOccurrence<T>>,
  /// child index defining the node to create an occurrence of
  childIndex: number,
  /// distance from the occurrence of the node m in the sequence
  distance: number
  )
  : OccWithScope<AbsOccurrence<T> | GhostAbsOccurrence>
{
  let child = childOf(m, childIndex)
  let o = {
    node: child,
    justifier: { distance: distance, label: childIndex },
    scope: m.scope
  }
  if (child.kind == "Abs") {
    return o as OccWithScope<AbsOccurrence<T>>
  } else {//if (child.label == "GhostAbs") {
    (o as OccWithScope<GhostAbsOccurrence>).node.boundVariables = []
    return o as OccWithScope<GhostAbsOccurrence>
  }
}

/// Return the list of possible occurrences opening up a new strand
/// in a strand-complete traversal
/// Returns void if the traversal is maximal
function newStrandOpeningOccurrences<T>(
  t: JustSeq<T>,
  lastOccurrence: OccWithScope<GhostVarOccurrence | VarOccurrence<T>>
): OccWithScope<GhostAbsOccurrence | AbsOccurrence<T>>[] {
  let da = dynamicArity(t)
  var possibleChildren =
      Array.apply(null, Array(da))
        .map((_, i) => createOccurrenceOfChildOf(lastOccurrence, i + 1, 1))
  return possibleChildren
}

////////// Traversals

/// To support traversals, the type T to encode variable labels
// must support the LocateBinder interface
interface LocateBinder extends NameLookup {
  /// Locate the binder occurrence from the P-view
  /// at an occurrence of a variable node with label encoded by type T
  /// The P-view (which represents the path from the variable node to the tree root, see paper)
  //  is provided as an iterable that enumerates backwards
  /// the occurrence in the P-view.
  /// The function must return a justification pointer to the occurrence of the binder
  findBinder<T>(
    pview: IterableIterator<[Occurrence<T>, number]>,
    freeVariableIndices: identifier[]): Pointer
}

// Implement interface LocateBinder for AST where the variable labels
// are encoded as simple name identifiers (string)
declare interface String {
  findBinder<T>(
    pview: IterableIterator<[Occurrence<T>, number]>,
    freeVariableIndices: identifier[]): Pointer
}
/// When using name identifier, the binder is the first lambda node
/// in the P-view binding that particular variable name.
/// If no such occurrence exists then it's a free variable
/// (justified by the tree root--the initial node occurrence in the P-view)
String.prototype.findBinder = function<T> (
  pview: IterableIterator<[Occurrence<T>, number]>,
  freeVariableIndices: identifier[]
) {
  let variableName = this.toString()
  // read the P-view backward and stop at the first binder containing the variable name
  let d = 1
  for (let [b, _] of pview) {
    if(isAbstractionOccurrence(b)) {
      let i = b.node.boundVariables.indexOf(variableName)
      if(i>-1) {
        return { distance: d, label: i+1 }
      }
      d+= b.justifier == "Initial" ? 0 : b.justifier.distance
    } else {
      d++
    }
  }
  // no binder found: it's a free variable
  return { distance: d, label: lookupOrCreateFreeVariableIndex(freeVariableIndices, variableName) }
}

declare interface DeBruijnPair {
  findBinder<T>(
    pview: IterableIterator<[Occurrence<T>, number]>,
    freeVariableIndices: identifier[]): Pointer
}
/// When encoding variable labels as DeBruijnPair, the
/// binder is given by walking back the P-view (path to the root)
/// and stopping after 'depth' number of occurrences, where
/// 'depth' is the deBruijn static depth (i.e. the number of nodes separating
/// the variable from its 'enabler' in the tree)
DeBruijnPair.prototype.findBinder = function<T>(
  pview: IterableIterator<[Occurrence<T>, number]>,
  freeVariableIndices: identifier[]
) {
  let enablerDepth: number = this.depth
  var distance = 1
  for (let [_,d] of pview) {
    enablerDepth--
    if (enablerDepth <= 0) {
      break;
    }
    distance += d
  }
  return { distance: distance, label: this.index }
}

type Extension<T> = Occurrence<T> | (OccWithScope<AbsOccurrence<T>|GhostAbsOccurrence>)[]

function isDeterministic<T>(e: Extension<T>): e is Occurrence<T> {
  return (e as Occurrence<T>) !== undefined && (e as Occurrence<T>).node !== undefined
}

/// Extend a traversal using the traversal rules of the 'normalizing traversals' from the paper
/// The input traversal is not modified, instead it returns the list of possibles node occurrences
/// to traverse, or just void if the traversal is maximal
function extendTraversal<T extends LocateBinder>(
  treeRoot: Abs<T>, t: JustSeq<T>,
  freeVariableIndices: identifier[]
): Extension<T>
{
  let nextIndex = t.length
  let lastIndex = t.length-1
  let lastOccurrence = t[lastIndex]

  if (lastOccurrence === undefined) { /// Empty sequence?
    return {
      node: treeRoot,
      justifier: "Initial",
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
      let m = t[nextIndex - distance] as OccWithScope<VarOccurrence<T> | GhostVarOccurrence | AppOccurrence<T>>
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
          justifier: "Initial",
          scope: Scope.Internal
        }
      } else {
        let pointer = bodyNode.name.findBinder(pview(t), freeVariableIndices)

        let m = t[nextIndex - pointer.distance] // if d= 1 then the justifier is the last occurrence
        return {
          node: bodyNode, // traverse the body of the lambda
          justifier: {
            distance: pointer.distance,
            label: pointer.label
          },
          scope: m.scope
        }
      }
    } else { /// Traverse the child of the ghost lambda node
      let m = t[lastIndex-lastOccurrence.justifier.distance]

      let justifierDistance = lastOccurrence.justifier.distance + 2
      let mu = t[nextIndex - justifierDistance]
      let i = lastOccurrence.justifier.label
      verbose && console.log('m:' + arity(m) + ', mu:' + arity(mu) + ', i:' + i)
      return {
        node: { kind : "GhostVar"},
        justifier : { distance: justifierDistance,
                      label: arity(mu) + i - arity(m) },
        scope : mu.scope
      }
    }
  }
}

function printPointer(j:Pointer|"Initial") {
  return (j == "Initial") ? '' : '('+j.distance+','+j.label+')'
}

function printOccurrence<T>(t: JustSeq<T>, o: Occurrence<T>, index: number, freeVariableIndex: identifier[]) : string {
  if(isStructuralOccurrence(o)){
    if(isAbstractionOccurrence(o)) {
      return '[' + o.node.boundVariables.join(' ') + ']' + printPointer(o.justifier)
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
      return '$[' + o.node.boundVariables + ']' + printPointer(o.justifier)
    } else {
      return '#' + printPointer(o.justifier)
    }
  }
}

function printSequence<T>(t: JustSeq<T>, freeVariableIndex:identifier[]) {
  return t.map((o, i) => printOccurrence(t, o, i, freeVariableIndex)).join('--')
}

/// core projection
function* coreProjection<T>(t: JustSeq<T>) {
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

function enumerateAllTraversals<T extends LocateBinder>(treeRoot: Abs<T>, t: JustSeq<T>, freeVariableIndices: identifier[]) {
  while(true) {
    var next = extendTraversal(treeRoot, t, freeVariableIndices)
    if(isDeterministic(next)) {
      t.push(next) // append the traversed occurrence
      verbose && console.log("extended:" + printSequence(t, freeVariableIndices))
    } else if (next.length == 0) {
      console.log("Maximal traversal reached:" + printSequence(t, freeVariableIndices))
      let p = Array.from(coreProjection(t))
      p.reverse()
      console.log("               projection:" + printSequence(p, freeVariableIndices))
      return t
    } else {
      /// external variable with multiple non-deterministic choices
      verbose && console.log("External variable reached with " + next.length + " branch(es):" + printSequence(t, freeVariableIndices))
      for(let o of next) {
        verbose && console.log("non-det-before:" + printSequence(t, freeVariableIndices))
        let t2: JustSeq<T> = t.concat(o)
        verbose && console.log("chose " + (printPointer(o.justifier) + ":" + printSequence(t2, freeVariableIndices)))
        enumerateAllTraversals(treeRoot, t2, freeVariableIndices)
      }
      return
    }
  }
}

/// Evaluate the term with term tree root treeRoot
function evaluate<T extends LocateBinder>(term: Abs<T>) {
  console.log('Traversing ' + printLambdaTerm(term).prettyPrint)
  var freeVariableIndex: identifier[] = []

  enumerateAllTraversals(term, [], freeVariableIndex)
}

evaluate(neil)

/// Traverse a traversal until the next strand
/// Return false if the input traversal is maximal
function traverseNextStrand<T extends LocateBinder>(treeRoot: Abs<T>, t: JustSeq<T>, freeVariableIndices: identifier[]) {
  var next = extendTraversal(treeRoot, t, freeVariableIndices)
  while (isDeterministic(next)) {
    t.push(next) // append the traversed occurrence
    verbose && console.log("extended:" + printSequence(t, freeVariableIndices))
    next = extendTraversal(treeRoot, t, freeVariableIndices)
  }
  return next.length>0
}

/// Evaluate and readout the **name-free** normal-form.
/// This 'read-out' implementation produces an AST with DeBruijn variable references (rather than identifiers).
/// Variable name collision can occur if pretty-printing the term by just looking up variable name
/// without displaying the associated deBruijn pairs.
function evaluateAndReadout<T extends LocateBinder>(
  root:Abs<T>,
  freeVariableIndices: identifier[] = []
) : [Abs<DeBruijnPair>, identifier[]]
{
  console.log('Evaluating ' + printLambdaTerm(root, freeVariableIndices).prettyPrint)

  /// Read out the subterm at ending at the last node of traversal t
  function readout(
      // A strand-complete traversal
      t: JustSeq<T>): Abs<DeBruijnPair> {
    traverseNextStrand<T>(root, t, freeVariableIndices)

    // get the last two nodes from the core projection
    var p = coreProjection(t)
    // The strand ends with an external variable, call it x
    let strandEndVar = p.next().value as OccWithScope<VarOccurrence<T> | GhostVarOccurrence>
     // The strand starts with an external lambda, call it \lambda y1 .... y_n
    let strandBeginAbs = p.next().value as OccWithScope<AbsOccurrence<T> | GhostAbsOccurrence>

    let argumentOccurrences = newStrandOpeningOccurrences(t, strandEndVar)
    if (argumentOccurrences.length == 0) {
      verbose && console.log("maximal traversal reached:" + printSequence(t, freeVariableIndices))
    } else {
      verbose && console.log("end of strand: external variable reached" + printSequence(t, freeVariableIndices))
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
          arguments: argumentOccurrences.map(o => readout(t.concat(o)))
        }
    }
  }

  return [readout([]), freeVariableIndices]
}

function evaluateAndPrintNormalForm(term: Abs<identifier>) {
  let [readout, freeVariableIndices] = evaluateAndReadout(term)
  console.log(printLambdaTerm(readout, freeVariableIndices).prettyPrint)
}

evaluateAndPrintNormalForm(neil)

evaluateAndPrintNormalForm(varityTwo)

/// Pretty-printing of both AST type should produce the same output
function test(term: Abs<identifier>) {
  let [readout1, freeVariableIndices1] = evaluateAndReadout(term)
  let n1 = printLambdaTerm(readout1, freeVariableIndices1).prettyPrint
  console.log('n1: ' + n1)

  var freeVariableIndex2: identifier[] = []
  var term2 = toDeBruijnAST(term, [], freeVariableIndex2)
  let [readout2, _] = evaluateAndReadout(term2, freeVariableIndex2)
  let n2 = printLambdaTerm(readout2, freeVariableIndex2).prettyPrint
  console.log('n2: ' + n2)

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
  let [readout, freeVariableIndices] = evaluateAndReadout(term)
  let resolvedNameReadout = resolveNameAmbiguity(readout, freeVariableIndices, [])
  console.log(printLambdaTerm(resolvedNameReadout, freeVariableIndices).prettyPrint)
}

evaluateResolveAndPrintNormalForm(neil)

evaluateResolveAndPrintNormalForm(varityTwo)


/// NOTES and REMARKS:
///
/// - IDEA: pointer is not needed for free variable occurrences!
///   Pointer to the tree node suffice! Could simplify traversal
///   implementation even further by introducing a new type FreeVarOccurrence<T> with no pointer

////// Tests cases:
//
// lambda x.x
// (lambda x.x x)(lambda x.x x)
// (lambda u.u (x u))(lambda v.v y)

// Test printing a lambda term from the deBruijn AST
// (lambda x.x x)(lambda x.x x)

// Traversing (lambda u.u (x u))(lambda v.v y)
// Maximal traversal reached:[]--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)--[](1,1)--u(7,1)--[v](9,1)--v(1,1)--$[](3,1)--#(5,1)--$[](1,1)--#(3,1)--[](5,1)--y(17,2)
//                projection:[]--x(1,1)--[v](1,1)--#(1,1)--$[](1,1)--y(5,2)
// Maximal traversal reached:[]--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)--$[](1,2)--#(3,1)--[](5,1)--y(11,2)
//                projection:[]--x(1,1)--$[](1,2)--y(3,2)

// Evaluating (lambda u.u (x u))(lambda v.v y)x (lambda v.v y) y
// x(lambda v.v y) y

// Evaluating (lambda t.t (lambda n a x.n (lambda s z.a s (x s z))) (lambda a.a) (lambda z0.z0))(lambda s2 z2.s2 (s2 z2))
// lambda x x s z.s (x s (x s z))