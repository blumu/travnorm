let verbose = false

/////////////// Variable names
type identifier = string

////////////// Lambda term with alternating AST
type Var = { kind: "Var", name: identifier, arguments: Abs[] }
type App = { kind: "App", operator: Abs, operands: Abs[] }
type Abs = { kind: "Abs", abs: identifier[], body: App | Var }

/// The alternating-AST of a lambda term always starts with a lambda node
type AltLambda = Abs

/// The three types of alternating-AST tree tokens
type AltNodes = Var | App | Abs

function isIdentifier(t: AltNodes | AltNodes[] | identifier): t is identifier { return (t as identifier).search !== undefined }
function isSingleton(t: AltNodes | AltNodes[]): t is AltNodes { return (t as AltNodes[]).length === undefined }

let abs = (variables: identifier[], body: App | Var | Abs | identifier): Abs =>
{
  let applicationBody: App | Abs | Var = isIdentifier(body) ? { kind: "Var", name: body, arguments: [] } : body

  return applicationBody.kind == "Abs"
    ? { kind: "Abs", abs: variables.concat(applicationBody.abs), body: applicationBody.body }
    : { kind: "Abs", abs: variables, body: applicationBody }
}

let app = (operator: Abs | identifier, operands: Abs | Abs[] | identifier): Abs =>
{
    let unappliedVar = (name: identifier): Abs => { return { kind: "Abs", abs: [], body: { kind: "Var", name: name, arguments: [] } } }

    let isDummy = (t: Abs): boolean => t.abs.length == 0

    // If operator is just an identifier then convert it into a variable node
    let rator: Abs = isIdentifier(operator) ? unappliedVar(operator) : operator

    // If operand is just an identifier then convert it into a variable node
    let rands = isIdentifier(operands) ? unappliedVar(operands) : operands

    // if single operand then make it into a singleton array
    let randsAsArray = isSingleton(rands) ? [rands] : rands

    if (isDummy(rator)) {
      return rator.body.kind == "App"
        // combine consecutive application
        ? { kind: "Abs", abs: [], body: { kind: "App", operator: rator.body.operator, operands: rator.body.operands.concat(randsAsArray) } }
        // combine consecutive application
        : { kind: "Abs", abs: [], body: { kind: "Var", name: rator.body.name, arguments: rator.body.arguments.concat(randsAsArray) } }
    } else {
      return { kind: "Abs", abs: [], body: { kind: "App", operator: rator, operands: randsAsArray } }
    }
}

/// Term examples
let identity: AltLambda = abs(['x'], 'x')
let delta: AltLambda = abs(['x'], app('x', 'x'))
var omega: AltLambda = app(delta, delta)

/// Neil Jones's example: J = (\u.u(x u))(\v.v y)
let neil: AltLambda =
  app(abs(['u'], app('u', app('x', 'u'))),
      abs(['v'], app('v', 'y')))
//////////


type Pretty =
  {
    prettyPrint: string
    mustBracketIfArgument: boolean
  }

function bracketize(t: Pretty): string {
  return t.mustBracketIfArgument ? '(' + t.prettyPrint + ')' : t.prettyPrint
}

function printLambdaTerm(t: AltNodes): Pretty {
  switch(t.kind) {
  case "Var":
    return  {
      prettyPrint: t.name + (t.arguments.length == 0 ? '' : ' ' + t.arguments.map(x => bracketize(printLambdaTerm(x))).concat()),
      mustBracketIfArgument: t.arguments.length > 0
    }
  case "App":
    return {
      prettyPrint: bracketize(printLambdaTerm(t.operator)) + t.operands.map(x => bracketize(printLambdaTerm(x))).concat(),
      mustBracketIfArgument: true
    }
  case "Abs":
    let bodyPrint = printLambdaTerm(t.body)
    return (t.abs.length == 0)
            ? {
                prettyPrint: bodyPrint.prettyPrint,
                mustBracketIfArgument: bodyPrint.mustBracketIfArgument
            }
            : {
                prettyPrint: '\lambda ' + t.abs.join(' ') + '.' + bodyPrint.prettyPrint,
                mustBracketIfArgument: true
            }
  }
}

console.log(printLambdaTerm(identity).prettyPrint)
console.log(printLambdaTerm(omega).prettyPrint)
console.log(printLambdaTerm(neil).prettyPrint)

/// A deBruijn-like representation of the lambda-term
/// where the name of a variable occurrence is defined by
/// a pair of integers referencing to the lambda-binder
/// and the index of the name in the lambda-binder
interface AbsTermNode {
  label: "Abs"
  boundVariables: identifier[]
  body: AppTermNode | VarTermNode
}

interface AppTermNode {
  label: "@"
  operator: AbsTermNode
  operands: AbsTermNode[]
}

interface VarTermNode {
  label: "Var"
  binder: {
    // Depth is the distance from the variable node to its binder node in the path to the tree root
    // (1 for the parent node, and so on)
    depth: number
    // Index of the variable name in the lambda-binder
    index: number
  }
  arguments: AbsTermNode[]
}


function findLastIndex<T>(a:T[], condition : (element:T, index:number) => boolean) : undefined | [number, T] {
  for (var i = a.length-1; i>=0; i--) {
    let e = a[i]
    if (condition(e, i)) {
      return [i, e]
    }
  }
  return undefined
}

function lambdaTermToDeBruijn_Abs(
    /// the node of the alternating AST to convert
    t:Abs,
    /// the list of binder nodes from the root
    bindersFromRoot: Abs[],
    /// map that assigns an index to every free variable seen so far
    freeVariableIndex:identifier[]
): AbsTermNode
{
  return {
    label : "Abs",
    boundVariables : t.abs,
    body: lambdaTermToDeBruijn_Var_App(t.body, bindersFromRoot.concat([t]), freeVariableIndex)
  }
}

function lambdaTermToDeBruijn_Var_App(
  /// the node of the alternating AST to convert
  t: Var | App,
  /// the list of binder nodes from the root
  bindersFromRoot: Abs[],
  /// map that assigns an index to every free variable seen so far
  freeVariableIndex: identifier[]
): AppTermNode | VarTermNode {
  switch (t.kind) {
  case "Var":
    let variableName = t.name
    /// find the variable binder
    let binderLookup = findLastIndex(bindersFromRoot, b => b.abs.indexOf(variableName) >= 0)

    var binder;
    if (binderLookup !== undefined) {
      let [binderIndex, b] = binderLookup
      let j = b.abs.indexOf(variableName)
      let binderDistance = bindersFromRoot.length - binderIndex
      binder = { depth: 2 * binderDistance - 1, index: j + 1 }
      verbose && console.log('bindersFromRoot:' + bindersFromRoot.map(x => '[' + x.abs.join(' - ') + ']').join('\\') + ' varName:' + variableName + ' binderIndex:' + binderIndex + ' j:' + j + ' depth:' + binder.depth + ' binderVarNames:' + b.abs.join('-'))
    }
    // no binder -> x is a free variable and its enabler is the root
    else {
      // lookup the variable index
      let j = freeVariableIndex.indexOf(variableName)
      if (j < 0) {
        j = freeVariableIndex.push(variableName)
      }
      let root = bindersFromRoot[0]
      binder = { depth: 2 * bindersFromRoot.length - 1, index: root.abs.length + j }
    }
    return {
      label: "Var",
      binder: binder,
      arguments: t.arguments.map(o => lambdaTermToDeBruijn_Abs(o, bindersFromRoot, freeVariableIndex))
    }
  case "App":
    return {
      label: "@",
      operator: lambdaTermToDeBruijn_Abs(t.operator, bindersFromRoot, freeVariableIndex),
      operands: t.operands.map(o => lambdaTermToDeBruijn_Abs(o, bindersFromRoot, freeVariableIndex))
    }
  }
}

// var t = lambdaTermToDeBruijn(omega, omega, undefined, [], [])

////////// Justified sequences

/// A justification pointer
type Pointer =
{
  /// distance from the justifier in the sequence
  distance : number
  /// and pointer's label
  label : number
}

/// Ghosts variable node
type GhostVarNode  = {
  label: 'GhostVar'
}

/// Ghost abstraction node
type GhostAbsNode = {
  label: 'GhostAbs',
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

type AbsOccurrence = {
  node: AbsTermNode
  /// Pointer to the justifying occurrence (of the parent-node)
  justifier: Pointer | "Initial"
}

type VarOccurrence = {
  node: VarTermNode
  /// Pointer to the justifying lambda-occurrence
  justifier: Pointer
}

type AppOccurrence = {
  node: AppTermNode
}

type StructuralOccurrence = AbsOccurrence | VarOccurrence | AppOccurrence

/// Node scope
enum Scope {
  /// Internal node
  Internal,
  /// External node
  External
}

type OccWithScope<T> = T & {
  /// Cache the scope of the underlying node (external or internal) in the occurrence itself
  /// (Recoverable from the hereditary justification).
  scope: Scope
}

/// An node occurrence in a justified sequence
type Occurrence = OccWithScope<GhostOccurrence | StructuralOccurrence>

function isAbstractionOccurrence(n: Occurrence): n is OccWithScope<AbsOccurrence | GhostAbsOccurrence> { return n.node.label == 'GhostAbs' || n.node.label == "Abs" }
function isVariableOccurrence(n: Occurrence): n is OccWithScope<VarOccurrence | GhostVarOccurrence> { return n.node.label == 'GhostVar' || n.node.label == "Var" }
function isApplicationOccurrence(n: Occurrence): n is OccWithScope<AppOccurrence> { return n.node.label == '@' }

function isGhostOccurrence(t: Occurrence): t is OccWithScope<GhostOccurrence> { return t.node.label == 'GhostVar' || t.node.label == 'GhostAbs' }
function isStructuralOccurrence(t: Occurrence): t is OccWithScope<StructuralOccurrence> { return !isGhostOccurrence(t) }

let isInternal = (o: Occurrence) => o.scope == Scope.Internal
let isExternal = (o: Occurrence) => o.scope == Scope.External

/// A justified sequence of node occurrences
type JustSeq = Occurrence[]

/// Iterate over the P-view of a justified sequence
function* pview (t:JustSeq) {
  var i = t.length-1
  while(i>=0){
    let lastOccurrence = t[i]
    yield lastOccurrence

    if (isVariableOccurrence(lastOccurrence)) {
      i--
    } else if (isApplicationOccurrence(lastOccurrence)) {
      i--
    } else if (isAbstractionOccurrence(lastOccurrence)) {
      if (lastOccurrence.justifier == "Initial") {
        i=-1 // initial node => end of P-view
      } else {
        i-=lastOccurrence.justifier.distance
      }
    }
  }
}

/// Return the sequence of position deltas between consecutive occurrences in the P-view
function* pview_delta (t:JustSeq) {
  var i = t.length-1
  var k=0
  while(i>=0){
    let lastOccurrence = t[i]
    if (isVariableOccurrence(lastOccurrence)) {
      k = 1
    } else if (isApplicationOccurrence(lastOccurrence)) {
      k = 1
    } else if (isAbstractionOccurrence(lastOccurrence)) {
      if (lastOccurrence.justifier == "Initial") {
        return // initial node => end of P-view
      } else {
        k = lastOccurrence.justifier.distance
      }
    }
    yield k
    i-=k
  }
}

/// Return the distance to an occurrence justifier from its static depth
/// by enumerating the P-view
function distanceToJustifier (t:JustSeq, enablerDepth:number) {
  var distance = 1
  for(let d of pview_delta(t)) {
    enablerDepth--
    if(enablerDepth<=0) {
      break;
    }
    distance += d
  }
  return distance
}

/// Arity of a node occurrence
function arity(o: GhostOccurrence | StructuralOccurrence) : number {
  switch (o.node.label) {
    case "GhostAbs":
    case "GhostVar":
      return 0
    case "@":
      return o.node.operands.length
    case "Var":
      return o.node.arguments.length
    case "Abs":
      return o.node.boundVariables.length
  }
}

/// Dynamic arity of a traversal (ending with an external variable)
function dynamicArity (t:JustSeq) : number {
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

type Extension = void | Occurrence | (OccWithScope<AbsOccurrence|GhostAbsOccurrence>)[]

function isDeterministic(e: Extension): e is Occurrence { return (e as Occurrence) !== undefined && (e as Occurrence).node !== undefined}
function isNondeterministic(e: Extension): e is (OccWithScope<AbsOccurrence|GhostAbsOccurrence>)[] {
  return (e as (OccWithScope<AbsOccurrence|GhostAbsOccurrence>)[]) !== undefined && (e as Occurrence[]).length !== undefined
}
function isMaximal(e: Extension): e is void { return !isDeterministic(e) && !isNondeterministic(e) }

/// childIndex ranges from
///   1 to artiy(x) for a variable-node
///   0 to artiy(x) for an @-node
function childOf(o: (GhostVarOccurrence | VarOccurrence | AppOccurrence), childIndex: number): AbsTermNode | GhostAbsNode {
  switch (o.node.label) {
  case "GhostVar":
     return { label: "GhostAbs", boundVariables: [] }
  case "Var":
    return childIndex <= arity(o)
      ? o.node.arguments[childIndex-1]
      : { label: "GhostAbs", boundVariables: [] }
  case "@":
    return childIndex <= arity(o)
      ? o.node.operands[childIndex-1]
      : { label: "GhostAbs", boundVariables: [] }
  }
}

function createOccurrenceOfChildOf(
    /// occurrence of the parent node
    m: OccWithScope<GhostVarOccurrence | VarOccurrence | AppOccurrence>,
    /// child index defining the node to create an occurrence of
    childIndex: number,
    /// distance from the occurrence of the node m in the sequence
    distance: number
    )
  : OccWithScope<AbsOccurrence | GhostAbsOccurrence>
{
  let child = childOf(m, childIndex)
  let o = {
    node: child,
    justifier: { distance: distance, label: childIndex },
    scope: m.scope
  }
  if (child.label == "Abs") {
    return o as OccWithScope<AbsOccurrence>
  } else {//if (child.label == "GhostAbs") {
    (o as OccWithScope<GhostAbsOccurrence>).node.boundVariables = []
    return o as OccWithScope<GhostAbsOccurrence>
  }
}

/// extend a traversal
function extendTraversal(treeRoot: AbsTermNode, t: JustSeq): Extension
{
  let nextIndex = t.length
  let lastIndex = t.length-1
  let lastOccurrence = t[lastIndex]

  if (lastOccurrence === undefined) { /// Empty sequence?
    let r = treeRoot as AbsTermNode
    return {
      node: r,
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
      let m = t[nextIndex - distance] as OccWithScope<VarOccurrence | GhostVarOccurrence | AppOccurrence>
      return createOccurrenceOfChildOf(m, lastOccurrence.justifier.label, distance)
    } else { /// external variable
      let da = dynamicArity(t)
      if(da === 0) {
        return /// maximal traversal
      } else {
        let o = lastOccurrence
        var possibleChildren =
          Array.apply(null, Array(da))
               .map((_,i) => createOccurrenceOfChildOf(o, i + 1, 1))
        return possibleChildren
      }
    }
  } else if (isAbstractionOccurrence(lastOccurrence)) {
    if(isStructuralOccurrence(lastOccurrence)) {
      let bodyNode = lastOccurrence.node.body
      if (bodyNode.label == "@") {
        return {
          node: bodyNode, // traverse the body of the lambda
          justifier: "Initial",
          scope: Scope.Internal
        }
      } else {
        let d = distanceToJustifier(t, bodyNode.binder.depth)
        let m = t[nextIndex -d] // if d= 1 then the justifier is the last occurrence
        return {
          node: bodyNode, // traverse the body of the lambda
          justifier: {
            distance: d,
            label: bodyNode.binder.index
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
        node: { label : "GhostVar"},
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

function printOccurrence(t: JustSeq, o: Occurrence, index: number, freeVariableIndex: identifier[]) : string {
  if(isStructuralOccurrence(o)){
    if(isAbstractionOccurrence(o)) {
      return '[' + o.node.boundVariables.join(' ') + ']' + printPointer(o.justifier)
    } else if (isVariableOccurrence(o)) {
      // retrieve the variable name from the binder
        //var j = t[index - o.justifier.distance].node as AbsTermNode | GhostAbsNode
        //let varName = o.justifier.label > j.boundVariables.length
          //? "#"
          //: j.boundVariables[o.justifier.label-1]
      let j = t[index - o.justifier.distance].node as AbsTermNode
      let name =
        (o.justifier.label <= j.boundVariables.length)
        ? j.boundVariables[o.justifier.label - 1]
          : freeVariableIndex[o.justifier.label - 1 - j.boundVariables.length]
      return name + printPointer(o.justifier)
    } else { //if (isApplicationOccurrence(o)) {
      return '@'
    }
  } else { // structural
    if(isAbstractionOccurrence(o)) {
      return '$[' + o.node.boundVariables + ']' + printPointer(o.justifier)
    } else {
      return '#' + printPointer(o.justifier)
    }
  }
}

function printSequence(t: JustSeq, freeVariableIndex:identifier[]) {
  return t.map((o, i) => printOccurrence(t, o, i, freeVariableIndex)).join('--')
}

/// Pop multiple elements from an array
function pops<T>(a:T[], k:number) {
  for (let i = 1; i <= k; i++)
    a.pop()
}

/// core projection
function* coreProjection(t: JustSeq) {
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
         pendingLambdas = pendingLambdas.concat(o.node.boundVariables)
       }
    } else if (isVariableOccurrence(o)) {
       if (isExternal(o)) {
         // patch link distance to account for removed occurrences
         var d = o.justifier.distance
         for (let j = i - o.justifier.distance; j<i; j++) {
           if(isInternal(t[j])) {
             d--
           }
         }
         let cloneOccurrence = Object.assign({}, o)
         cloneOccurrence.justifier = { distance: d, label: o.justifier.label }
         yield cloneOccurrence
         pendingLambdas = []
       } else {
         pops(pendingLambdas, arity(o))
       }
    } else if(isApplicationOccurrence(o)){
       pops(pendingLambdas, arity(o))
    }
  }
}

function enumerateAllTraversals(treeRoot: AbsTermNode, t: JustSeq, freeVariableIndex: identifier[]) {
  while(true) {
    var next = extendTraversal(treeRoot, t)
    if (isMaximal(next)) {
      console.log("Maximal traversal reached:" + printSequence(t, freeVariableIndex))
      let p = Array.from(coreProjection(t))
      p.reverse()
      console.log("               projection:" + printSequence(p, freeVariableIndex))
      return t
    } else if(isDeterministic(next)) {
      t.push(next) // append the traversed occurrence
      verbose && console.log("extended:" + printSequence(t, freeVariableIndex))
    } else {
      /// external variable with multiple non-deterministic choices
      verbose && console.log("External variable reached with " + next.length + " branch(es):" + printSequence(t, freeVariableIndex))
      for(let o of next) {
        verbose && console.log("non-det-before:" + printSequence(t, freeVariableIndex))
        let t2 :JustSeq = t.concat(o)
        verbose && console.log("chose " + (printPointer(o.justifier) + ":" + printSequence(t2, freeVariableIndex)))
        enumerateAllTraversals(treeRoot, t2, freeVariableIndex)
      }
      return
    }
  }
}

/// Evaluate the term with term tree root treeRoot
function evaluate(term: AltLambda) {
  console.log('Traversing ' + printLambdaTerm(term).prettyPrint)
  var freeVariableIndex: identifier[] = []
  var treeRoot = lambdaTermToDeBruijn_Abs(term, [], freeVariableIndex)

  enumerateAllTraversals(treeRoot, [], freeVariableIndex)
}

evaluate(neil)

/// Traverse a traversal until the next strand
/// Return false if the input traversal is maximal
function traverseNextStrand(treeRoot: AbsTermNode, t: JustSeq, freeVariableIndex: identifier[]) {
  var next = extendTraversal(treeRoot, t)
  while (isDeterministic(next)) {
    t.push(next) // append the traversed occurrence
    verbose && console.log("extended:" + printSequence(t, freeVariableIndex))
    next = extendTraversal(treeRoot, t)
  }
  return !isMaximal(next)
}


/// read-out
function evaluateAndReadout(term:AltLambda) {
  console.log('Traversing ' + printLambdaTerm(term).prettyPrint)
  var freeVariableIndex :identifier[] = []
  var treeRoot = lambdaTermToDeBruijn_Abs(term, [], freeVariableIndex)

  var t: JustSeq = []

  var more :boolean = true
  while(more) {
    more = traverseNextStrand(treeRoot, t, freeVariableIndex)
    if (more) {
      verbose && console.log("end of strand: external variable reached" + printSequence(t, freeVariableIndex))
      //
    } else {
      verbose && console.log("Maximal traversal reached:" + printSequence(t, freeVariableIndex))
      let strandEndVar = coreProjection(t).next().value as OccWithScope<VarOccurrence | GhostVarOccurrence>
      let strandBeginAbs = coreProjection(t).next().value as OccWithScope<AbsOccurrence | GhostAbsOccurrence>

      // let x: Var = {
      //   kind: "Var",
      //   name: strandEndVar.,
      //   arguments:
      // }
      ///
    }
  }
}


////// Tests cases:
//
// Traversing (lambda u.u (x u))(lambda v.v y)
// Maximal traversal reached:[]--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)--[](1,1)--u(7,1)--[v](9,1)--v(1,1)--$[](3,1)--#(5,1)--$[](1,1)--#(3,1)--[](5,1)--y(17,2)
//                projection:[]--x(1,1)--[v](1,1)--#(1,1)--$[](1,1)--y(5,2)
// Maximal traversal reached:[]--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)--$[](1,2)--#(3,1)--[](5,1)--y(11,2)
//                projection:[]--x(1,1)--$[](1,2)--y(3,2)