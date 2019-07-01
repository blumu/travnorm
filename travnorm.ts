/////////////// Variable names
type identifier = string

////////////// Lambda term with alternating AST
type VarApp = { name: identifier, arguments: Abs[] }
type App = { app: Abs[] }
type Abs = { abs: identifier[],  body: App | VarApp }

/// The alternating-AST of a lambda term always starts with a lambda node
type AltLambda = Abs

/// The three types of alternating-AST tree tokens
type AltNodes = VarApp | App | Abs

function isAbs(t: AltNodes): t is Abs { return (t as Abs).abs !== undefined }
function isApp(t: AltNodes): t is App { return (t as App).app !== undefined }
function isVarApp(t: AltNodes): t is VarApp { return (t as VarApp).arguments !== undefined }
function isIdentifier(t: AltNodes | AltNodes[] | identifier): t is identifier { return (t as identifier).search !== undefined }

function isSingleton(t: AltNodes | AltNodes[]): t is AltNodes { return (t as AltNodes[]).length === undefined }

// add a dummy lambda if necessary
let dummyLambda = (l: AltNodes) => isAbs(l) ? l : { abs: [], body: l }

let abs = (variables: identifier[], body: App | VarApp | Abs | identifier): Abs =>
{
  let applicationBody: App | Abs | VarApp = isIdentifier(body) ? { name: body, arguments: [] } : body

  return isAbs(applicationBody)
    ? { abs: variables.concat(applicationBody.abs), body: applicationBody.body }
    : { abs: variables, body: applicationBody }
}

let app = (operator: Abs | identifier, operands: Abs | Abs[] | identifier): Abs =>
{
    let unappliedVar = (name: identifier): Abs => { return { abs: [], body: { name: name, arguments: [] } } }

    /// If operator is just an identifier then convert it into a variable node
    let rator: Abs = isIdentifier(operator) ? unappliedVar(operator) : operator

    /// If operand is just an identifier then convert it into a variable node
    let rands = isIdentifier(operands) ? unappliedVar(operands) : operands

    /// if single operand then make it into a singleton array
    let randsAsArray = isSingleton(rands) ? [rands] : rands

    let randsDummified = randsAsArray.map(dummyLambda)

    if (rator.abs === []) {
      if (isApp(rator.body)) {
        /// combine consecutive application
        return { abs: [], body: { app: rator.body.app.concat(randsDummified) } }
      } else if (isVarApp(rator.body)) {
        /// combine consecutive application
        return { abs: [], body: { name: rator.body.name, arguments: rator.body.arguments.concat(randsDummified) } }
      } else {
        throw "Impossible case: abstraction necessarily alternate with application, by construction."
      }
    } else {
      return { abs: [], body: { app: [rator].concat(randsDummified) } }
    }
}


/// Term examples
let identity: AltLambda = abs(['x'], 'x')
let delta: AltLambda = abs(['x'], app('x', 'x'))
var omega: AltLambda = app(delta, delta)

/// Neil Jones's example: J = (\u.u(x u))(\v.v y)
let neil: AltLambda =
  app(abs(['u'], app('u', app('x', 'u'))),
      abs(['v'], app('u', 'v')))
//////////

function printLambdaTerm (t:AltNodes) {
    if(isVarApp(t)) {
      console.log("variable {0}", t)
    } else if (isApp(t)) {
      let [operator, ...operands] = t.app
      console.log("app {0} - {1}", operator, operands)
      printLambdaTerm(operator)
      operands.forEach(printLambdaTerm);
    } else if (isAbs(t)) {
      console.log("abs {0} . {1}", t.abs, t.body)
      printLambdaTerm(t.body)
    }
}

////////////// Tree nodes for alternating AST
/// Node scope
enum Scope {
  /// Internal node
  Internal,
  /// External node
  External
}

/// Tree node labels
type Label = "@" | "Var" | identifier[]

function isAppLabel(t: Label): t is "@" { return (t as "@") !== undefined }
function isVarLabel(t: Label): t is "Var" { return (t as "Var") !== undefined }
function isAbsLabel(t: Label): t is identifier[] { return (t as identifier[]) !== undefined }

/// Defines an enabling node
type Enabler = {
  // depth is the distance from the enabled node from its enabler node in the tree
  // (1 for the parent node, and so on)
  depth : number
  // The enabling label (index of the variable name for a lambda enabler, child index for a variable/@ enabler)
  label : number,
  // Cache the scope of the enabling node (external or internal).
  // Recoverable from the hereditary enabling relation itself.
  scope: Scope
}

/// Type of initial node with no enabler
enum Initial {
  InitialNode
}

// A term tree node
interface TermNode {
  label : Label
  enabler : Enabler | Initial
  children : TermNode[]
}

function lambdaTermToTreeNodes(
    // the tree root
    root:Abs,
    /// the node of the alternating AST to convert
    t:AltNodes,
    /// the parent note of t, with associated scope
    parent:([AltNodes,Scope])|undefined,
    /// the list of binder nodes from the root
    bindersFromRoot:[Abs,Scope][],
    /// map that assigns an index to every free variable seen so far
    freeVariableIndex:identifier[]
) : TermNode
{
  if(isVarApp(t)) {
    let variableName = t.name
    /// find the variable binder
    let binder : Enabler | undefined =
      bindersFromRoot
      .reverse()
      .map((b,i) => {
          let [bNode, bScope] = b
          let j = bNode.abs.indexOf(variableName)
          return j<0 ? undefined : { node: bNode, depth:2*i+1, label: j, scope: bScope }
      })
      .filter(b=> b != undefined)[0];
    // no binder -> x is a free variable and its enabler is the root
    if(binder === undefined) {
      // lookup the variable index
      let j = freeVariableIndex.indexOf(variableName)
      if(j<0) {
        j = freeVariableIndex.push(variableName)
      }
      binder = { label: j, depth:2*bindersFromRoot.length+1, scope: Scope.External }
    }
    return {
      label : "Var",
      enabler : binder,
      children : []
    }
  } else if (isApp(t)) {
    let [operator, ...operands] = t.app
    return {
      label : "@",
      enabler : Initial.InitialNode,
      children : [lambdaTermToTreeNodes(root, operator, [t,Scope.External], bindersFromRoot, freeVariableIndex)]
                  .concat(operands.map(o => lambdaTermToTreeNodes(root, o, [t,Scope.External], bindersFromRoot, freeVariableIndex)))
    }
  } else { //if (isAbs(t)) {
    /// A root node is external, other nodes have the scope of their parent
    let parentScope = (parent === undefined) ? Scope.External : parent[1]
    return {
      label : t.abs,
      enabler : (parent === undefined) ? Initial.InitialNode : { label: 1, depth: 1, scope: parentScope },
      children : [lambdaTermToTreeNodes(root, t.body, [t,parentScope], bindersFromRoot.concat([t,parentScope]), freeVariableIndex)]
    }
  }

}

var t = lambdaTermToTreeNodes(omega, omega, undefined, [], [])

console.log("test")

//printLambdaTerm(omega_alt)
console.log("ended")


////////// Justified sequences


/// A justification pointer
type Pointer =
{
  /// distance from the justifier in the sequence
  distance : number
  /// and pointer's label
  label : number
}

/// Ghosts node
type GhostVar = {
  label: 'GhostVar',
  scope: Scope /// cached scope (recoverable)
}

type GhostLmd = {
  label: 'GhostLmd',
  names: identifier[],
  scope: Scope /// cached scope (recoverable)
}

type GhostNode = GhostVar | GhostLmd

/// An node occurrence in a justified sequence
type Occurrence =
{
  /// the node it is an occurrence of
  node: TermNode | GhostNode
  /// pointer to the justifying occurrence
  justifier : Pointer | Initial
}

function isGhost(t: TermNode | GhostNode): t is GhostNode { return (t as GhostNode).label !== undefined }
function isStructural(t: TermNode | GhostNode): t is TermNode { return (t as TermNode).label !== undefined }

let isVarOccurrence = (o: Occurrence) => isGhost(o.node) ? o.node.label === 'GhostVar' : isVarLabel(o.node.label)
let isAbsOccurrence = (o: Occurrence) => isGhost(o.node) ? o.node.label === 'GhostLmd' : isAbsLabel(o.node.label)
let isAppOccurrence = (o: Occurrence) => isGhost(o.node) ? false : isAppLabel(o.node.label)

let scopeOf = (o: Occurrence) => isGhost(o.node)
  ? o.node.scope
  : o.node.enabler == Initial.InitialNode ? <Scope>Scope.External : o.node.enabler.scope

let isInternal = (o: Occurrence) => scopeOf(o) == Scope.Internal
let isExternal = (o: Occurrence) => scopeOf(o) == Scope.External

/// A justified sequence of node occurrences
type JustSeq = Occurrence[]

/// Iterate over the P-view of a justified sequence
function* pview (t:JustSeq) {
  var i = t.length-1
  while(i>=0){
    let lastOccurrence = t[i]
    yield lastOccurrence

    if (isVarOccurrence(lastOccurrence)) {
      i--
    } else if (isAppOccurrence(lastOccurrence)) {
      i--
    } else if (isAbsOccurrence(lastOccurrence)) {
      if(lastOccurrence.justifier === Initial.InitialNode) {
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
    if (isVarOccurrence(lastOccurrence)) {
      k = 1
    } else if (isAppOccurrence(lastOccurrence)) {
      k = 1
    } else if (isAbsOccurrence(lastOccurrence)) {
      if(lastOccurrence.justifier === Initial.InitialNode) {
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
function distanceToJustifier (t:JustSeq, enablerDepth:number)
{
  var distance = 0
  for(let d of pview_delta(t)) {
    if(enablerDepth<=0) {
      break;
    }
    distance += d
    enablerDepth--
  }
  return distance
}

/// Arity of a node occurrence
function arity(o:Occurrence) : number {
  if(isGhost(o.node)) {
    return 0
  } else if (isAppOccurrence(o)) {
    return o.node.children.length-1
  } else if (isVarOccurrence(o)) {
    return o.node.children.length
  } else { // if (isAbsLabel(l)) {
    return o.node.label.length
  }
}

/// Dynamic arity of a traversal (ending with an external variable)
function dynamicArity (t:JustSeq) : number {
  var i = t.length - 1
  var sum = 0
  var max = 0
  while (i >= 0) {
    let lastOccurrence = t[i]
    if (isAbsOccurrence(lastOccurrence)) {
      if (isExternal(lastOccurrence)) {
        return max
      } else {
        sum += arity(lastOccurrence)
      }
    } else if (isVarOccurrence(lastOccurrence)
      || isAppOccurrence(lastOccurrence)) {
      sum -= arity(lastOccurrence)
    }
    max = Math.max(sum, max)
    i--
  }
  return max
}

type Extension = void | Occurrence | Occurrence[]

function isMaximal(e: Extension): e is void { return (e as void) !== undefined }
function isDeterministic(t: Extension): t is Occurrence { return (t as Occurrence).node !== undefined }
function isNondeterministic(t: Extension): t is Occurrence[] { return (t as Occurrence[]).length !== undefined }

/// extend a traversal
function extendTraversal (treeRoot:TermNode, t:JustSeq) : (void | Occurrence | Occurrence[])
{
  let lastIndex = t.length-1
  let lastOccurrence = t[lastIndex]
  /// Empty sequence
  if(lastOccurrence === undefined) {
    return {
      node: treeRoot,
      justifier: Initial.InitialNode
    }
  } else if (isStructural(lastOccurrence.node) && isAppOccurrence(lastOccurrence)) {
    return {
      node: lastOccurrence.node.children[0], // traverse the operator node
      justifier : { distance:1, label: 0 }
    }
  } else if (isVarOccurrence(lastOccurrence)) {
    if(lastOccurrence.justifier === Initial.InitialNode) {
      throw "Impossible: a variable occurrence necessarily has a justifier."
    }
    if (isInternal(lastOccurrence)) {
      let distance = 1+lastOccurrence.justifier.distance
      // Occurrence `m` from the paper, is the node preceding the variable occurrence's justifier.
      let m = t[lastIndex - distance]
      return {
        node: isStructural(m.node)
              ? m.node.children[lastOccurrence.justifier.label]
              : { label: "GhostLmd", names: [], scope: scopeOf(m) },
        justifier: { distance: distance, label: lastOccurrence.justifier.label }
      }
    } else {
      let da = dynamicArity(t)
      if(da === 0) {
        return
      } else {
        var possibleChildren =
          Array.apply(null, Array(da))
               .map(function (_,i) { return {
                  node: lastOccurrence.node, //previousNode
                  justifier : { distance:1, label: i }
                }})
        return possibleChildren
      }
    }
  } else {// if (isAbsLabel(lastOccurrence.node.label)) {
    if(isStructural(lastOccurrence.node)) {
      let bodyNode = lastOccurrence.node.children[0]
      return {
        node: bodyNode, // traverse the body of the lambda
        justifier : bodyNode.enabler == Initial.InitialNode
                        ? Initial.InitialNode
                        : { distance: distanceToJustifier(t, bodyNode.enabler.depth),
                            label: bodyNode.enabler.label }
      }
    } else { /// Traverse the child of the ghost lambda node
      if(lastOccurrence.justifier === Initial.InitialNode) {
        throw('Impossible: ghost lambda are always justified.')
      }
      let mu = t[lastIndex-lastOccurrence.justifier.distance]
      let justifierDistance = lastOccurrence.justifier.distance + 1
      let m = t[lastIndex-justifierDistance]
      let i = lastOccurrence.justifier.label
      let j = arity(mu) + i - arity(m)
      return {
        node: { label : "GhostVar", scope: scopeOf(m) },
        justifier : { distance: justifierDistance, label: j }
      }
    }
  }
}

function traverse(treeRoot: TermNode, t: JustSeq) {
  var t: JustSeq = []
  while (true) {
    var next = extendTraversal(treeRoot, t)
    if (isMaximal(next)) {
      return t;
    } else if(isDeterministic(next)) {
      t = t.concat(next) // append the traversed occurrence
    } else {
      /// external variable with multiple non-deterministic choices
      for(let o of next) {
        let t2 :JustSeq = t.concat(o)
        traverse(treeRoot, t2)
      }
    }
  }
}

/// Evaluate the term with term tree root treeRoot
function evaluate(treeRoot: TermNode, t: JustSeq) {
  traverse(treeRoot, [])
}

/// core projection

/// read-out
