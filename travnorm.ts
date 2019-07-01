/////////////// Variable names
type identifier = string

/////////////// Lambda term with standard AST
namespace StandardAST {
  type Lambda = {
    var : identifier
  } | {
    operator : Lambda
    operand : Lambda
  }| {
    abs: identifier
    body: Lambda
  }

  let identity : Lambda =  { abs:'x', body: {var:'x'} }

  let omega :Lambda =
      {
          operator: { abs:'x', body: {operator: {var:'x'}, operand : {var:'x'} }},
          operand : { abs:'x', body: {operator: {var:'x'}, operand : {var:'x'} }}
      }
}

////////////// Lambda term with alternating AST
type Var = {
  var: identifier
}

type App = {
  operator : Abs
  operands : Abs[]
}

type Abs = {
  abs: string[]
  body: App | Var
}

type AltLambda = Var | App | Abs

let identity : AltLambda = { abs:['x'], body: {var:'x'}}

let omega :AltLambda =
  {abs:[],
   body:
    {
     operator: { abs: ['x'], body: { operator: { abs: [], body: { var: 'x' } }, operands: [{ abs: [], body: { var:'x'}} ] }},
     operands: [{ abs: ['x'], body: { operator: { abs: [], body: { var: 'x' } }, operands: [{ abs: [], body: { var:'x'}}] }} ]
    }
  }

function isAbs(t: AltLambda): t is Abs { return (t as Abs).abs !== undefined }
function isApp(t: AltLambda): t is App { return (t as App).operator !== undefined }
function isVar(t: AltLambda): t is Var { return (t as Var).var !== undefined }

function printLambdaTerm (t:AltLambda) {
    if(isVar(t)) {
      console.log("variable {0}", t.var)
    } else if (isApp(t)) {
      console.log("app {0} - {1}", t.operator, t.operands)
      printLambdaTerm(t.operator)
      t.operands.forEach(printLambdaTerm);
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
    t:AltLambda,
    /// the parent note of t, with associated scope
    parent:([AltLambda,Scope])|undefined,
    /// the list of binder nodes from the root
    bindersFromRoot:[Abs,Scope][],
    /// map that assigns an index to every free variable seen so far
    freeVariableIndex:identifier[]
) : TermNode
{
  if(isVar(t)) {
    let x = t.var
    /// find the variable binder
    let binder : Enabler | undefined =
      bindersFromRoot
      .reverse()
      .map((b,i) => {
          let [bNode, bScope] = b
          let j = bNode.abs.indexOf(x)
          return j<0 ? undefined : { node: bNode, depth:2*i+1, label: j, scope: bScope }
      })
      .filter(b=> b != undefined)[0];
    // no binder -> x is a free variable and its enabler is the root
    if(binder === undefined) {
      // lookup the variable index
      let j = freeVariableIndex.indexOf(x)
      if(j<0) {
        j = freeVariableIndex.push(x)
      }
      binder = { label: j, depth:2*bindersFromRoot.length+1, scope: Scope.External }
    }
    return {
      label : "Var",
      enabler : binder,
      children : []
    }
  } else if (isApp(t)) {
    return {
      label : "@",
      enabler : Initial.InitialNode,
      children : [lambdaTermToTreeNodes(root, t.operator, [t,Scope.External], bindersFromRoot, freeVariableIndex)]
                  .concat(t.operands.map(o => lambdaTermToTreeNodes(root, o, [t,Scope.External], bindersFromRoot, freeVariableIndex)))
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
type GhostNode = {
  label : "GhostVar" | "GhostLmd",
  scope : Scope /// cached scope (recoverable)
}

/// An node occurrence in a justified sequence
type Occurrence =
{
  /// the node it is an occurrence of
  node: TermNode | GhostNode
  /// pointer to the justifying occurrence
  justifier : Pointer | Initial
}

function isGhost(t: TermNode | GhostNode): t is GhostNode { return (t as GhostNode) !== undefined }
function isStructural(t: TermNode | GhostNode): t is TermNode { return (t as TermNode) !== undefined }

let isVarOccurrence = (o: Occurrence) => isGhost(o.node) ? o.node.label === "GhostVar" : isVarLabel(o.node.label)
let isAbsOccurrence = (o: Occurrence) => isGhost(o.node) ? o.node.label === "GhostLmd" : isAbsLabel(o.node.label)
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
              : { label: "GhostLmd", scope: scopeOf(m) },
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


/// core projection

/// read-out
