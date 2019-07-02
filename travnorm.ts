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
let isDummy = (t: Abs): boolean => t.abs.length == 0

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

    if (isDummy(rator)) {
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
    if(isVarApp(t)) {
      return  {
        prettyPrint: t.name + (t.arguments.length == 0 ? '' : ' ' + t.arguments.map(x => bracketize(printLambdaTerm(x))).concat()),
        mustBracketIfArgument: t.arguments.length > 0
      }
    } else if (isApp(t)) {
      let [operator, ...operands] = t.app
      return {
        prettyPrint: bracketize(printLambdaTerm(operator)) + operands.map(x => bracketize(printLambdaTerm(x))).concat(),
        mustBracketIfArgument: true
      }
    } else { //if (isAbs(t)) {
      let bodyPrint = printLambdaTerm(t.body)
      if (isDummy(t)) {
        return {
          prettyPrint: bodyPrint.prettyPrint,
          mustBracketIfArgument: bodyPrint.mustBracketIfArgument
        }
      } else {
        return {
          prettyPrint: '\lambda ' + t.abs.join(' ') + '.' + bodyPrint.prettyPrint,
          mustBracketIfArgument: true
        }
      }
    }
}

console.log(printLambdaTerm(identity).prettyPrint)
console.log(printLambdaTerm(omega).prettyPrint)
console.log(printLambdaTerm(neil).prettyPrint)

/// Tree node labels
type Label = "@" | "Var" | identifier[]

function isAppLabel(t: Label): t is "@" { return (t as "@") == '@' }
function isVarLabel(t: Label): t is "Var" { return (t as "Var") == 'Var' }
function isAbsLabel(t: Label): t is identifier[] { return !isAppLabel(t) && !isVarLabel(t) }

/// Defines an enabling node
type Enabler = {
  // depth is the distance from the enabled node from its enabler node in the tree
  // (1 for the parent node, and so on)
  depth : number
  // The enabling label (index of the variable name for a lambda enabler, child index for a variable/@ enabler)
  label : number
}

// A term tree node
interface TermNode {
  label : Label
  enabler : Enabler | "Initial"
  children : TermNode[]
}

function lambdaTermToTreeNodes(
    // the tree root
    root:Abs,
    /// the node of the alternating AST to convert
    t:AltNodes,
    /// the parent node of t
    parent: AltNodes | undefined,
    /// the list of binder nodes from the root
    bindersFromRoot: Abs[],
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
          let j = b.abs.indexOf(variableName)
          return j<0 ? undefined : { node: b, depth:2*i+1, label: j }
      })
      .filter(b=> b !== undefined)[0];
    // no binder -> x is a free variable and its enabler is the root
    if(binder === undefined) {
      // lookup the variable index
      let j = freeVariableIndex.indexOf(variableName)
      if(j<0) {
        j = freeVariableIndex.push(variableName)
      }
      binder = { label: j, depth:2*bindersFromRoot.length-1}
    }
    return {
      label : "Var",
      enabler : binder,
      children: t.arguments.map(o => lambdaTermToTreeNodes(root, o, t, bindersFromRoot, freeVariableIndex))
    }
  } else if (isApp(t)) {
    let [operator, ...operands] = t.app
    return {
      label : "@",
      enabler : "Initial",
      children: [lambdaTermToTreeNodes(root, operator, t, bindersFromRoot, freeVariableIndex)]
                  .concat(operands.map(o => lambdaTermToTreeNodes(root, o, t, bindersFromRoot, freeVariableIndex)))
    }
  } else { //if (isAbs(t)) {
    return {
      label : t.abs,
      enabler: (parent === undefined) ? "Initial" : { label: 1, depth: 1 },
      children: [lambdaTermToTreeNodes(root, t.body, t, bindersFromRoot.concat([t]), freeVariableIndex)]
    }
  }
}

// var t = lambdaTermToTreeNodes(omega, omega, undefined, [], [])

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
  label: 'GhostVar'
}

type GhostLmd = {
  label: 'GhostLmd',
  names: identifier[]
}

type GhostNode = GhostVar | GhostLmd

/// Node scope
enum Scope {
  /// Internal node
  Internal,
  /// External node
  External
}

/// An node occurrence in a justified sequence
type Occurrence =
{
  /// The node it is an occurrence of
  node: TermNode | GhostNode
  /// Pointer to the justifying occurrence
  justifier: Pointer | "Initial"
  /// Cache the scope of the underlying node (external or internal) in the occurrence itself
  /// (Recoverable from the hereditary justification).
  scope : Scope
}

function isGhost(t: TermNode | GhostNode): t is GhostNode { let g = (t as GhostNode); return g.label == 'GhostVar' || g.label == 'GhostLmd' }
function isStructural(t: TermNode | GhostNode): t is TermNode { return !isGhost(t) }

let isVarOccurrence = (o: Occurrence) => isGhost(o.node) ? o.node.label === 'GhostVar' : isVarLabel(o.node.label)
let isAbsOccurrence = (o: Occurrence) => isGhost(o.node) ? o.node.label === 'GhostLmd' : isAbsLabel(o.node.label)
let isAppOccurrence = (o: Occurrence) => isGhost(o.node) ? false : isAppLabel(o.node.label)

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

    if (isVarOccurrence(lastOccurrence)) {
      i--
    } else if (isAppOccurrence(lastOccurrence)) {
      i--
    } else if (isAbsOccurrence(lastOccurrence)) {
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
    if (isVarOccurrence(lastOccurrence)) {
      k = 1
    } else if (isAppOccurrence(lastOccurrence)) {
      k = 1
    } else if (isAbsOccurrence(lastOccurrence)) {
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
function distanceToJustifier (t:JustSeq, enablerDepth:number)
{
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

function isDeterministic(e: Extension): e is Occurrence { return (e as Occurrence) !== undefined && (e as Occurrence).node !== undefined}
function isNondeterministic(e: Extension): e is Occurrence[] { return (e as Occurrence[]) !== undefined && (e as Occurrence[]).length !== undefined }
function isMaximal(e: Extension): e is void { return !isDeterministic(e) && !isNondeterministic(e) }

function childOf(n: TermNode, childIndex: number): TermNode {
  if(isVarLabel(n.label)) {
    return n.children[childIndex]
  } else if (isAppLabel(n.label)) {
    return n.children[childIndex+1]
  } else {
    throw "Child lookup on lambda node not needed."
  }
}

/// extend a traversal
function extendTraversal (treeRoot:TermNode, t:JustSeq) : (void | Occurrence | Occurrence[])
{
  let lastIndex = t.length-1
  let lastOccurrence = t[lastIndex]

  if (lastOccurrence === undefined) { /// Empty sequence?
    return {
      node: treeRoot,
      justifier: "Initial",
      scope: Scope.External
    }
  } else if (isStructural(lastOccurrence.node) && isAppLabel(lastOccurrence.node.label) ){
    //if(!isStructural(lastOccurrence.node))
//      throw "Impossible: An application node is necessarily structural!"
    return {
      node: lastOccurrence.node.children[0], // traverse the operator node
      justifier : { distance:1, label: 0 },
      scope: Scope.Internal
    }
  } else if (isGhost(lastOccurrence.node) && lastOccurrence.node.label === 'GhostVar'
          || isStructural(lastOccurrence.node) && isVarLabel(lastOccurrence.node.label)) {
    if (lastOccurrence.justifier == "Initial") {
      throw "Impossible: a variable occurrence necessarily has a justifier."
    }
    if (isInternal(lastOccurrence)) {
      let distance = 1+lastOccurrence.justifier.distance
      // Occurrence `m` from the paper, is the node preceding the variable occurrence's justifier.
      let m = t[lastIndex - distance]
      let a = arity(m)
      return {
        node: isStructural(m.node) && lastOccurrence.justifier.label < a
                ? childOf(m.node, lastOccurrence.justifier.label)
                : { label: "GhostLmd", names: [] },
        justifier: { distance: distance, label: lastOccurrence.justifier.label },
        scope: Scope.External
      }
    } else { /// external variable
      let da = dynamicArity(t)
      if(da === 0) {
        return
      } else {
        var possibleChildren =
          Array.apply(null, Array(da))
               .map(function (_,i) { return {
                  node: lastOccurrence.node, //previousNode
                  justifier : { distance:1, label: i },
                  scope: Scope.External
                }})
        return possibleChildren
      }
    }
  } else if ((isGhost(lastOccurrence.node) && lastOccurrence.node.label === 'GhostLmd'
          || isAbsLabel(lastOccurrence.node.label))) {

    if(isStructural(lastOccurrence.node)) {
      let bodyNode = lastOccurrence.node.children[0]
      if (bodyNode.enabler == "Initial") {
        return {
          node: bodyNode, // traverse the body of the lambda
          justifier: "Initial",
          scope: Scope.Internal
        }
      } else {
        let d = distanceToJustifier(t, bodyNode.enabler.depth)
        let m = t[lastIndex - d]
        return {
          node: bodyNode, // traverse the body of the lambda
          justifier: {
            distance: d,
            label: bodyNode.enabler.label
          },
          scope: m.scope
        }
      }
    } else { /// Traverse the child of the ghost lambda node
      if (lastOccurrence.justifier == "Initial") {
        throw('Impossible: ghost lambda are always justified.')
      }
      let mu = t[lastIndex-lastOccurrence.justifier.distance]
      let justifierDistance = lastOccurrence.justifier.distance + 1
      let m = t[lastIndex-justifierDistance]
      let i = lastOccurrence.justifier.label
      let j = arity(mu) + i - arity(m)
      return {
        node: { label : "GhostVar"},
        justifier : { distance: justifierDistance, label: j },
        scope : m.scope
      }
    }
  } else {
    throw "Impossible!"
  }
}

function printOccurrence(o:Occurrence) : string {
  if(isGhost(o.node)){
    if(o.node.label == "GhostLmd") {
      return '[$]'
    } else if (o.node.label == "GhostVar") {
      return '#'
    } else {
      throw "Impossible occurrence"
    }
  } else if(isAbsLabel(o.node.label)) {
    return '[' + o.node.label.join(' ') + ']'
  } else if (isVarLabel(o.node.label)) {
    if (o.justifier == "Initial") {
      throw "Impossible: variable cannot be initial."
    } else {
      return '('+o.justifier.distance +','+o.justifier.label+')'
    }
  } else if (isAppLabel(o.node.label)) {
    return '@'
  } else {
    throw "Impossible occurrence"
  }
}

function printSequence(t:JustSeq) {
  return t.map(printOccurrence).join('--')
}

function traverse(treeRoot: TermNode, t: JustSeq) {
  var t: JustSeq = []
  while (true) {
    var next = extendTraversal(treeRoot, t)
    if (isMaximal(next)) {
      console.log("Maximal traversal reached:" + printSequence(t))
      return t
    } else if(isDeterministic(next)) {
      t = t.concat(next) // append the traversed occurrence
      console.log("extended:" + printSequence(t))
    } else {
      /// external variable with multiple non-deterministic choices
      console.log("External variable reached:" + printSequence(t))
      for(let o of next) {
        let t2 :JustSeq = t.concat(o)
        traverse(treeRoot, t2)
      }
    }
  }
}

/// Evaluate the term with term tree root treeRoot
function evaluate(term: AltLambda) {
  var treeRoot = lambdaTermToTreeNodes(term, term, undefined, [], [])
  traverse(treeRoot, [])
}

evaluate(neil)

/// core projection

/// read-out
