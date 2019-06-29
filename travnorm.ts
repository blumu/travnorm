/////////////// Variable names
type identifier = string

/////////////// Lambda term with standard AST
type Lambda =
  {
    var : identifier
  }
  | {
      operator : Lambda
      operand : Lambda
    }
  | {
      abs: identifier
      body: Lambda
    }

let identity : Lambda =  { abs:'x', body: {var:'x'} }

let omega :Lambda =
    {
        operator: { abs:'x', body: {operator: {var:'x'}, operand : {var:'x'} }},
        operand : { abs:'x', body: {operator: {var:'x'}, operand : {var:'x'} }}
    }
////////////////////

////////////// Lambda term with alternating AST
interface Var {
  name: identifier
}

interface App {
  operator : Abs
  operands : Abs[]
}

interface Abs {
  abs: string[]
  body: App | Var
}

type AltLambda = Var | App | Abs

let id : AltLambda = { abs:['x'], body: {name:'x'}}

let omega_alt :AltLambda =
  {
    operator: { abs:['x'], body: {operator: { abs:[], body: {name:'x'}}, operands: [ { abs:[], body: {name:'x'}} ] }},
    operands : [ { abs:['x'], body: {operator: { abs:[], body: {name:'x'}}, operands: [ { abs:[], body: {name:'x'}}] }} ]
  }

function isAbs(t: AltLambda): t is Abs {
  return (t as Abs).abs !== undefined;
}
function isApp(t: AltLambda): t is App {
  return (t as App).operator !== undefined;
}
function isVar(t: AltLambda): t is Var {
  return (t as Var).name !== undefined;
}

function printLambdaTerm (t:AltLambda) {
    if(isVar(t)) {
      console.log("variable {0}", t.name)
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
type Enabler<T> = { node: T, label : number }

type Label = "@" | identifier | string[]

// A term tree node
interface TermNode<T> {
  label : Label
  enabler : Enabler<T> | undefined
  children : TermNode<T>[]
}

function lambdaTermToTreeNodes (
    t:AltLambda,
    parent:AltLambda|undefined,
    bindersFromRoot:Abs[]
  ) : TermNode<AltLambda>
{
  if(isVar(t)) {
    let x = t.name
    /// find the variable binder
    let e : Enabler<Abs> | undefined =
      bindersFromRoot
      .reverse()
      .map(binder => {
          let j = binder.abs.indexOf(x)
          return (j>-1) ? { node : binder, label : j } : undefined
      })
      .filter(b=> b != undefined)[0];
    return {
        label : t.name,
        enabler : e,
        children : []
    }
  } else if (isApp(t)) {
    return {
      label : "@",
      enabler : undefined,
      children : [lambdaTermToTreeNodes(t.operator, t, bindersFromRoot)]
                  .concat(t.operands.map(o => lambdaTermToTreeNodes(o, t, bindersFromRoot)))
    }
  } else { //if (isAbs(t)) {
    return {
      label : t.abs,
      enabler : (parent !== undefined) ?  { node : parent, label : 1 } : undefined,
      children : [lambdaTermToTreeNodes(t.body, t, bindersFromRoot.concat(t))]
    }
  }
}
var t = lambdaTermToTreeNodes(omega_alt, undefined, [])

console.log("test")

//printLambdaTerm(omega_alt)
console.log("ended")


////////// Justified sequences

/// An node occurrence in a justified sequence
type Occurrence<T> =
{
  /// the node it is an occurrence of
  node : TermNode<T>
  /// distance from the justifier in the sequence
  justifier : number
  /// justification label
  linkLabel : number
}

/// A justified sequence of node occurrences
type JustSeq<T> = Occurrence<T>[]
