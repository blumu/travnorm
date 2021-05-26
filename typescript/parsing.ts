/// Parsing combinators used to define lambda-terms and construct their AST
/// The AST is parameterized by a type T indicating how the variable node labels
/// are encoded.
///

/// Variable names
export type identifier = string

////////////// Lambda term with alternating AST
/// The type T represents the type used to label variable nodes
/// It can be for instance just 'string' or a deBruijn index
export type Var<T> = { kind: "Var", name: T, arguments: Abs<T>[] }
export type App<T> = { kind: "App", operator: Abs<T>, operands: Abs<T>[] }
export type Abs<T> = { kind: "Abs", boundVariables: identifier[], body: App<T> | Var<T> }

type LambdaAST<T> = Var<T> | App<T> | Abs<T>

/// A binder is defined by the list of identifier that it binds
export type Binder = { boundVariables: identifier[] }

/// To support pretty-printing, the type T must implement name lookup
export interface NameLookup {
  // Given a list of binders occurring in the path from the root
  // to the variable node, return the name of the variable
  // If the variable is free then the map
  // 'freeVariableIndices' can be used to lookup a free variable name from its 'free variable index'
  lookup(bindersFromRoot: Binder[],
    freeVariableIndices: identifier[], // readonly
    withEncoding: boolean // if true then pretty-print the variable name encoding itself as well as the variable name
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

export function printLambdaTerm<T extends NameLookup>(
  r: Abs<T>,
  // print variable name reference encoding in addition to resolved names
  withEncoding: boolean,
  // optional array use to assign indices to free variables (used with the deBruijn encoding)
  freeVariableIndices: identifier[] = []
): Pretty {

  function printSubterm(
    t: LambdaAST<T>,
    bindersFromRoot: Abs<T>[]
  ): Pretty {
    switch (t.kind) {
      case "Var":
        return {
          prettyPrint: (t.name.lookup(bindersFromRoot, freeVariableIndices, withEncoding))
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

function abs<T>(variables: identifier[], body: LambdaAST<T> | T): Abs<T> {
  let applicationBody: LambdaAST<T> = isOfVariableNameType(body) ? { kind: "Var", name: body, arguments: [] } : body

  return applicationBody.kind == "Abs"
    ? { kind: "Abs", boundVariables: variables.concat(applicationBody.boundVariables), body: applicationBody.body }
    : { kind: "Abs", boundVariables: variables, body: applicationBody }
}

function app<T>(operator: Abs<T> | T, operands: Abs<T> | Abs<T>[] | T = []): Abs<T> {
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

/// lookup the index assigned to a free variable, or create one if it is not defined yet
export function lookupOrCreateFreeVariableIndex(freeVariableIndices: string[], variableName: string) {
  let j = freeVariableIndices.indexOf(variableName)
  return (j < 0)
    // create a fresh free variable name
    ? freeVariableIndices.push(variableName)
    : j + 1
}

////////////////// Alternating-AST with variable named with string identifiers.

// An implementation of variable labels where the variable
// name is specified in every node of the tree
// by the name identifier itself
declare global {
  interface String {
    lookup<T>(bindersFromRoot: Abs<T>[], freeVariableIndices: identifier[]): string
  }
}

String.prototype.lookup = function <T>(bindersFromRoot: Abs<T>[], freeVariableIndices: identifier[]) {
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
export var omega = app(delta, delta)

/// Neil Jones's example: J = (\u.u(x u))(\v.v y)
export let neil =
  app(abs(['u'], app('u', app('x', 'u'))),
    abs(['v'], app('v', 'y')))

let varity =
  abs(['t'], app('t', [abs(['n', 'a', 'x'], app('n', abs(['s', 'z'], app('a', [app('s'), app('x', [app('s'), app('z')])])))),
  abs(['a'], 'a'),
  abs(['z0'], 'z0')
  ]))

let two = abs(['s2', 'z2'], app('s2', app('s2', 'z2')))

export let varityTwo = app(varity, two)


export function test_parsing () {
  console.log("===== Parsing and pretty-printing examples")

  console.log(printLambdaTerm(identity, false).prettyPrint)
  console.log(printLambdaTerm(omega, false).prettyPrint)
  console.log(printLambdaTerm(neil, false).prettyPrint)
  console.log(printLambdaTerm(varityTwo, false).prettyPrint)
}
