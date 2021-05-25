/// <reference path="parsing.ts" />

import { identifier, Abs, App, Var, lookupOrCreateFreeVariableIndex, NameLookup, printLambdaTerm, Binder, omega } from "./parsing";

namespace DeBruijnConversion{
  /// if true then print additional logging
  export let verbose = false
}

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
export class DeBruijnPair implements NameLookup {
  // Depth is the distance from the variable node to its binder node in the path to the tree root
  // (1 for the parent node, and so on)
  depth: number = 0
  // Index of the variable name in the lambda-binder
  index: number = 0

  constructor(depth: number, index: number) {
    this.depth = depth
    this.index = index
  }

  /// Lookup name of a bound variable.
  /// If the variable is bound, return the binder and the name of the variable ([Abs<DeBruijnPair>, identifier])
  /// If it's a free variable, return the name of the free variable (identifier)
  lookupBinderAndName(
    bindersFromRoot: Binder[],
    freeVariableIndices: identifier[]
  ): { binder: Binder | undefined, name: identifier } {
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

  lookup(bindersFromRoot: Binder[], freeVariableIndices: identifier[], printEncoding: boolean): string {
    let binderAndName = this.lookupBinderAndName(bindersFromRoot, freeVariableIndices)
    /// If printEncoding os true then append the deBruijn pair encoding
    return binderAndName.name + (printEncoding ? '(' + this.depth + ',' + this.index + ')' : '')
  }

}

/// Convert an AST of type Abs<identifier> to an AST of type Abs<DeBruijnPair>
/// NOTE: This is not actually needed in the implementation of the traversal-based normalization procedure
/// it's used for debugging purpose only.
export function toDeBruijnAST(
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
          DeBruijnConversion.verbose && console.log('bindersFromRoot:' + newBindersFromRoot.map(x => '[' + x.boundVariables.join(' - ') + ']').join('\\') + ' varName:' + variableName + ' binderIndex:' + binderIndex + ' depth:' + binder.depth + ' binderVarNames:' + b.boundVariables.join('-'))
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

export function test_debruijn_ast_printing() {
  console.log('Test printing a lambda term from the deBruijn AST')
  let d = printLambdaTerm(toDeBruijnAST(omega, [], []), false).prettyPrint
  let d2 = printLambdaTerm(omega, false).prettyPrint
  console.log(d)
  console.log(d2)
  if (d !== d2) {
    throw "Pretty printing should give the same result"
  }
}
