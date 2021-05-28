
# Evaluating untyped lambda terms via traversals

This project hosts implementations in TypeScript and Rust of lambda calculus term evaluation algorithm from the TCS paper [Evaluating lambda terms with traversals](https://www.sciencedirect.com/science/article/abs/pii/S0304397519305316).

## Updates

- May 2021, Added Rust implementation
- June 2019, TypeScript implementation
- Jan-April 2018, Ocaml/F# implemention for untyped lambda calculus in [https://github.com/blumu/dphil.tools/tree/master/HOG](HOG)
- 2008, Original Ocaml/F# implementation of traversals for simply-typed terms (without automated readout)


## TypeScript implementation

### Installation and usage

After cloning the git repository install nodejs and TypeScript (tested with TypeScript 4.2.4.)

```cmd
npm install -D typescript
```

Build the TypeScript sources with:

```cmd
tsc
```

Run all tests with:

```cmd
node out\all_tests.js
```

In the TypeScript implementation, lambda terms are defined in the code using combinators, for instance:

```ts
let varity =
  abs(['t'], app('t', [abs(['n', 'a', 'x'], app('n', abs(['s', 'z'], app('a', [app('s'), app('x', [app('s'), app('z')])])))),
  abs(['a'], 'a'),
  abs(['z0'], 'z0')
  ]))
let two = abs(['s2', 'z2'], app('s2', app('s2', 'z2')))
let varity_two = app(varity, two)
```

See `all_tests.ts` for more examples.

### Example: Enumerating all traversals

`(lambda u.u (x u))(lambda v.v y)`

```text
|Depth:0|External variable reached with 2 branch(es):[]--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)
|Depth:0|Choice:1|Trav: []--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1) |Occurrence: [](1,1)
  |Depth:1|External variable reached with 1 branch(es):[]--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)--[](1,1)--u(7,1)--[v](9,1)--v(1,1)--$[](3,1)--#(5,1)
  |Depth:1|Choice:1|Trav: []--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)--[](1,1)--u(7,1)--[v](9,1)--v(1,1)--$[](3,1)--#(5,1) |Occurrence: $[](1,1)
    |Depth:2|Maximal traversal:[]--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)--[](1,1)--u(7,1)--[v](9,1)--v(1,1)--$[](3,1)--#(5,1)--$[](1,1)--#(3,1)--[](5,1)--y(17,2)
    |               projection:[]--x(1,1)--[v](1,1)--#(1,1)--$[](1,1)--y(5,2)
|Depth:0|Choice:2|Trav: []--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1) |Occurrence: $[](1,2)
  |Depth:1|Maximal traversal:[]--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)--$[](1,2)--#(3,1)--[](5,1)--y(11,2)
  |               projection:[]--x(1,1)--$[](1,2)--y(3,2)
```

### Examples: Evaluation with name-preserving resolution

#### `(lambda u.u (x u))(lambda v.v y)`

```ts
evaluateAndPrintNormalForm(app(abs(['u'], app('u', app('x', 'u'))), abs(['v'], app('v', 'y'))))
Evaluating (lambda u.u (x u))(lambda v.v y)
x (lambda v.v y) y
```

#### `(lambda t.t (lambda n a x.n (lambda s z.a s (x s z))) (lambda a.a) (lambda z0.z0))(lambda s2 z2.s2 (s2 z2))`

```ts
let varity =
  abs(['t'], app('t', [abs(['n', 'a', 'x'], app('n', abs(['s', 'z'], app('a', [app('s'), app('x', [app('s'), app('z')])])))),
  abs(['a'], 'a'),
  abs(['z0'], 'z0')
  ]))
let two = abs(['s2', 'z2'], app('s2', app('s2', 'z2')))
evaluateAndPrintNormalForm(app(varity, two))
```

```text
Evaluating (lambda t.t (lambda n a x.n (lambda s z.a s (x s z))) (lambda a.a) (lambda z0.z0))(lambda s2 z2.s2 (s2 z2))
lambda x x' s z.s (x s (x' s z))
```

### Some raw ideas for future improvements

- Package a smaller implementation: if reading out the normalized term with names is not needed then the normalization procedure working on the DeBruijn-based AST fits in about 500 LOC.
- A justification pointer is not needed for free variable occurrences. The reference to the tree node alone suffices.
  We could encode them with a new type `FreeVarOccurrence<T>` with no associated pointer.
  Need to investigate if this could help avoid the array used to map free variable indices to their names. (The free variable name would then just be encoded in the traversal occurrence itself.)
- Alternating AST probably not needed: p-view/core could be adjusted to operate on traditional AST (with single node per lambda/application), though traversals would get longer;
- Implementing traversals using (shared) linked-lists could help save on memory by avoiding array copy at each recursive call.  Justification pointers could also be implemented with pointers instead of array index/deltas.

## Rust implementation

### Installation and usage for Rust

After cloning the git repository install [Rust](https://www.rust-lang.org/learn/get-started) and run `cargo build` and `cargo test`.

The Rust version features a parser implemented using LALRPOP. The user
provides the input lambda term as a string argument to the program. For instance:

```cmd
cd rust
cargo run "(λ t . t (λ n a x . n (λ s z . a s (x s z))) (λ a . a) (λ z0 . z0) ) (λ s2 z2 . s2 (s2 z2))"
```

Output:

```text
Running `target\debug\travnorm.exe "(λ t . t (λ n a x . n (λ s z . a s (x s z))) (λ a . a) (λ z0 . z0) ) (λ s2 z2 . s2 (s2 z2))"`

Parsing lambda term (λ t . t (λ n a x . n (λ s z . a s (x s z))) (λ a . a) (λ z0 . z0) ) (λ s2 z2 . s2 (s2 z2))
term has length 26
===== Evaluation without name resolution
Evaluating (\lambda t.t (\lambda n a x.n (\lambda s z.a s (x s z))) (\lambda a.a) (\lambda z0.z0))(\lambda s2 z2.s2 (s2 z2))
\lambda x x s z.s(1,3) (x(3,1) s(5,3) (x(5,2) s(7,3) z(7,4)))
===== Evaluation with name resolution
Evaluating (\lambda t.t (\lambda n a x.n (\lambda s z.a s (x s z))) (\lambda a.a) (\lambda z0.z0))(\lambda s2 z2.s2 (s2 z2))
\lambda x x' s z.s (x s (x' s z))
```

The input lambda term can also be passed from standard input. For instance on Windows:

```cmd
type fib_four.lmd | cargo run
```

To enumerate all traversals add the `--enumerate` switch:

```cmd
cargo run -- --enumerate "(λ u.u (x u))(λ v.v y)"
```

Output:

```cmd
Reading input lambda term from command-line argument
Parsing lambda term '(λ u.u (x u))(λ v.v y)'
term has length 12
===== Enumerate all traversals
Traversing (λ u.u (x u))(λ v.v y)
    |Depth:2|Length:18|Maximal traversal:[]--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)--[](1,1)--u(7,1)--[v](9,1)--v(1,1)--$[](3,1)--#(5,1)--$[](1,1)--#(3,1)--[](5,1)--y(17,2)
    |               projection:[]--x(1,1)--[v](1,1)--#(1,1)--$[](1,1)--y(5,2)
  |Depth:1|Length:12|Maximal traversal:[]--@--[u](1,0)--u(1,1)--[v](3,1)--v(1,1)--[](3,1)--x(7,1)--$[](1,2)--#(3,1)--[](5,1)--y(11,2)
  |               projection:[]--x(1,1)--$[](1,2)--y(3,2)
```

### Examples

Fibonacci(4)

```cmd
cargo run "(λa.a (λ b c. c (λ d e f.f) (λ d e. d) (λ d e. d e) (λ d e. b (λ f g. c (λ h i. i (h f)) (λh.g) (λh.h)) d (b (λ f g. c(λ h i.i (h (λ j k. k (j f)))) (λh i.g) (λ h.h)(λ h.h)) d e))) (λ b c.c) a) (λf x . f(f(f (f x))))"
```

Output:

```cmd
===== Evaluation without name resolution
Evaluating (\lambda a.a (\lambda b c.c (\lambda d e f.f) (\lambda d e.d) (\lambda d e.d e) (\lambda d e.b (\lambda f g.c (\lambda h i.i (h f)) (\lambda h.g) (\lambda h.h)) d (b (\lambda f g.c (\lambda h i.i (h (\lambda j k.k (j f)))) (\lambda h i.g) (\lambda h.h) (\lambda h.h)) d e))) (\lambda b c.c) a)(\lambda f x.f (f (f (f x))))
\lambda d e.d(1,1) (d(3,1) (d(5,1) (d(7,1) (d(9,1) (d(11,1) (d(13,1) (d(15,1) e(17,2))))))))
===== Evaluation with name resolution
Evaluating (\lambda a.a (\lambda b c.c (\lambda d e f.f) (\lambda d e.d) (\lambda d e.d e) (\lambda d e.b (\lambda f g.c (\lambda h i.i (h f)) (\lambda h.g) (\lambda h.h)) d (b (\lambda f g.c (\lambda h i.i (h (\lambda j k.k (j f)))) (\lambda h i.g) (\lambda h.h) (\lambda h.h)) d e))) (\lambda b c.c) a)(\lambda f x.f (f (f (f x))))
\lambda d e.d (d (d (d (d (d (d (d e)))))))
```

## Other implementations

- An **OCaml/F#** implementation with GUI available [https://github.com/blumu/dphil.tools/tree/master/HOG](here).
I originally wrote this tool back in 2008 for my DPhil thesis for the simply-typed lambda calculus and higher-order grammars. In 2018 I added the traversal implementation for the untyped lambda calculus. The tools lets you perform a full traversal enumeration with core projections from which the term AST can be reconstructed, though it does not implement the conflict avoiding name-resolution readout from the paper.
