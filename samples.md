
# Lambda term samples

Define sample terms:

```cmd
set id=λx. x
set fst=λx y. x
set snd=λx y. y
set K=λx y. x
set apply=λf x. f x
set comp=λg f. λx. g (f x)
set sa=λx. x x
set zero=λ s z. z
set one=λ s z. s z
set two=λs z. s(s z)
set three=λs z. s(s(s z))
set four=λs z. s(s(s(s z)))
set five=λs z. s(s(s(s(s z))))
set six=λs z. s(s(s(s(s(s z)))))
set Y=(λx. t (x x)) (λx. t (x x))
set fib=λa.a (λ b c. c (λ d e f.f) (λ d e. d) (λ d e. d e) (λ d e. b (λ f g. c (λ h i. i (h f)) (λh.g) (λh.h)) d (b (λ f g. c(λ h i.i (h (λ j k. k (j f)))) (λh i.g) (λ h.h)(λ h.h)) d e))) (λ b c.c) a

set succ=λ n f x.f (n f x)
set plus=λm n.m (%succ%) n
set mult=λm n.m ((%plus%) n) (%zero%)
set power=λb e.e b


set neil=(λu.u(x u))(λv.v y)
set varity_two=(λ t . t (λ n a x . n (λ s z . a s (x s z))) (λ a . a) (λ z0 . z0) ) (λ s2 z2 . s2 (s2 z2))
set term_with_free_var=(λ x . x y) (λ z . z w)
```

Normalize some terms by traversal:

```cmd
cargo run "(%fib%) (%zero%)"
cargo run "(%fib%) (%one%)"
cargo run "(%fib%) (%two%)"
cargo run "(%fib%) (%three%)"
cargo run "(%fib%) (%four%)"
```

Print all the traversals:

```cmd
cargo run -- --enumerate "(%fib%) (%zero%)"
cargo run -- --enumerate "(%fib%) (%one%)"
cargo run -- --enumerate "(%fib%) (%two%)"
cargo run -- --enumerate "(%fib%) (%two%)"
cargo run -- --enumerate "(%fib%) (%four%)"
```

```cmd
cargo run --   "(%mult%) (%three%) (%two%)"
cargo run --   "(%mult%) (%three%) (%six%)"
cargo run --   "(%mult%) (%four%) (%four%)"
cargo run --   "(%mult%) (%six%) (%six%)"
```

## Large stack use

This example produces a stack overflow (`STATUS_STACK_OVERFLOW`) with the default Rust stack size:

```cmd
cargo run -- --enumerate  "(λs . s(s(s(s 0)))) ((λ f x.f(f(f(f(f x)))))) "
cargo run -- --enumerate --verbose 1 "(λs . s(s(s(s 0)))) ((λ f x.f(f(f(f(f x)))))) "
cargo run -- "(λs . s(s(s(s 0)))) ((λ f x.f(f(f(f(f x)))))) "
```
