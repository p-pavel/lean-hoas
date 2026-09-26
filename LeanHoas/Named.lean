import LeanHoas.Setup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Binders, the Hard Way" =>

A {deftech}[binder] introduces a variable name for some region of code, its
scope: a function parameter, a `let`, a loop variable, a quantifier such as
"for every order `o`". The most direct way to represent a language with
binders stores names as strings, and immediately inherits two chores:
deciding when two terms are the same up to renaming, and substituting one
term into another without mixing variables up.{margin}[Reading the Lean:
`inductive` declares a tree-shaped type with the listed constructors.
`namespace` and `open` scope names, like a module and its import.
`deriving DecidableEq` generates an equality test. `example` states an
unnamed fact, and `by decide` proves it by running that test.]

```lean
namespace Named

inductive Term where
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term
  deriving DecidableEq

open Term

def Term.subst (t : Term) (x : String) (s : Term) : Term :=
  match t with
  | var y => if x = y then s else var y
  | lam y b => if x = y then lam y b else lam y (b.subst x s)
  | app f a => app (f.subst x s) (a.subst x s)
```

We write `λx. b` for a function with parameter `x` and body `b`,{margin}[`λx. b`
is the notation of the λ-calculus, the minimal language of functions that
programming-language theory uses as its laboratory. In Lean it is
`fun x => b`.] and `t[x := s]` for `t` with `s` substituted for the free
occurrences of `x`.{margin}[A variable is _free_ in a term when no binder
inside that term introduces it. In `λy. x`, `x` is free and `y` is bound.]
Now `(λy. x)[x := y]` should be a constant function returning the _outer_
`y`. The binder {deftech (key := "capture")}[captures] it instead:

```lean
example : (lam "y" (var "x")).subst "x" (var "y") = lam "y" (var "y") := by
  decide
```

The same function, written twice, is two different terms, although the two
are {deftech (key := "alpha-equivalence")}[α-equivalent]: they differ only in
the names of bound variables.

```lean
example : lam "x" (var "x") ≠ lam "y" (var "y") := by decide
```

The standard repairs are fresh-name supplies, renaming during substitution,
and an α-equivalence relation that every theorem must respect. The rest of
this document is about making those chores disappear.

```lean -show
def Term.toString : Term → String
  | var x => x
  | lam x b => s!"λ{x}. {b.toString}"
  | app f a =>
    let fs := match f with
      | lam .. => s!"({f.toString})"
      | _ => f.toString
    let as := match a with
      | var x => x
      | _ => s!"({a.toString})"
    s!"{fs} {as}"

instance : ToString Term := ⟨Term.toString⟩

end Named
```
