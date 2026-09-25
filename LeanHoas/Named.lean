import LeanHoas.Setup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Binders, the Hard Way" =>

Object languages bind variables. The most direct encoding stores names, and
immediately inherits two chores: deciding when terms are the same up to
renaming, and substituting without capturing variables.

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

`(λy. x)[x := y]` should be a constant function returning the _outer_ `y`.
The binder captures it instead:

```lean
example : (lam "y" (var "x")).subst "x" (var "y") = lam "y" (var "y") := by
  decide
```

The same function, written twice, is two different terms:

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
