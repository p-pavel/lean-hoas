import LeanHoas.Setup
import LeanHoas.Named
import LeanHoas.DeBruijn

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Parametric HOAS" =>

{deftech (key := "PHOAS")}[Parametric HOAS] (PHOAS) makes one change:
abstract over the type of variables. Binders stay Lean functions, but their
argument is now an opaque `v` instead of a whole term. `Term'` no longer
occurs to the left of its own arrow, so the datatype is positive and Lean
accepts it. Going under a binder means handing it a `v`, and each operation
is free to choose what `v` is.

```lean
namespace PHOAS

inductive Term' (v : Type) where
  | var : v → Term' v
  | lam : (v → Term' v) → Term' v
  | app : Term' v → Term' v → Term' v

def Term := ∀ v, Term' v

open Term'
```

A closed term, one with no free variables, must work for _every_ choice of
`v`. We read this as "the term cannot depend on what `v` is", a reading
called {tech}[parametricity]. Lean does not enforce that reading; a later
chapter shows where it breaks and how to repair it.

Names and indices are gone, and binding is Lean's:

```lean
def I : Term := fun _ => lam fun x => var x
def K : Term := fun _ => lam fun x => lam fun _ => var x
def two : Term := fun _ => lam fun f => lam fun x => app (var f) (app (var f) (var x))
def omega : Term := fun _ => lam fun x => app (var x) (var x)
```

Renaming needs no separately defined relation: renaming the Lean variable
that stands for an object-language binder does not change the PHOAS term.
{margin}[`rfl` proves equations that hold by definition, with no reasoning
beyond unfolding and computation.]

```lean
example : I = fun _ => lam fun y => var y := rfl
```

# One Term, Many Interpretations

This is the central idea of the book:

*PHOAS lets each operation choose the representation of variables that is
most convenient for that operation.*

With nothing to remember about a variable, we can count occurrences:

```lean
def Term'.count : Term' Unit → Nat
  | var _ => 1
  | lam b => (b ()).count
  | app f a => f.count + a.count

def Term.count (e : Term) : Nat := (e Unit).count

example : two.count = 3 := rfl
```

With a name per variable, we can print. Fresh names come from a depth
counter: binders that are in scope at the same point sit at different
depths, so their names never clash.

```lean
def Term'.toNamed : Term' String → Nat → Named.Term
  | var x, _ => .var x
  | lam b, n =>
    let x := s!"x{n}"
    .lam x ((b x).toNamed (n + 1))
  | app f a, n => .app (f.toNamed n) (a.toNamed n)

def Term.toNamed (e : Term) : Named.Term := (e String).toNamed 0
```

```lean (name := twoNamed)
#eval two.toNamed
```

```leanOutput twoNamed
λx0. λx1. x0 (x0 x1)
```

With a binder depth per variable, the first-order representation of the
previous chapter (a tree of plain data, with no functions inside) falls out,
including the index arithmetic we no longer write by hand anywhere else:

```lean
def Term'.toDeBruijn : Term' Nat → Nat → DeBruijn.Term
  | var l, d => .var (d - l - 1)
  | lam b, d => .lam ((b d).toDeBruijn (d + 1))
  | app f a, d => .app (f.toDeBruijn d) (a.toDeBruijn d)

def Term.toDeBruijn (e : Term) : DeBruijn.Term := (e Nat).toDeBruijn 0

example : K.toDeBruijn = .lam (.lam (.var 1)) := rfl

end PHOAS
```

The next chapters make two more choices: syntax itself, which gives
substitution, and semantic values, which give evaluation.
