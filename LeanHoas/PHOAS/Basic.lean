import LeanHoas.Setup
import LeanHoas.Named
import LeanHoas.DeBruijn

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Parametric HOAS" =>

Abstract over the type of variables. Binders stay Lean functions, but their
domain is an opaque `v`. The datatype becomes positive, so Lean accepts it.
A body cannot usefully inspect its argument, because it knows nothing about
`v`. And going under a binder means handing it a `v`, which we are free to
choose.

```lean
namespace PHOAS

inductive Term' (v : Type) where
  | var : v → Term' v
  | lam : (v → Term' v) → Term' v
  | app : Term' v → Term' v → Term' v

def Term := ∀ v, Term' v

open Term'
```

A closed term must work for _every_ choice of `v`. Names and indices are gone;
binding is Lean's:

```lean
def I : Term := fun _ => lam fun x => var x
def K : Term := fun _ => lam fun x => lam fun _ => var x
def two : Term := fun _ => lam fun f => lam fun x => app (var f) (app (var f) (var x))
def omega : Term := fun _ => lam fun x => app (var x) (var x)
```

α-equivalence is no longer a relation. It is Lean's own definitional equality:

```lean
example : I = fun _ => lam fun y => var y := rfl
```

# One term, many interpretations

Each choice of `v` is a different way to look under binders. With nothing to
remember about a variable, we can count occurrences:

```lean
def Term'.count : Term' Unit → Nat
  | var _ => 1
  | lam b => (b ()).count
  | app f a => f.count + a.count

def Term.count (e : Term) : Nat := (e Unit).count

example : two.count = 3 := rfl
```

With a name per variable, we can print. Freshness is a counter, and it cannot
go wrong because the names are only ever read, never compared:

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

With a binder depth per variable, the first-order representation from the
previous chapter falls out, including the index arithmetic we no longer
write by hand anywhere else:

```lean
def Term'.toDeBruijn : Term' Nat → Nat → DeBruijn.Term
  | var l, d => .var (d - l - 1)
  | lam b, d => .lam ((b d).toDeBruijn (d + 1))
  | app f a, d => .app (f.toDeBruijn d) (a.toDeBruijn d)

def Term.toDeBruijn (e : Term) : DeBruijn.Term := (e Nat).toDeBruijn 0

example : K.toDeBruijn = .lam (.lam (.var 1)) := rfl

end PHOAS
```
