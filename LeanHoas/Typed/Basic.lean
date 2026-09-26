import LeanHoas.Setup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Typed PHOAS: Evaluation Without Environments" =>

The untyped `Term` can be printed and counted, but not evaluated in Lean.
Its values would need a Lean type `D` of functions from `D` to `D`: the same
negative occurrence the kernel rejected. The rejection is deserved, because
`omega` applied to itself runs forever and Lean's functions must terminate.

Types fix this. Index the syntax by object-language types, and the host's
type checker enforces the object language's typing rules: ill-typed programs
cannot be built at all, and every well-typed program terminates. Each object
type gets its own Lean type of values. The representation of variables
becomes a family `v : Ty → Type`, so that a variable of object type `t` is a
value of `v t`.{margin}[`Exp'` is an _indexed family_ (Haskell calls it a
GADT): each constructor fixes the type index of what it builds. `const`
always builds an `Exp' v .nat`, and `lam` always builds an arrow.]

```lean
namespace Typed

inductive Ty where
  | nat
  | arrow : Ty → Ty → Ty

scoped infixr:25 " ⇒ " => Ty.arrow

abbrev Ty.denote : Ty → Type
  | nat => Nat
  | arrow a b => a.denote → b.denote

inductive Exp' (v : Ty → Type) : Ty → Type where
  | var : v t → Exp' v t
  | const : Nat → Exp' v .nat
  | plus : Exp' v .nat → Exp' v .nat → Exp' v .nat
  | lam : (v dom → Exp' v ran) → Exp' v (dom ⇒ ran)
  | app : Exp' v (dom ⇒ ran) → Exp' v dom → Exp' v ran

def Exp (t : Ty) := ∀ v, Exp' v t

open Exp'
```

`Ty.denote` gives each object-language type its meaning as a Lean type:
`nat` means `Nat`, and an arrow means a Lean function type.{margin}[A
_denotation_ is what a piece of syntax means in some model, here in Lean
itself. `abbrev` is a `def` that Lean unfolds freely, which is how `+` on
`Ty.denote .nat` finds addition on `Nat`. `scoped infixr` makes `a ⇒ b`
mean `Ty.arrow a b`, grouping to the right, inside this namespace.] Applying
a number as if it were a function is rejected by Lean before anything runs
(`?m.5` is a type Lean has not solved yet):

```lean +error (name := illTyped)
example : Exp .nat := fun v => app (const 1) (const 2)
```

```leanOutput illTyped
Application type mismatch: The argument
  const 1
has type
  Exp' ?m.5 Ty.nat
but is expected to have type
  Exp' v (Ty.nat ⇒ Ty.nat)
in the application
  (const 1).app
```

# Variables Are Their Values

An interpreter for a first-order representation carries an environment: a
map from variables to their current values, extended at every binder and
consulted at every variable. PHOAS offers a different choice of `v`: let the
values themselves represent the variables, `v := Ty.denote`. A λ becomes a
Lean `fun` that receives the value directly, so there is nothing to extend
and nothing to look up. The interpreter is total (it always terminates and
never fails) and type-safe by construction.

```lean
def Exp'.denote : Exp' Ty.denote t → t.denote
  | var x => x
  | const n => n
  | plus a b => a.denote + b.denote
  | lam b => fun x => (b x).denote
  | app f a => f.denote a.denote

def Exp.denote (e : Exp t) : t.denote :=
  (e Ty.denote).denote
```

```lean
def add : Exp (.nat ⇒ .nat ⇒ .nat) := fun _ =>
  lam fun x => lam fun y => plus (var x) (var y)

def twice : Exp ((.nat ⇒ .nat) ⇒ .nat ⇒ .nat) := fun _ =>
  lam fun f => lam fun x =>
    app (var f) (app (var f) (var x))

def three : Exp .nat := fun v =>
  app (app (twice v) (app (add v) (const 1))) (const 1)

example : three.denote = 3 := rfl

example : twice.denote (add.denote 10) 0 = 20 := rfl

end Typed
```
