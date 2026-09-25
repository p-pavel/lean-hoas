import LeanHoas.Setup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Typed HOAS: Evaluation Without Environments" =>

Index the syntax by object-language types, and the host's type checker
enforces the object language's typing rules. Ill-typed programs cannot be
built at all.

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

# Variables are their values

The payoff of choosing `v`: let a variable _be_ the value it stands for. The
interpreter needs no environment, no lookup, and no substitution, and it is
total and type-safe by construction.

```lean
def Exp'.denote : Exp' Ty.denote t → t.denote
  | var x => x
  | const n => n
  | plus a b => a.denote + b.denote
  | lam b => fun x => (b x).denote
  | app f a => f.denote a.denote

def Exp.denote (e : Exp t) : t.denote := (e Ty.denote).denote
```

```lean
def add : Exp (.nat ⇒ .nat ⇒ .nat) := fun _ =>
  lam fun x => lam fun y => plus (var x) (var y)

def twice : Exp ((.nat ⇒ .nat) ⇒ .nat ⇒ .nat) := fun _ =>
  lam fun f => lam fun x => app (var f) (app (var f) (var x))

def three : Exp .nat := fun v =>
  app (app (twice v) (app (add v) (const 1))) (const 1)

example : three.denote = 3 := rfl

example : twice.denote (add.denote 10) 0 = 20 := rfl

end Typed
```
