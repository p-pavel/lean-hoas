import LeanHoas.Setup
import LeanHoas.Typed.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "A Verified Transformation" =>

Constant folding replaces `1 + 2` by `3` before the program runs. Over
parametric syntax it is written once, for every `v`. Its correctness proof
then makes the choice that matters for correctness, the values, and becomes
a plain structural induction.{margin}[Structural induction is recursion for
proofs: one case per constructor, with the statement already established for
the sub-terms.]

```lean
namespace Typed
open Exp'

def Exp'.cfold : Exp' v t → Exp' v t
  | var x => var x
  | const n => const n
  | plus a b =>
    match a.cfold, b.cfold with
    | const n, const m => const (n + m)
    | a', b' => plus a' b'
  | lam b => lam fun x => (b x).cfold
  | app f a => app f.cfold a.cfold

def Exp.cfold (e : Exp t) : Exp t := fun v => (e v).cfold
```

The theorem: a folded program means the same as the original.

```lean
theorem Exp'.cfold_denote (e : Exp' Ty.denote t) :
    e.cfold.denote = e.denote := by
  induction e with
  | var => rfl
  | const => rfl
  | plus a b iha ihb =>
    simp only [cfold]
    split <;> simp_all [denote]
  | lam b ih => funext x; exact ih x
  | app f a ihf iha => simp [cfold, denote, ihf, iha]

theorem Exp.cfold_denote (e : Exp t) : e.cfold.denote = e.denote :=
  Exp'.cfold_denote (e _)
```

The `lam` case is everything this proof has to say about binders:
`funext x; exact ih x`.{margin}[`funext` is function extensionality: two
functions are equal when they agree on every argument.] With a first-order
representation, the same theorem needs machinery of its own: an environment
for the evaluator, a lemma that looking up a variable in an extended
environment finds the new value, and weakening and renaming lemmas so that
the induction hypothesis still applies under a binder. With `v := Ty.denote`,
Lean's own function binder does that bookkeeping.

Another choice of `v` confirms that folding happened: with nothing stored at
variables, count the additions that remain.

```lean
def Exp'.plusCount : Exp' (fun _ => Unit) t → Nat
  | plus a b => a.plusCount + b.plusCount + 1
  | lam b => (b ()).plusCount
  | app f a => f.plusCount + a.plusCount
  | _ => 0

def Exp.plusCount (e : Exp t) : Nat := (e _).plusCount

def addThree : Exp (.nat ⇒ .nat) := fun _ =>
  lam fun x => plus (var x) (plus (const 1) (const 2))

example : addThree.plusCount = 2 := rfl
example : addThree.cfold.plusCount = 1 := rfl
example : addThree.cfold.denote 10 = 13 := rfl

end Typed
```
