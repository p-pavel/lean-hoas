import LeanHoas.Setup
import LeanHoas.PHOAS.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Substitution Is Instantiation" =>

A term with one free variable is a function from variables to terms. To
substitute, choose the variables to _be_ terms, then flatten the result.
There is no traversal that renames or shifts anything.

```lean
namespace PHOAS
open Term'

def Term1 := ∀ v, v → Term' v

def Term'.squash : Term' (Term' v) → Term' v
  | var e => e
  | lam b => lam fun x => (b (var x)).squash
  | app f a => app f.squash a.squash

def Term1.subst (e : Term1) (s : Term1) : Term1 :=
  fun v z => (e (Term' v) (s v z)).squash

def Term1.toNamed (e : Term1) (free : String) : Named.Term :=
  (e String free).toNamed 0
```

This is the substitution that the named encoding got wrong in the first
chapter: `(λy. x)[x := y]`, with `y` free.

```lean
def constX : Term1 := fun _ x => lam fun _ => var x
def freeY : Term1 := fun _ y => var y
```

```lean (name := noCapture)
#eval (constX.subst freeY).toNamed "y"
```

```leanOutput noCapture
λx0. y
```

The binder and the free variable can never meet: one is a Lean `fun`, the
other is a value supplied from outside.

# β-reduction

Head β-reduction on closed terms is the same trick one level up:

```lean
def Term'.headBeta : Term' (Term' v) → Term' v
  | app (lam b) a => (b a.squash).squash
  | e => e.squash

def Term.app (f a : Term) : Term := fun v => .app (f v) (a v)

def Term.headBeta (e : Term) : Term := fun v => (e (Term' v)).headBeta
```

```lean (name := twoI)
#eval (two.app I).headBeta.toNamed

end PHOAS
```

```leanOutput twoI
λx0. (λx1. x1) ((λx1. x1) x0)
```
