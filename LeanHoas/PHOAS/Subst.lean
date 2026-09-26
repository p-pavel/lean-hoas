import LeanHoas.Setup
import LeanHoas.PHOAS.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Substitution Is Instantiation" =>

Substitution is the next choice of `v`, and the least obvious one:

 1. Normally `v` stands for the object language's variables.
 2. For substitution, choose `v` to be syntax itself: `v := Term' v₀`.
 3. A term then has type `Term' (Term' v₀)`, a tree whose variables are trees.
 4. So a variable can literally contain the term that should replace it.
 5. `squash` removes the extra layer, the way flattening turns a list of
    lists into a list.

Nothing renames or shifts anything.{margin}[For readers who know monads:
`var` and `squash` look like `pure` and `join`, and substitution like `bind`.
But `Term'` is not even a functor in `v`, because a binder takes a `v` as
input. `squash` works anyway, because a binder's argument can always be
wrapped back into syntax with `var`.] A term with one free variable is a
function from that variable to a term, `Term1`:

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
other is a value supplied from outside, so there is nothing to
{tech (key := "capture")}[capture].

# β-Reduction

One step of {tech}[β-reduction] at the top of a closed term is the same trick
one level up. `Term.app` applies one closed term to another by instantiating
both at the same `v`:

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

That is `λx. I (I x)`: `f` became `I`. The inner applications remain,
because `headBeta` reduces only at the top.
