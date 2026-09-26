import LeanHoas.Setup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Nameless, but Not Effortless" =>

{deftech}[De Bruijn indices] turn {tech (key := "alpha-equivalence")}[α-equivalence]
into plain equality: a variable is the number of binders between it and its
binder, so `λx. x` and `λy. y` are both `lam (var 0)`.{margin}[Named after
Nicolaas de Bruijn, who introduced them in 1972 for the Automath proof
checker. Lean's own terms are _locally nameless_: indices for bound
variables, unique identifiers for free ones.] Free variables are indices
that point past the outermost binder: at the top level, `var 0` is the first
free variable. The chore moves into index arithmetic, since a term that
moves under a binder must be shifted.

```lean
namespace DeBruijn

inductive Term where
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term
  deriving Repr, DecidableEq

open Term

def Term.shift (c : Nat) : Term → Term
  | var k => var (if k < c then k else k + 1)
  | lam b => lam (b.shift (c + 1))
  | app f a => app (f.shift c) (a.shift c)

def Term.instantiate (s : Term) : Term → Term := go 0 s
where
  go (j : Nat) (s : Term) : Term → Term
    | var k =>
      if k < j then var k
      else if k = j then s
      else var (k - 1)
    | lam b => lam (go (j + 1) (s.shift 0) b)
    | app f a => app (go j s f) (go j s a)

def Term.beta : Term → Term
  | app (lam b) a => b.instantiate a
  | t => t
```

`beta` performs the computation rule of the λ-calculus: applying `λx. b` to
an argument `a` gives `b[x := a]`. It is called {deftech}[β-reduction].
`instantiate` replaces index `j` by `s`, decrements the larger indices
because one binder has disappeared, and shifts `s` each time it goes under a
`lam`.

Take `(λx. λy. x) y` with `y` free. The result must be a constant function
returning that free `y`, which now sits one binder deeper:

```lean
example : (app (lam (lam (var 1))) (var 0)).beta =
    lam (var 1) := by
  decide

end DeBruijn
```

Forget one `shift` and the answer is `lam (var 0)`, that is `λy. y`:
{tech (key := "capture")}[capture] again, just spelled in numbers.
