import LeanHoas.Setup
import LeanHoas.Named

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Let the Host Bind" =>

The host language already implements binding, scope, and substitution
correctly. Higher-order abstract syntax reuses that machinery: the body of an
object-level λ _is_ a host-level function. Substitution becomes function
application, and α-equivalence is inherited from the host.

Lean refuses the obvious declaration:

```lean +error -keep (name := negative)
inductive Term where
  | lam : (Term → Term) → Term
  | app : Term → Term → Term
```

```leanOutput negative
(kernel) arg #1 of 'Term.lam' has a non positive occurrence of the datatypes being declared
```

This is not pedantry. A type that occurs to the left of its own arrow can
inhabit the empty type:

```lean
namespace Naive

unsafe inductive Liar where
  | mk : (Liar → Empty) → Liar

noncomputable unsafe def Liar.paradox : Empty :=
  let refute : Liar → Empty := fun | .mk f => f (.mk f)
  refute (.mk refute)
```

# The idea runs

Outside the logic, marked `unsafe`, the idea computes. The extra constructor
`free` is a hole we need in order to look underneath a binder. Keep that in
mind: it comes back as the central design decision.

```lean
unsafe inductive Term where
  | lam : (Term → Term) → Term
  | app : Term → Term → Term
  | free : String → Term

namespace Term

unsafe def whnf : Term → Term
  | app f a => match whnf f with
    | lam body => whnf (body a)
    | f' => app f' a
  | t => t

unsafe def toNamed (n : Nat) : Term → Named.Term
  | lam b =>
    let x := s!"x{n}"
    .lam x (toNamed (n + 1) (b (free x)))
  | app f a => .app (toNamed n f) (toNamed n a)
  | free x => .var x

unsafe instance : ToString Term := ⟨fun t => toString (t.toNamed 0)⟩

unsafe def I : Term := lam fun x => x
unsafe def K : Term := lam fun x => lam fun _ => x
```

No substitution function was written, yet β-reduction works:

```lean (name := kab)
#eval (app (app K (free "a")) (free "b")).whnf
```

```leanOutput kab
a
```

# The host is too generous

Lean's function space contains far more than λ-bodies. This "term" inspects
its argument, which no λ-term can do:

```lean
unsafe def exotic : Term := lam fun
  | lam _ => free "saw-a-lambda"
  | _ => free "saw-something-else"
```

Looking under its binder, we find a constant function:

```lean (name := exoticShow)
#eval exotic
```

```leanOutput exoticShow
λx0. saw-something-else
```

Applying it disagrees:

```lean (name := exoticApp)
#eval (app exotic I).whnf

end Term
end Naive
```

```leanOutput exoticApp
saw-a-lambda
```

So naive HOAS has three problems: Lean rejects it, it admits exotic terms,
and going under a binder needs a variable the encoding does not have. One
change addresses all three.
