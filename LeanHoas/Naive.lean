import LeanHoas.Setup
import LeanHoas.Named

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Let the Host Bind" =>

The {tech}[host language] already implements binding, scope, and
substitution correctly. {deftech}[Higher-order abstract syntax] reuses that
machinery.{margin}[Named by Frank Pfenning and Conal Elliott in 1988. The
idea goes back to Alonzo Church, whose 1940 theory of types writes
"for all `x`, `P`" as a constant applied to a function: `Π (λx. P)`.]
_Abstract syntax_ means the tree, not the text: the structure a parser
produces. _Higher-order_ is meant as in "higher-order function": the
tree contains functions. The body of an object-language λ is no longer data
with a name in it; it _is_ a host-language function, waiting for its
argument. Substitution becomes function application, and renaming bound
variables becomes Lean's business instead of ours.

Lean refuses the obvious declaration:

```lean +error -keep (name := negative)
inductive Term where
  | lam : (Term → Term) → Term
  | app : Term → Term → Term
```

```leanOutput negative
(kernel) arg #1 of 'Term.lam' has a non positive occurrence of the datatypes being declared
```

The _kernel_ is Lean's small trusted core, which re-checks every definition.
It requires a type to occur only _strictly positively_ in its own
constructors: never to the left of an arrow, as `Term` does in
`Term → Term`. This is not pedantry. A type that occurs to the left of its
own arrow lets us build a value of the empty type:{margin}[`Empty` has no
values. A program that produced one would let us prove anything, so the
kernel rejects such types instead of trusting the programmer.]

```lean
namespace Naive

unsafe inductive Liar where
  | mk : (Liar → Empty) → Liar

noncomputable unsafe def Liar.paradox : Empty :=
  let refute : Liar → Empty := fun | .mk f => f (.mk f)
  refute (.mk refute)
```

Run as a program, `paradox` loops forever; read as a proof, it proves
anything.{margin}[`.mk f` is short for `Liar.mk f`: Lean infers the type from
context. `fun | p => e` defines a function by pattern matching.
`noncomputable` here only tells Lean not to compile the definition.]

# The Idea Runs

Marked `unsafe`, the idea computes.{margin}[`unsafe` declarations skip the
kernel's checks. They can run, but no safe definition or theorem may refer
to them. This changes the status of the construction; it does not solve the
problem.] The
extra constructor `free` is a hole we need in order to look underneath a
binder. Keep that in mind: it comes back as the central design decision.

```lean
unsafe inductive Term where
  | lam : (Term → Term) → Term
  | app : Term → Term → Term
  | free : String → Term

namespace Term

unsafe def reduce : Term → Term
  | app f a => match reduce f with
    | lam body => reduce (body a)
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

No substitution function was written, yet {tech}[β-reduction] works:

```lean (name := kab)
#eval (app (app K (free "a")) (free "b")).reduce
```

```leanOutput kab
a
```

`toNamed` uses the trick worth remembering: to see inside a function, call it
with a placeholder and inspect what comes back. You may have used tools that
do exactly this. Scala's Slick library calls the callback in
`users.filter(_.age > 18)` with a symbolic row instead of a real one, to
learn which query you meant. Tracing compilers such as JAX or PyTorch's
`torch.fx` run your Python function on placeholder values to record what it
computes. They also meet the problem shown next: a single trace cannot
capture a function that branches on its argument, so such code is rejected
or only the branch taken is recorded.

# The Host Is Too Generous

Lean's function space contains far more than λ-bodies. This
{deftech}[exotic term] inspects its argument, which no λ-term can do:

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
#eval (app exotic I).reduce

end Term
end Naive
```

```leanOutput exoticApp
saw-a-lambda
```

So naive HOAS has three problems: Lean rejects it, it admits exotic terms,
and going under a binder needs a variable the encoding does not have. One
change addresses all three, the second with a caveat we return to later.
