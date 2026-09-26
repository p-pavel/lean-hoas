import LeanHoas.Setup

import LeanHoas.Recognition
import LeanHoas.Named
import LeanHoas.DeBruijn
import LeanHoas.Naive
import LeanHoas.PHOAS.Basic
import LeanHoas.PHOAS.Subst
import LeanHoas.PHOAS.Exotic
import LeanHoas.Typed.Basic
import LeanHoas.Typed.ConstFold

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Higher-Order Abstract Syntax in Lean" =>

Sooner or later, many programs grow a language: business rules, filters,
templates, queries, workflows. Once that language has variables, the program
has to handle variable binding, and binding is where the bugs are:
variables captured by the wrong definition, off-by-one index errors, and
theorems that hold only "up to renaming". Higher-order abstract syntax (HOAS)
hands most of that work to the language the implementation is written in. This
document builds the idea from scratch in Lean: first the pain, then the naive
idea and why Lean rejects it, then the parametric version (PHOAS) that works,
and finally a typed language with an interpreter and a verified optimization.

Two words recur. The {deftech}[object language] is the language being
implemented, the one whose syntax trees we build. The {deftech}[host language]
is the language doing the implementing, here Lean.{margin}[In the literature
the host language is also called the _meta-language_.]

*Who this is for.* Working programmers who are comfortable with functions,
types, recursion and pattern matching, and curious about Lean or about how
language tools work inside. No computer science degree is assumed, and this is
not a textbook. Terms from programming-language theory are explained in margin
notes where they first appear, so readers who already know them can skip the
notes. The Lean code is meant to be read, not memorized, and every block is
checked by Lean when the book is built.

*Where to start.* If you know the λ-calculus, α-equivalence, and de Bruijn
indices, skip ahead to {ref "binders-hard-way"}[Binders, the Hard Way].
Otherwise start with {ref "built-this-before"}[You Have Built This Before],
a one-page bridge from the rules and filter languages you may have built to
the vocabulary used here.

*How to read it.* The code in this book is live. Hover over a name, or tap
it on a phone, to see its type. In a proof, click or tap a step such as
`simp` or `funext` to see the proof state at that point: what is known, and
what remains to be shown. The sources are literate Lean, with text and code
in the same files, and they open in any editor with Lean support. Clone the
[repository](https://github.com/p-pavel/lean-hoas), change an example, and
Lean tells you at once what broke. Good first experiments: make `Term.subst`
in {ref "binders-hard-way"}[Binders, the Hard Way] avoid capture, try to
write the exotic term against
parametric HOAS, or break constant folding and watch its proof fail.

{include 1 LeanHoas.Recognition}

{include 1 LeanHoas.Named}

{include 1 LeanHoas.DeBruijn}

{include 1 LeanHoas.Naive}

{include 1 LeanHoas.PHOAS.Basic}

{include 1 LeanHoas.PHOAS.Subst}

{include 1 LeanHoas.PHOAS.Exotic}

{include 1 LeanHoas.Typed.Basic}

{include 1 LeanHoas.Typed.ConstFold}

# When PHOAS Is Inconvenient

PHOAS deliberately hides the identity of variables behind parametricity. That
is what makes renaming and substitution free, and it is also the cost:
operations that need to look at variable identity have to work for it.

 * A PHOAS term is a function, so it has no built-in equality test, printer,
   hash, or serialization. Each is an interpretation you write, like
   `Term.toNamed`.
 * `Term` quantifies over all types, so it is itself a "large" type, in
   `Type 1`. Anything declared to take an ordinary `Type`, including the `v`
   of `Term'` itself, cannot take a `Term`. Code works with `Term' v` inside
   and quantifies over `v` only at the edges, as `squash` does.
 * Theorems that relate two interpretations, such as printing and
   evaluation, need the well-formedness hypothesis, which must be proved for
   each term they are used on.
 * Questions such as "which variables are free here?" or "are these two
   occurrences the same variable?" need a `v` that can be inspected, such as
   `Nat`, or a conversion to de Bruijn form.
 * Going the other way, from a parser's output with names or indices to a
   PHOAS term, needs an environment and must handle unbound names. The
   bookkeeping the rest of the book avoids reappears at that boundary.
 * When renaming and substitution are themselves the subject of study, as in
   proofs about a type system itself, explicit first-order syntax keeps them
   visible.

Named and nameless representations are not obsolete. A reasonable design is
first-order syntax at the edges, for parsing, storage, and error messages,
and PHOAS in the middle, where terms are transformed, evaluated, and reasoned
about.

# The Idea on One Page

 * An object-language binder becomes a Lean `fun`. Lean then does the
   scoping, renaming, and substitution work.
 * Making the variable type a parameter, `Term' v`, keeps the datatype
   positive. Quantifying over it, `∀ v, Term' v`, says that a term works for
   any representation of variables.
 * The caveat: `∀ v` alone does not prove, inside Lean, that a term treats
   every `v` the same way. When a theorem compares two interpretations, it
   needs the well-formedness hypothesis.

Every operation chooses the representation of variables that suits it:

 * `v := Unit` forgets variable identity, to count occurrences.
 * `v := String` gives printable names.
 * `v := Nat` gives binder depths, and from them de Bruijn indices.
 * `v := Term' v₀` makes variables into syntax, which is substitution.
 * `v := Ty.denote` makes variables into values, which is evaluation, and
   the setting for proofs about evaluation.

# Where HOAS Is Native

Naive HOAS fails in Lean for two separate reasons: as an inductive type it
would make the logic inconsistent, and Lean's functions are rich enough to
build exotic terms. Logical frameworks avoid both. There,
`lam : (tm → tm) → tm` is a declared constant rather than an inductive type
with recursion over it, and the framework's functions contain only λ-terms.
Naive HOAS is then sound and _adequate_: object terms correspond one-to-one
to framework terms in normal form.

 * [Twelf](https://twelf.org): the LF logical framework with a logic
   programming engine for metatheory.
 * [Beluga](https://beluga-lang.readthedocs.io): contextual types let
   programs pattern-match on HOAS terms together with their contexts.
 * [Abella](https://abella-prover.org): a two-level logic whose `∇`
   quantifier reasons about fresh names.
 * λProlog: higher-order logic programming, with HOAS as its native idiom.

Further reading: Pfenning and Elliott, _Higher-Order Abstract Syntax_ (1988);
Chlipala, _Parametric Higher-Order Abstract Syntax for Mechanized Semantics_
(2008); Chlipala, _Certified Programming with Dependent Types_, chapter on
higher-order syntax.
