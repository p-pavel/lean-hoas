import LeanHoas.Setup

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

Sooner or later, many programs grow a language. It starts as a filter
expression, a rule engine, a template or configuration language, a query
builder, a workflow definition. Once users can write something like "for
every order `o`, `o.total > 100`", the program has to represent code as data:
a syntax tree for a language with variables. From then on it must answer the
questions every language implementer meets. Which `o` does this `o` refer
to? What happens when one expression is plugged into another?

That is the problem of variable binding, and it is where the bugs are:
variables captured by the wrong definition, off-by-one index errors, and
theorems that hold only "up to renaming". Higher-order abstract syntax (HOAS)
hands all of it to the programming language you are already writing in. This
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

Lean's function space is too rich for naive HOAS, which is why PHOAS is
needed. Logical frameworks make the opposite design choice: their function
space contains only λ-terms, so naive HOAS is adequate there. Proofs of
adequacy show that object terms correspond exactly to canonical framework
terms.

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
