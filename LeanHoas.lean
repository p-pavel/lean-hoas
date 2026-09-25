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

Every language implementation eventually has to handle variable binding, and
binding is where the bugs are: capture, forgotten shifts, and theorems that
hold only up to renaming. Higher-order abstract syntax lets the host language
handle all of it. This document builds the idea from scratch in Lean: first
the pain, then the naive idea and why Lean rejects it, then the parametric
version that works, and finally a typed language with an interpreter and a
verified optimization.

{include 1 LeanHoas.Named}

{include 1 LeanHoas.DeBruijn}

{include 1 LeanHoas.Naive}

{include 1 LeanHoas.PHOAS.Basic}

{include 1 LeanHoas.PHOAS.Subst}

{include 1 LeanHoas.PHOAS.Exotic}

{include 1 LeanHoas.Typed.Basic}

{include 1 LeanHoas.Typed.ConstFold}

# Where HOAS Is Native

Lean's function space is too rich for naive HOAS, which is why the parametric
detour is needed. Logical frameworks make the opposite design choice: their
function space contains only λ-terms, so naive HOAS is adequate there. Proofs
of adequacy show that object terms correspond exactly to canonical framework
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
