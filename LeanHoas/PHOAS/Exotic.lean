import LeanHoas.Setup
import LeanHoas.PHOAS.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Small Print: Parametricity" =>

Quantifying over `v` is meant to stop a term from depending on which `v` it
is given. That guarantee is {deftech}[parametricity]: a polymorphic
definition behaves the same way at every type.{margin}[The word is
Christopher Strachey's (1967); the relational formulation used below is John
Reynolds' (1983). Philip Wadler's paper "Theorems for free!" (1989) made it
popular with programmers.] For many languages it is a theorem _about_ the
language, proved from outside. Lean's logic does not contain it, and
classical reasoning can branch on which type a definition was handed. The
interpretations of the "same" term can then disagree.{margin}[Lean's logic
includes the law of the excluded middle, so `if v = Unit then … else …` is
allowed even though no program could decide it. Such definitions cannot be
compiled, and are marked `noncomputable`.]

```lean
namespace PHOAS
open Term'

open Classical in
noncomputable def chameleon : Term := fun v => if v = Unit then two v else I v
```

This is an {tech}[exotic term] of a new kind: it does not inspect its
argument, it inspects the type. Counting sees `two`; printing sees `I`.
Lean needs a proof even that `String ≠ Unit`: if the two were equal, `▸`
would carry "all `Unit` values are equal" over to `String`, giving
`"a" = "b"`.{margin}[`simp` rewrites the goal with the listed definitions
and lemmas, plus a standard set, until it closes.]

```lean
theorem string_ne_unit : String ≠ Unit := by
  intro h
  have : ∀ a b : String, a = b := h ▸ fun (_ _ : Unit) => rfl
  exact absurd (this "a" "b") (by decide)

example : chameleon.count = 3 := by
  simp [chameleon, Term.count, two, Term'.count]

example : chameleon.toNamed = .lam "x0" (.var "x0") := by
  simp [chameleon, Term.toNamed, string_ne_unit, I, Term'.toNamed]
  rfl
```

# Well-Formedness

The fix is to state the missing uniformity for each term, as a property we
can prove, instead of expecting the type to guarantee it. Interpret the term
at two variable types at once, and require the two results to have the same
shape, with variables paired up by the binder that introduced them. This is
Reynolds' relational parametricity in miniature: a relation between two
instantiations that the term must respect. `Γ` lists the pairs of variables
bound so far.{margin}[An `inductive … → Prop` defines a relation by rules:
each constructor is one way to establish it. Names such as `Γ` and `b₁` that
are used without being declared become implicit arguments.]

```lean
inductive Term'.Equiv {v₁ v₂ : Type} :
    List (v₁ × v₂) → Term' v₁ → Term' v₂ → Prop
  | var : (x, y) ∈ Γ → Equiv Γ (var x) (var y)
  | lam : (∀ x y, Equiv ((x, y) :: Γ) (b₁ x) (b₂ y)) →
      Equiv Γ (lam b₁) (lam b₂)
  | app : Equiv Γ f₁ f₂ → Equiv Γ a₁ a₂ →
      Equiv Γ (app f₁ a₁) (app f₂ a₂)

def Term.Wf (e : Term) : Prop := ∀ v₁ v₂, Term'.Equiv [] (e v₁) (e v₂)
```

Honest terms are well-formed by a proof that mirrors their shape:

```lean
theorem two_wf : two.Wf := fun _ _ =>
  .lam fun _ _ => .lam fun _ _ =>
    .app (.var (by simp)) (.app (.var (by simp)) (.var (by simp)))
```

The chameleon is not:

```lean
theorem chameleon_not_wf : ¬ chameleon.Wf := by
  intro h
  have h := h Unit String
  simp only [chameleon, if_pos, if_neg string_ne_unit, two, I] at h
  cases h with
  | lam h => cases h () "x"

end PHOAS
```

Theorems that relate two interpretations, such as "printing then parsing
gives back the term", need `Wf` as a hypothesis. Theorems that use a single
interpretation do not, and the next chapters live entirely in that case.
