import LeanHoas.Setup
import LeanHoas.PHOAS.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Small Print: Parametricity" =>

Quantifying over `v` is meant to stop a term from inspecting `v`. That
guarantee is _parametricity_, and it is a theorem _about_ Lean's type theory,
not a statement Lean can use internally. Classical logic can branch on which
type it was handed, so different interpretations of the "same" term can
disagree.

```lean
namespace PHOAS
open Term'

open Classical in
noncomputable def chameleon : Term := fun v => if v = Unit then two v else I v
```

Counting sees `two`; printing sees `I`:

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

# Well-formedness

The fix is to state the missing theorem per term instead of for the whole
type. A term is well-formed when any two of its interpretations have the
same shape, with variables paired up by their binders:

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
