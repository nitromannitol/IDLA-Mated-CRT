import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# First pass: measurable decoder of an injective Borel graph

The Borel injective-projection theorem therefore gives a Borel
decoder on the set of measures admitting such a `w`. Extend it by the zero function outside that Borel set." This file is
the abstract form of that step (Lusin-Souslin, Kechris 15.1-15.2): a measurable graph whose first projection is injective
has a measurable section, defined on the projection, and equal to a fixed default value off the projection.
-/

namespace MatedCRT

open MeasureTheory Set Function

/-- **Measurable section of an injective Borel graph** (Lusin-Souslin). Let `G ⊆ X × Y` be measurable with `X`, `Y`
standard Borel, and suppose that each `x` has at most one `y` with `(x, y) ∈ G`. Then there is a measurable `F : X → Y`
with `(x, F x) ∈ G` whenever `x` is in the projection of `G`, and `F x = y₀` (a chosen default value) otherwise. -/
theorem exists_measurable_section_of_injective {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] (y₀ : Y) (G : Set (X × Y)) (hG : MeasurableSet G)
    (hinj : ∀ x y₁ y₂, (x, y₁) ∈ G → (x, y₂) ∈ G → y₁ = y₂) :
    ∃ F : X → Y, Measurable F ∧ (∀ x, (∃ y, (x, y) ∈ G) → (x, F x) ∈ G) ∧
      ∀ x, (¬ ∃ y, (x, y) ∈ G) → F x = y₀ := by
  have : StandardBorelSpace G := hG.standardBorel
  let p : G → X := fun q => q.1.1
  let g : G → Y := fun q => q.1.2
  have hp : Measurable p := measurable_fst.comp measurable_subtype_coe
  have hg : Measurable g := measurable_snd.comp measurable_subtype_coe
  have hpinj : Injective p := by
    intro q₁ q₂ h
    have hx : q₁.1.1 = q₂.1.1 := h
    apply Subtype.ext
    exact Prod.ext hx (hinj _ _ _ q₁.2 (hx ▸ q₂.2))
  have hemb : MeasurableEmbedding p := Measurable.measurableEmbedding hp hpinj
  refine ⟨Function.extend p g (fun _ => y₀), hemb.measurable_extend hg measurable_const, ?_, ?_⟩
  · rintro x ⟨y, hy⟩
    have hx : x ∈ Set.range p := ⟨⟨(x, y), hy⟩, rfl⟩
    obtain ⟨q, rfl⟩ := hx
    rw [hpinj.extend_apply]
    exact q.2
  · intro x hx
    rw [Function.extend_apply']
    rintro ⟨q, hq⟩
    exact hx ⟨q.1.2, by
      have : q.1.1 = x := hq
      rw [← this]
      exact q.2⟩

end MatedCRT
