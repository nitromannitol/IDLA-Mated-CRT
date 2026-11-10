import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), measure layer, step M1): exact field-measurable modification

Generic measure theory, no frozen input. Let `m ≤ mΩ` be the field σ-algebra and `P` a probability measure on `Ω`.
Let `Y : Ω → X` be `m`-measurable (for instance the moment vector `ω ↦ (∫ φ_k dμ_g(ω))_k` of the field-measurable
version `g` of the LQG measure) and let `S ⊆ X` be universally measurable: `S` is `Q`-null measurable for every finite
measure `Q` on `X` (for analytic `S` in a Polish `X` this is the frozen input `FrozenUniversalMeasurabilityOfAnalytic`).
Then there are a Borel set `B ⊆ X` and an `m`-measurable `P`-null set `N ⊆ Ω` with `Y ω ∈ S ↔ Y ω ∈ B` for `ω ∉ N`.

Hence the preimage `Y⁻¹ S` is `P`-almost surely equal to the `m`-measurable set `Y⁻¹ B`. This avoids a trimmed
almost-sure equality: the exceptional set is the preimage of a Borel `Q`-null set, which is `m`-measurable and `P`-null.
Terminology: the field σ-algebra of Duplantier-Sheffield (the σ-algebra of the GFF pairings), Armstrong-Kuusi-Mourrat
(analytic sets in the moment space).
-/

namespace MatedCRT.S5c

open MeasureTheory

theorem exists_borel_null_modification {Ω X : Type*} [mΩ : MeasurableSpace Ω] {m : MeasurableSpace Ω} [MeasurableSpace X]
    (hm : m ≤ mΩ) {P : @Measure Ω mΩ} [IsProbabilityMeasure P] {Y : Ω → X} (hY : Measurable[m] Y)
    {S : Set X} (hS : ∀ Q : Measure X, IsFiniteMeasure Q → NullMeasurableSet S Q) :
    ∃ B : Set X, MeasurableSet B ∧ ∃ N : Set Ω, MeasurableSet[m] N ∧ P N = 0 ∧
      ∀ ω, ω ∉ N → (Y ω ∈ S ↔ Y ω ∈ B) := by
  let μm : @Measure Ω m := P.trim hm
  have : IsFiniteMeasure μm := inferInstance
  let Q : Measure X := @Measure.map Ω X m _ Y μm
  obtain ⟨B, hB, hSB⟩ := hS Q inferInstance
  have hE0 : Q {x | ¬ (x ∈ S ↔ x ∈ B)} = 0 := ae_iff.1 (Filter.eventuallyEqSet_iff.1 hSB)
  let Z : Set X := toMeasurable Q {x | ¬ (x ∈ S ↔ x ∈ B)}
  have hZ : MeasurableSet Z := measurableSet_toMeasurable _ _
  have hQZ : Q Z = 0 := by
    rw [measure_toMeasurable]
    exact hE0
  have hsub : {x | ¬ (x ∈ S ↔ x ∈ B)} ⊆ Z := subset_toMeasurable _ _
  refine ⟨B, hB, Y ⁻¹' Z, hY hZ, ?_, ?_⟩
  · rw [← trim_measurableSet_eq hm (hY hZ), ← Measure.map_apply hY hZ]
    exact hQZ
  · intro ω hω
    by_contra h
    exact hω (hsub (show Y ω ∈ {x | ¬ (x ∈ S ↔ x ∈ B)} from h))

end MatedCRT.S5c
