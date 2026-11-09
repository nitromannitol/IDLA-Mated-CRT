import MatedCRT.FirstPass.Frozen.S1c

/-! # Full Borel image of a Borel event of full measure (plan H2, q1, fp-S2g)

The measure-theoretic lemma of `notes/fp-gaps/CHATGPT-q1-open-steps.md` section 2 (eq. (2)), used for the Borel full set of
local measures in H2. Let `F : Z → X` be measurable between Polish spaces, `P` a probability on `Z`, and `E` a measurable set
with `P E = 1`. The image `F '' E` is analytic (Mathlib `MeasurableSet.analyticSet_image`), hence null-measurable for the law
`P.map F` by the frozen Lusin input `FrozenUniversalMeasurabilityOfAnalytic` (`FirstPass/Frozen/S1c.lean:40`). It has full
law because `E ⊆ F ⁻¹' (F '' E)`. A Borel subset of full law then lies inside `F '' E`. -/

namespace MatedCRT

open MeasureTheory

/-- **Full Borel image (fp-S2g, q1).** Under `FrozenUniversalMeasurabilityOfAnalytic`, a measurable `F` between Polish
spaces and a measurable event `E` of full measure, there is a Borel set `B ⊆ F '' E` of full law `P.map F`. -/
theorem exists_measurable_subset_image_full_law (hU : FrozenUniversalMeasurabilityOfAnalytic)
    {Z X : Type} [MeasurableSpace Z] [StandardBorelSpace Z] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (P : Measure Z) [IsProbabilityMeasure P] (F : Z → X)
    (hF : Measurable F) (E : Set Z) (hE : MeasurableSet E) (hPE : P E = 1) :
    ∃ B : Set X, MeasurableSet B ∧ B ⊆ F '' E ∧ P.map F B = 1 := by
  have hQ : IsProbabilityMeasure (P.map F) := (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).mpr inferInstance
  have hAn : NullMeasurableSet (F '' E) (P.map F) :=
    hU X (P.map F) inferInstance (F '' E) (hE.analyticSet_image hF)
  have hle : P E ≤ P.map F (F '' E) :=
    calc P E ≤ P (F ⁻¹' (F '' E)) := measure_mono fun z hz => ⟨z, hz, rfl⟩
      _ ≤ P.map F (F '' E) := Measure.le_map_apply hF.aemeasurable _
  have hQA : P.map F (F '' E) = 1 := by
    rw [hPE] at hle
    exact le_antisymm prob_le_one hle
  obtain ⟨S, hS, hAS⟩ := hAn
  have hD : P.map F {x | ¬ (x ∈ F '' E ↔ x ∈ S)} = 0 :=
    measure_mono_null (fun x hx => fun heq => hx (eq_iff_iff.mp heq)) (ae_iff.1 hAS)
  have hNm : MeasurableSet (toMeasurable (P.map F) {x | ¬ (x ∈ F '' E ↔ x ∈ S)}) :=
    measurableSet_toMeasurable _ _
  have hN0 : P.map F (toMeasurable (P.map F) {x | ¬ (x ∈ F '' E ↔ x ∈ S)}) = 0 := by
    rw [measure_toMeasurable, hD]
  have hSQ : P.map F S = 1 := (measure_congr hAS).symm.trans hQA
  refine ⟨S \ toMeasurable (P.map F) {x | ¬ (x ∈ F '' E ↔ x ∈ S)}, hS.diff hNm, ?_, ?_⟩
  · intro x hx
    by_contra hxA
    exact hx.2 (subset_toMeasurable _ _ (fun h => hxA (h.mpr hx.1)))
  · rw [measure_sdiff_null hN0, hSQ]

end MatedCRT
