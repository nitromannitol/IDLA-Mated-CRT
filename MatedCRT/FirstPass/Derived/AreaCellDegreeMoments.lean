import MatedCRT.FirstPass.Derived.DegreeBoundOfLemma25Tail

/-! # Moments of degrees of the mated-CRT map -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace MatedCRT

/-- The labelled edge-end degree has finite moments in every valid environment. -/
theorem MatedCRTEnv.IsValid.lintegral_labelledDegree_pow_lt_top
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε)
    (x : ℤ) (k : ℕ) :
    ∫⁻ ω, ((MatedCRTHarmonic.MatedCRT.lemma25Degree ε (S.bm ω) x : ℕ∞) : ℝ≥0∞) ^ k ∂S.P < ⊤ := by
  obtain ⟨hlaw, hmeas⟩ := hS.isCorrelatedBM2_map_bm
  have hm : Measurable (fun p =>
      ((MatedCRTHarmonic.MatedCRT.lemma25Degree ε p x : ℕ∞) : ℝ≥0∞) ^ k) :=
    ((measurable_of_countable ENat.toENNReal).comp
      (MatedCRTHarmonic.MatedCRT.measurable_lemma25Degree ε x)).pow_const k
  rw [← lintegral_map hm hmeas]
  exact MatedCRTHarmonic.MatedCRT.lemma25Tail_lintegral_degree_pow_lt_top hlaw hε x k

/-- Every moment of the full multiplicity degree is finite. -/
theorem MatedCRTEnv.IsValid.lintegral_matedDeg_pow_lt_top
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε)
    (x : ℤ) (k : ℕ) :
    ∫⁻ ω, ((matedDeg (S.mult ε ω) x : ℕ) : ℝ≥0∞) ^ k ∂S.P < ⊤ := by
  apply (lintegral_mono fun ω => ?_).trans_lt (hS.lintegral_labelledDegree_pow_lt_top hε x k)
  apply pow_le_pow_left' _ k
  have h := matedDeg_bmEdgeCount_le_encard ε (S.bm ω) x
  simpa [MatedCRTHarmonic.MatedCRT.lemma25Degree,
    MatedCRTHarmonic.MatedCRT.lemma25IncidentDarts, MatedCRTEnv.mult] using ENat.toENNReal_mono h

end MatedCRT
