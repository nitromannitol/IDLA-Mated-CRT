import MatedCRT.Proofs.IDLA.WalkerLawMeasurable

/-! # Characterization of the annealed IDLA law -/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory

/-- On valid environments the totalized joint outer probability is the outer
measure of the joint law, including for events which are not measurable. -/
theorem MatedCRTEnv.IsValid.jointOuterProb_eq_idlaJointLaw
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    (E : Set (Ω × (ℕ → ℕ → ℤ))) :
    jointOuterProb S.P (fun ω => walkerSequenceLaw (S.mult ε ω) 0) E =
      hS.idlaJointLaw ε E := by
  rw [S.jointOuterProb_eq_idlaJointMeasure, hS.idlaJointMeasure_eq]

/-- On measurable events the joint outer probability is the integral of the
conditional probabilities of the walker sections. -/
theorem MatedCRTEnv.IsValid.jointOuterProb_eq_lintegral
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ)
    {E : Set (Ω × (ℕ → ℕ → ℤ))} (hE : MeasurableSet E) :
    jointOuterProb S.P (fun ω => walkerSequenceLaw (S.mult ε ω) 0) E =
      ∫⁻ ω, walkerSequenceLaw (S.mult ε ω) 0 (Prod.mk ω ⁻¹' E) ∂S.P := by
  rw [hS.jointOuterProb_eq_idlaJointLaw ε E]
  exact hS.idlaJointLaw_apply ε hE

end MatedCRT
