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

end MatedCRT
