import MatedCRT.FirstPass.Derived.BrownianExitLawIdentification

/-! Weak continuity of the stopped Brownian endpoint law on bounded open domains. -/

set_option autoImplicit false

open MeasureTheory Set HarmonicBalls MarkovProcess BouRabeeGwynne
open scoped Topology

namespace MatedCRT.BrownianExitLawIdentification

/-- The endpoint of a stopped standard Brownian curve, as a probability measure. -/
noncomputable def stoppedBrownianEndpointProbability (V : Set (Euc 2))
    (hV : IsOpen V) (μ : Measure (BrownianPath 2)) (hμ : IsStandardBrownianLaw μ)
    (z : Euc 2) : ProbabilityMeasure (Euc 2) := by
  letI : IsProbabilityMeasure μ := hμ.1
  letI : IsProbabilityMeasure (stoppedBrownianLaw V z μ) :=
    stoppedBrownianLaw_isProbabilityMeasure hV z μ
  exact ⟨(stoppedBrownianLaw V z μ).map CurveSpace.endPoint,
    (Measure.isProbabilityMeasure_map_iff
      CurveSpace.continuous_endPoint.measurable.aemeasurable).mpr inferInstance⟩

/-- The endpoint kernel is weakly continuous at interior starts. -/
theorem continuous_stoppedBrownianEndpointProbability {V : Set (Euc 2)}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (μ : Measure (BrownianPath 2)) (hμ : IsStandardBrownianLaw μ) :
    Continuous (fun z : V => stoppedBrownianEndpointProbability V hV μ hμ z) := by
  let R := Complex.orthonormalBasisOneI.repr
  let U : Set ℂ := R.symm '' V
  have hU : IsOpen U := R.symm.toHomeomorph.isOpenMap V hV
  have hUb : Bornology.IsBounded U := R.symm.isometry.lipschitzWith.isBounded_image hVb
  have hRU : R '' U = V := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [R.apply_symm_apply] using hw
    · intro x hx
      exact ⟨R.symm x, ⟨x, hx, rfl⟩, R.apply_symm_apply x⟩
  let f : V → U := fun z => ⟨R.symm z, ⟨z, z.property, rfl⟩⟩
  have hf : Continuous f := R.symm.continuous.comp continuous_subtype_val |>.subtype_mk _
  have heq (z : V) : stoppedBrownianEndpointProbability V hV μ hμ z =
      (planarBrownianExitProbability U hU (f z)).map R := by
    apply Subtype.ext
    change (stoppedBrownianLaw V (z : Euc 2) μ).map CurveSpace.endPoint =
      ((planarBrownianExitProbability U hU (R.symm z) : ProbabilityMeasure ℂ) :
        Measure ℂ).map R
    have h := stoppedBrownianLaw_endPoint_eq U hU (f z) μ hμ
    change (stoppedBrownianLaw (R '' U) (R (R.symm z)) μ).map CurveSpace.endPoint =
      ((planarBrownianExitProbability U hU (R.symm z) : ProbabilityMeasure ℂ) :
        Measure ℂ).map R at h
    simpa only [hRU, R.apply_symm_apply] using h
  simp only [heq]
  exact (continuous_euclidean_planarBrownianExitProbability hU hUb).comp hf

/-- Restricting the endpoint kernel to any subset of the domain preserves continuity. -/
theorem continuous_stoppedBrownianEndpointProbability_on {V K : Set (Euc 2)}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hK : K ⊆ V)
    (μ : Measure (BrownianPath 2)) (hμ : IsStandardBrownianLaw μ) :
    Continuous (fun z : K => stoppedBrownianEndpointProbability V hV μ hμ z) := by
  exact (continuous_stoppedBrownianEndpointProbability hV hVb μ hμ).comp
    (continuous_subtype_val.subtype_mk fun z : K => hK z.property)

end MatedCRT.BrownianExitLawIdentification
