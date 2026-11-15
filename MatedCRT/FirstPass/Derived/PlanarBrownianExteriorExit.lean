import MatedCRT.FirstPass.Derived.BrownianExitKernelContinuity

/-! # Planar Brownian exit laws at exterior points -/

set_option autoImplicit false
noncomputable section

open MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

/-- The first-exit law from an open set is a point mass at an exterior start. -/
theorem planarBrownianExitProbability_eq_dirac_of_not_mem {U : Set ℂ}
    (hU : IsOpen U) (z : ℂ) (hz : z ∉ U) :
    ((planarBrownianExitProbability U hU z : ProbabilityMeasure ℂ) : Measure ℂ) =
      Measure.dirac z := by
  change (planarBrownianMotion z).map
    (fun ω => ω ((ContinuousPath.exitTime U ω).toNNReal)) = Measure.dirac z
  have h : (fun ω : ContinuousPath ℂ => ω ((ContinuousPath.exitTime U ω).toNNReal))
      =ᵐ[planarBrownianMotion z] (fun _ => z) := by
    filter_upwards [ae_planarBrownianMotion_eval_zero z] with ω hω
    have ht : ContinuousPath.exitTime U ω = 0 := by
      apply le_antisymm _ bot_le
      apply sInf_le
      exact ⟨0, by simp, by simpa only [hω] using hz⟩
    simpa only [ht, ENNReal.toNNReal_zero] using hω
  rw [Measure.map_congr h, Measure.map_const, measure_univ, one_smul]

end MatedCRT
end
