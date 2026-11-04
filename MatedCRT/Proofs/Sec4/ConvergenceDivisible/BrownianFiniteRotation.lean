import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuousPathFiniteLaws

/-! # Rotation invariance of finite Brownian laws -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped NNReal

/-- A finite family of Brownian evaluations has mean zero. -/
theorem unitPathRestriction_finite_mean_zero (I : Finset UnitTime) :
    (∫ w, I.restrict (fun t => unitPathRestriction w t) ∂brownianMotion 0) = 0 := by
  let V : ContinuousPath ℝ → I → ℝ :=
    fun w => I.restrict (fun t => unitPathRestriction w t)
  have hV : Integrable V (brownianMotion 0) :=
    (unitPathRestriction_finite_gaussian I).integrable
  change (∫ w, V w ∂brownianMotion 0) = 0
  ext t
  have h := (ContinuousLinearMap.proj t : (I → ℝ) →L[ℝ] ℝ).integral_comp_comm hV
  simpa [V, unitPathRestriction] using
    h.symm.trans (canonical_isPreBrownianReal.integral_eval t.1.1)

/-- Two independent finite Brownian vectors are invariant under every rotation. -/
theorem unitPathRestriction_finite_rotation (I : Finset UnitTime) (θ : ℝ) :
    let μ := (brownianMotion 0).map
      (fun w => I.restrict (fun t => unitPathRestriction w t))
    (μ.prod μ).map (ContinuousLinearMap.rotation θ) = μ.prod μ := by
  let V : ContinuousPath ℝ → I → ℝ :=
    fun w => I.restrict (fun t => unitPathRestriction w t)
  let μ := (brownianMotion 0).map V
  have hV := unitPathRestriction_finite_gaussian I
  have : IsGaussian μ := hV.isGaussian_map
  have hzero : μ[id] = 0 := by
    rw [integral_map hV.aemeasurable (by fun_prop)]
    exact unitPathRestriction_finite_mean_zero I
  exact IsGaussian.map_rotation_eq_self hzero θ

end MatedCRT
