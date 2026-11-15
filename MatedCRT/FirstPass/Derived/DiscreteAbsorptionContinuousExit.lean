import MatedCRT.FirstPass.Derived.ExitDecomposition
import LatticeProb.Walk.ConstantStepPrefix

/-! # Continuous exit curves and discrete absorption -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open ExitDecomposition LatticeProb
open scoped NNReal ENNReal

/-- Absorption at the first vertex outside an open set preserves the continuous
first-exit curve, even when the interpolation leaves between two vertices. -/
theorem continuousExitCurve_stoppedPath (p : ℤ → Plane) {U : Set Plane}
    (hU : IsOpen U) {m : ℝ≥0} (hm : 0 < m) (x : ℕ → ℤ) :
    let A := p ⁻¹' U
    let f := ConstantStepInterpolation.continuousPlanePath m (fun n => p (x n))
    let g := ConstantStepInterpolation.continuousPlanePath m
      (fun n => p (stoppedPath A x n))
    normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal =
      normalizedPrefixCurve f (continuousExitTime U 0 f).toNNReal := by
  dsimp only
  by_cases ht : vExitTime (p ⁻¹' U) x = ⊤
  · rw [stoppedPath_of_top ht]
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 ht
    have hk' : vExitTime (p ⁻¹' U) x = (k : ℕ∞) := hk.symm
    have hout : p (x k) ∉ U :=
      ((MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec (p ⁻¹' U) x k).1 hk').1
    exact (ConstantStepInterpolation.continuousExitTime_and_curve_eq_of_prefix hm
      (fun n hn => congrArg p (stoppedPath_of_le hk' hn).symm) hU hout).2.2

end MatedCRT
end
