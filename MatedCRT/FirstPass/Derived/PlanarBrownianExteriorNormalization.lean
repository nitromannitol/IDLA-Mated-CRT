import MatedCRT.FirstPass.Derived.PlanarBrownianExteriorHomeomorphism

/-! # Affine normalization of exterior planar Brownian exit laws -/

set_option autoImplicit false
noncomputable section

open MeasureTheory HarmonicBalls

namespace MatedCRT

/-- An exterior planar Brownian exit law is preserved by an invertible affine
normalization, also for unbounded domains. -/
theorem planarBrownianExitProbability_normalize_of_not_mem
    (U : Set ℂ) (hU : IsOpen U) (c z : ℂ) (hz : z ∉ U)
    {r : ℝ} (hr : r ≠ 0) :
    let W := (fun w : ℂ => c + r • w) ⁻¹' U
    let hW : IsOpen W := hU.preimage (by fun_prop)
    ((planarBrownianExitProbability U hU z : ProbabilityMeasure ℂ) : Measure ℂ).map
        (fun w => r⁻¹ • (w - c)) =
      ((planarBrownianExitProbability W hW (r⁻¹ • (z - c)) : ProbabilityMeasure ℂ) :
        Measure ℂ) := by
  let F : ℂ ≃ₜ ℂ := (Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addLeft c)
  have hFinv : ∀ w : ℂ, F.symm w = r⁻¹ • (w - c) := by
    intro w
    change r⁻¹ • (-c + w) = r⁻¹ • (w - c)
    rw [sub_eq_add_neg, add_comm]
  have hF : (F : ℂ → ℂ) = fun w => c + r • w := rfl
  have hFinv' : (F.symm : ℂ → ℂ) = fun w => r⁻¹ • (w - c) :=
    funext hFinv
  have h := planarBrownianExitProbability_map_homeomorph_of_not_mem hU z hz F.symm
  simpa only [Homeomorph.symm_symm, hF, hFinv'] using h

end MatedCRT
end
