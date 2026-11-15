import MatedCRT.FirstPass.Derived.PlanarBrownianExitFrontier

/-! # Frontier support under planar exit-law normalization -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set HarmonicBalls

namespace MatedCRT

/-- The normalized planar Brownian exit law is supported on the frontier of
    the normalized domain. -/
theorem planarBrownianExitProbability_normalize_ae_mem_frontier
    (U : Set ℂ) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (c z : ℂ) (hz : z ∈ U) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ w ∂(((planarBrownianExitProbability U hU z : ProbabilityMeasure ℂ) : Measure ℂ).map
      (fun w => r⁻¹ • (w - c))),
      w ∈ frontier ((fun w : ℂ => c + r • w) ⁻¹' U) := by
  let F : ℂ ≃ₜ ℂ := (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft c)
  have hF : ∀ w : ℂ, F w = c + r • w := fun _ => rfl
  have hFinv : ∀ w : ℂ, F.symm w = r⁻¹ • (w - c) := by
    intro w
    change r⁻¹ • (-c + w) = r⁻¹ • (w - c)
    rw [sub_eq_add_neg, add_comm]
  have hmap : Measurable (fun w : ℂ => r⁻¹ • (w - c)) := by fun_prop
  apply (ae_map_iff hmap.aemeasurable isClosed_frontier.measurableSet).2
  filter_upwards [planarBrownianExitProbability_ae_mem_frontier U hU hUb z hz] with w hw
  have hpre := F.preimage_frontier U
  have heq : (fun w : ℂ => c + r • w) ⁻¹' U = F ⁻¹' U := by
    ext x
    simp only [mem_preimage, hF]
  have hm : F.symm w ∈ frontier (F ⁻¹' U) := by
    rw [← hpre]
    change F (F.symm w) ∈ frontier U
    simpa only [F.apply_symm_apply] using hw
  change r⁻¹ • (w - c) ∈ frontier ((fun w : ℂ => c + r • w) ⁻¹' U)
  simpa only [hFinv, ← heq] using hm

end MatedCRT
end
