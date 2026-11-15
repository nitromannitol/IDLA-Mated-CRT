import MatedCRT.FirstPass.Derived.PlanarBrownianExteriorExit

/-! # Transport of planar Brownian exit laws at exterior points -/

set_option autoImplicit false
noncomputable section

open MeasureTheory HarmonicBalls

namespace MatedCRT

/-- At an exterior start, a homeomorphism transports the exit law to the
exit law from the image domain, even when the domain is unbounded. -/
theorem planarBrownianExitProbability_map_homeomorph_of_not_mem
    {U : Set ℂ} (hU : IsOpen U) (z : ℂ) (hz : z ∉ U) (e : ℂ ≃ₜ ℂ) :
    let V := e.symm ⁻¹' U
    let hV : IsOpen V := hU.preimage e.symm.continuous
    ((planarBrownianExitProbability U hU z : ProbabilityMeasure ℂ) : Measure ℂ).map e =
      ((planarBrownianExitProbability V hV (e z) : ProbabilityMeasure ℂ) : Measure ℂ) := by
  dsimp only
  have hz' : e z ∉ e.symm ⁻¹' U := by
    simpa only [Set.mem_preimage, e.symm_apply_apply] using hz
  rw [planarBrownianExitProbability_eq_dirac_of_not_mem hU z hz,
    planarBrownianExitProbability_eq_dirac_of_not_mem _ (e z) hz',
    Measure.map_dirac' e.continuous.measurable]

end MatedCRT
end
