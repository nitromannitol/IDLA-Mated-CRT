import MatedCRT.FirstPass.Derived.BrownianExitLawIdentification
import LatticeProb.Bonanno.BouRabeeGwynne.HarmonicNearClosureBrownianExit

/-! # Frontier support of planar Brownian exit laws -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set HarmonicBalls BouRabeeGwynne

namespace MatedCRT

/-- Brownian motion started inside a bounded open planar domain exits on its
frontier almost surely. -/
theorem planarBrownianExitProbability_ae_mem_frontier (U : Set ℂ)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (z : ℂ) (hz : z ∈ U) :
    ∀ᵐ w ∂((planarBrownianExitProbability U hU z : ProbabilityMeasure ℂ) : Measure ℂ),
      w ∈ frontier U := by
  let E := Complex.orthonormalBasisOneI.repr
  let ρ := (planarBrownianMotion 0).map TargetLawTemplateEvent.complexPathToEuc
  have hρ : IsStandardBrownianLaw ρ :=
    TargetLawTemplateEvent.isStandardBrownianLaw_map_complexPathToEuc
  have hV : IsOpen (E '' U) := E.toHomeomorph.isOpenMap U hU
  have hVb : Bornology.IsBounded (E '' U) := E.isometry.lipschitzWith.isBounded_image hUb
  have hfront := standardBrownianLaw_stopped_endPoint_ae_mem_frontier
    (by norm_num : 1 ≤ 2) hρ hV hVb (show E z ∈ E '' U from ⟨z, hz, rfl⟩)
  rw [BrownianExitLawIdentification.stoppedBrownianLaw_endPoint_eq U hU z ρ hρ] at hfront
  have hpre : E ⁻¹' frontier (E '' U) = frontier U := by
    change E.toHomeomorph ⁻¹' frontier (E.toHomeomorph '' U) = frontier U
    rw [E.toHomeomorph.preimage_frontier, E.toHomeomorph.injective.preimage_image]
  have h := (ae_map_iff E.continuous.measurable.aemeasurable
    isClosed_frontier.measurableSet).mp hfront
  filter_upwards [h] with w hw
  change w ∈ E ⁻¹' frontier (E '' U) at hw
  rwa [hpre] at hw

end MatedCRT
end
