/-
Scale invariance of the quantum cone, given the radial invariance.

The circle-average process of the rescaled cone `h(R_b ·) + Q log R_b - γ⁻¹ log b` and the one of `h`
are a.s. continuous processes indexed by `(0,∞) × ℂ`; the vector of their values at finitely many
circles avoiding the origin has the same law (`map_circleVec_rescaled_eq`, which takes the radial
invariance as an explicit hypothesis).  Since the circles avoiding the origin are dense, the laws
coincide (`LatticeProb.map_eq_of_ae_continuous_of_dense_coordinates`).
-/
import MatedCRT.FirstPass.Derived.ConeScalingProcessAux
import LatticeProb.Prob.LawAEContinuousDense

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal Classical

namespace MatedCRT.FirstPass.Derived

/-- **Scale invariance of the quantum cone, given the radial invariance** (hrad: explicit hypothesis, the Williams gluing
identity for the radial pair; not a Prop). -/
theorem quantumConeScaling_of_radialInvariance {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ)
    (hrad : P.map (fun ω => radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) =
      P.map (fun ω => radialProcess (hcirc ω))) :
    P.map (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) =
      P.map (fun ω => circleProcess (hcirc ω)) := by
  have hYc : ∀ i : Set.Ioi (0 : ℝ) × ℂ, Measurable fun ω => circleProcess (hcirc ω) i :=
    fun i => h.measurable_circle i.1.1 i.2 i.1.2
  have hYm : Measurable fun ω => circleProcess (hcirc ω) := measurable_pi_iff.2 hYc
  have hXc : ∀ᵐ ω ∂P, Continuous
      (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
    filter_upwards [h.ae_continuousOn_circle, ae_coneScaleRadius_spec hγ0 hγ2 h b] with ω hc hspec
    exact continuous_circleProcess_of_continuousOn (continuousOn_rescaledCircle hspec.1 hc)
  have hYcont : ∀ᵐ ω ∂P, Continuous (circleProcess (hcirc ω)) := by
    filter_upwards [h.ae_continuousOn_circle] with ω hc
    exact continuous_circleProcess_of_continuousOn hc
  have hXcoord := LatticeProb.aemeasurable_apply_of_ae_continuous_of_dense hXc dense_nonsingularSet
    (fun d hd => aemeasurable_rescaled_coord hγ0 hγ2 h b ⟨d, hd⟩)
  have hXm := LatticeProb.aemeasurable_of_ae_continuous hXc hXcoord
  refine LatticeProb.map_eq_of_ae_continuous_of_dense_coordinates hXm hYm.aemeasurable hXc hYcont
    dense_nonsingularSet ?_
  intro k a ha
  exact map_circleVec_rescaled_eq hγ0 hγ2 h b (fun j => ⟨a j, ha j⟩) hrad

end MatedCRT.FirstPass.Derived
