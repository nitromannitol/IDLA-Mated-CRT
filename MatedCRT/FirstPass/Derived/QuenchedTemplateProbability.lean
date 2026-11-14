import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import MatedCRT.FirstPass.Derived.TemplateEventCompactOpen
import MatedCRT.FirstPass.Derived.BrownianTemplateScales

/-! # Template probabilities for varying quenched walk laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Filter Set Topology MarkovProcess _root_.HarmonicBalls
open MatedCRT.TemplateEventCompactOpen
open scoped ENNReal NNReal

/-- Weak convergence of the mesh-dependent quenched path laws to a law with the
Brownian template probabilities yields the template lower bound, with radius
chosen before mesh. The environment is fixed, while the starting vertex and
time scale may vary with the mesh. -/
theorem eventually_templateProbability_of_tendsto_walkPathLaw
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (a : ℝ → ℤ) (m : ℝ → ℝ) (hm : ∀ ε, 0 ≤ m ε)
    (ν : ProbabilityMeasure (ContinuousPath ℂ))
    (hν : ∀ r : ℝ, (ν : Measure (ContinuousPath ℂ)) (templateDisconnectionEvent r) =
      planarBrownianMotion 0 (templateDisconnectionEvent r))
    (hlim : Tendsto (fun ε : ℝ => walkPathLaw S
      (fun _ => vertexPoint ε (S.η ω)) (hm ε) ε (a ε) ω)
      (𝓝[>] (0 : ℝ)) (𝓝 ν))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      1 - δ ≤ (srwLaw (S.mult ε ω) (a ε)
        {ξ | interpPathCM (vertexPoint ε (S.η ω)) (hm ε) ξ ∈
          templateDisconnectionEvent r}).toReal := by
  have hthreshold : ENNReal.ofReal (1 - δ) < 1 :=
    ENNReal.ofReal_lt_one.mpr (by linarith)
  filter_upwards [(tendsto_order.1 tendsto_planarBrownianMotion_templateDisconnectionEvent).1
    _ hthreshold] with r hr
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
    (isOpen_templateDisconnectionEvent r)
  have hlt : ENNReal.ofReal (1 - δ) <
      (𝓝[>] (0 : ℝ)).liminf (fun ε : ℝ =>
        (walkPathLaw S (fun _ => vertexPoint ε (S.η ω)) (hm ε) ε (a ε) ω :
          Measure (ContinuousPath ℂ)) (templateDisconnectionEvent r)) := by
    have hνr : ENNReal.ofReal (1 - δ) <
        (ν : Measure (ContinuousPath ℂ)) (templateDisconnectionEvent r) := by
      rw [hν]
      exact hr
    exact hνr.trans_le hport
  filter_upwards [eventually_lt_of_lt_liminf hlt] with ε hε
  have heq :
      (walkPathLaw S (fun _ => vertexPoint ε (S.η ω)) (hm ε) ε (a ε) ω :
        Measure (ContinuousPath ℂ)) (templateDisconnectionEvent r) =
      srwLaw (S.mult ε ω) (a ε)
        {ξ | interpPathCM (vertexPoint ε (S.η ω)) (hm ε) ξ ∈
          templateDisconnectionEvent r} := by
    exact Measure.map_apply (measurable_interpPathCM _ (hm ε))
      (isOpen_templateDisconnectionEvent r).measurableSet
  rw [heq] at hε
  exact ((ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hε.le)

end MatedCRT
