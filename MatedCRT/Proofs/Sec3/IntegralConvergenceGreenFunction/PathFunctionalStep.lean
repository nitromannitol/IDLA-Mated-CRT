import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxPathIntegral
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxPathJoint
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxPathLimit
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions

/-!
# Lemma 3.4: the step `LBMPathFunctionalMeasurableStep` holds

Both clauses of `LBMPathFunctionalMeasurableStep` (`Steps/Sec3/ConvergenceHarmonicFunctions.lean`) hold for every valid mated-CRT
environment (paper argument):

* the first clause (almost sure strong measurability in the Brownian path) is `lbmPathFunctional_aestronglyMeasurable`;
* the second clause: the expectations of the approximate path functionals `E k` are measurable in the environment (Fubini,
  `measurable_integral_boundedLipschitz_approxPath`), almost surely equal to the expectations of the approximate paths, and converge
  for almost every environment to the expectation of the Liouville Brownian path functional
  (`tendsto_integral_boundedLipschitz_approxPath`); the limit is almost everywhere measurable.

The step is proved here, in the Proofs directory of Lemma 3.4, from its statement in `Steps/`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal

/-- **Second clause of `LBMPathFunctionalMeasurableStep`.** For a valid mated-CRT environment and a bounded Lipschitz path functional
`F`, the expectation `ω ↦ ∫ F (Liouville Brownian path of ω) d(planar Brownian law)` is almost surely measurable. -/
theorem lbmPathFunctional_aemeasurable_integral {Ω : Type} [MeasurableSpace Ω] (𝒮 : SpaceFillingSLEModel) (γ : ℝ)
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (y : ℂ) (F : (ℝ≥0 → ℂ) → ℝ)
    (hF : IsBoundedLipschitzPathFunctional F) :
    AEMeasurable (fun ω => ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) S.P := by
  have hE : ∀ k : ℕ, ∃ E : Ω → ℝ, Measurable E ∧ ∀ᵐ ω ∂S.P, E ω = ∫ b, F (fun t : ℝ≥0 =>
      b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ (S.hcirc ω) (dyadicScale k) b s) (k : ℝ≥0)
        (S.m₀.toNNReal * t))) ∂planarBrownianMotion y :=
    fun k => measurable_integral_boundedLipschitz_approxPath hS.isQuantumCone hF k (k : ℝ≥0)
      S.m₀.toNNReal (planarBrownianMotion y)
  choose E hEmeas hEae using hE
  have hall : ∀ᵐ ω ∂S.P, ∀ k : ℕ, E k ω = ∫ b, F (fun t : ℝ≥0 =>
      b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ (S.hcirc ω) (dyadicScale k) b s) (k : ℝ≥0)
        (S.m₀.toNNReal * t))) ∂planarBrownianMotion y :=
    ae_all_iff.2 hEae
  have hlim : ∀ᵐ ω ∂S.P, Tendsto (fun k : ℕ => E k ω) atTop
      (𝓝 (∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y)) := by
    filter_upwards [hall, hS.isLQGClock, hS.isQuantumCone.ae_continuousOn_circle] with ω hω1 hω2 hω3
    have hH : ∀ k : ℕ, Continuous (S.hcirc ω (dyadicScale k)) := by
      intro k
      apply continuousOn_univ.mp
      apply hω3.comp (continuous_const.prodMk continuous_id).continuousOn
      intro z _
      exact ⟨dyadicScale_pos k, mem_univ z⟩
    have hT := tendsto_integral_boundedLipschitz_approxPath hF hH (planarBrownianMotion y)
      (G := S.clock ω) (hω2 y).1 (hω2 y).2 S.m₀.toNNReal
    exact (tendsto_congr hω1).2 hT
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun k => (hEmeas k).aemeasurable) hlim

/-- **`LBMPathFunctionalMeasurableStep` holds.** Both clauses hold for every valid environment, every starting point and every
bounded Lipschitz path functional. -/
theorem lbmPathFunctionalMeasurableStep_holds (𝒮 : SpaceFillingSLEModel) : LBMPathFunctionalMeasurableStep 𝒮 := by
  unfold LBMPathFunctionalMeasurableStep
  intro γ _ _ Ω _ S hS y F hF
  exact ⟨lbmPathFunctional_aestronglyMeasurable 𝒮 γ S hS y F hF,
    lbmPathFunctional_aemeasurable_integral 𝒮 γ S hS y F hF⟩

end MatedCRT
