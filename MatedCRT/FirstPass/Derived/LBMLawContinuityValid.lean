import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.Derived.LBMLawContinuity

/-!
# Continuity of the Liouville Brownian law for a valid environment

For a valid mated-CRT environment `S`, the circle averages `h_ε` of the quantum cone field are almost
surely continuous at every dyadic radius `ε = 2^{-k}` (they are a.s. jointly continuous in `(r, z)`,
`r > 0`). Together with the LQG clock property of `S.clock` this reduces the continuity in the
starting point of the law of the Liouville Brownian path `b ↦ (t ↦ b(F⁻¹ t))` under planar Brownian
motion to the stopped heat bound for the dyadic approximants
`ε^{γ²/2} e^{γ h_ε}` along Brownian motion stopped on leaving `B(0, R + 1)`
(`continuous_planarBrownianPathLaw_lbmContinuousPath`).
-/

open MeasureTheory ProbabilityTheory Set MarkovProcess Filter Topology
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- **Dyadic circle averages are continuous.** For a valid environment, almost surely the circle
average `z ↦ h_ε(z)` is continuous at every dyadic radius `ε = 2^{-k}`. -/
theorem ae_continuous_hcirc_dyadicScale {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ k : ℕ, Continuous (S.hcirc ω (dyadicScale k)) := by
  filter_upwards [hS.isQuantumCone.ae_continuousOn_circle] with ω hω k
  apply continuousOn_univ.mp
  apply hω.comp (continuous_const.prodMk continuous_id).continuousOn
  intro z _
  exact ⟨dyadicScale_pos k, mem_univ z⟩

/-- **Continuity of the Liouville Brownian law from the stopped heat bound.** For a valid
environment whose circle averages almost surely satisfy the stopped heat bound on every disc
`B(0, R + 1)`, almost surely the law of the Liouville Brownian path under planar Brownian motion
from `z` is a continuous function of `z`, for every choice of the measurability proofs. -/
theorem ae_continuous_planarBrownianPathLaw_of_stoppedHeatBound {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hheat : ∀ᵐ ω ∂S.P, ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
        ∫⁻ b, (∫⁻ s in Ioc 0 (min t
            (ContinuousPath.exitTime (Metric.ball (0 : ℂ) (R + 1)) b).toReal),
            ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
              Real.exp (γ * S.hcirc ω (LatticeProb.LQG.dyadicScale k) (b s.toNNReal))))
          ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C * t ^ β)) :
    ∀ᵐ ω ∂S.P,
      ∃ hg : ∀ z : ℂ, AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z),
        Continuous fun z => planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) (hg z) := by
  filter_upwards [hS.isLQGClock, ae_continuous_hcirc_dyadicScale hS, hheat] with ω hω hc hh
  exact ⟨fun z => aemeasurable_lbmContinuousPath (hω z).1 (hω z).2 hc,
    continuous_planarBrownianPathLaw_lbmContinuousPath (fun z => (hω z).1) (fun z => (hω z).2)
      hc hh _⟩

/-- **The continuity hypothesis of the Liouville Brownian law field, from the stopped heat bound.**
If every valid environment almost surely satisfies the stopped heat bound, then for every
`γ ∈ (0, 2)` and every valid environment, almost surely the law of the Liouville Brownian path
under planar Brownian motion from `z` is continuous in `z`. -/
theorem lbmLawContinuity_of_stoppedHeatBound {𝒮 : SpaceFillingSLEModel}
    (hheat : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ᵐ ω ∂S.P, ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
        ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
          ∫⁻ b, (∫⁻ s in Ioc 0 (min t
              (ContinuousPath.exitTime (Metric.ball (0 : ℂ) (R + 1)) b).toReal),
              ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
                Real.exp (γ * S.hcirc ω (LatticeProb.LQG.dyadicScale k) (b s.toNNReal))))
            ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C * t ^ β)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ᵐ ω ∂S.P,
        ∃ hg : ∀ z : ℂ, AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z),
          Continuous fun z => planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) (hg z) :=
  fun γ hγ hγ2 Ω _ S hS =>
    ae_continuous_planarBrownianPathLaw_of_stoppedHeatBound hS (hheat γ hγ hγ2 Ω S hS)

end MatedCRT.FirstPass.Derived
