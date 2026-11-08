import MatedCRT.Proposed.Berestycki2015
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.KilledClockBridge

/-! # Stopped-clock convergence required for the occupation argument -/

namespace MatedCRT

open HarmonicBalls MarkovProcess MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- The all-time continuous dyadic killed-clock limit used in the localization
of the LBM time change in Lemma 3.4 of the corrected paper, lines 1168–1172.
This is a proof step, not an assertion of the staged diffusion theorem; no
written proof of this exact assertion has been supplied. -/
def DirichletStoppedClockConvergenceStep {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (x : ℂ) (G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ) : Prop :=
  ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
    let K : ℕ → ℝ≥0 → ℝ := fun n =>
      killedGMCClockApprox U γ (hcirc q.1) (dyadicScale n) q.2
    (∀ t : ℝ≥0, Tendsto (fun n => K n t) atTop (𝓝 (G q.1 q.2 t))) ∧
    Continuous (G q.1 q.2)

end MatedCRT
