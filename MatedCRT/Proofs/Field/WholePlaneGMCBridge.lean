import HarmonicBalls.Defs.LQG
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.GMCInterfaces

/-!
# The dyadic LQG limit in the whole-plane GMC interface

Leonardo Bonanno's `MatedCRTHarmonic.GMSLemma27` interface defines the same
circle-average approximation and vague limit as Harmonic Balls. This bridge
lets the GMC estimates in Bonanno's formalization be used after the separate
bridge between the two whole-plane GFF circle-average interfaces is supplied.
-/

namespace MatedCRT.Field

open MeasureTheory HarmonicBalls

theorem dyadicRadius_eq_dyadicScale (k : ℕ) :
    MatedCRTHarmonic.GMSLemma27.dyadicRadius k = dyadicScale k := by
  simp [MatedCRTHarmonic.GMSLemma27.dyadicRadius, dyadicScale, zpow_neg, zpow_natCast, inv_pow]

theorem lqgApprox_eq_bonanno {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (k : ℕ) (ω : Ω) :
    MatedCRTHarmonic.GMSLemma27.lqgApprox γ (fun r z ω => hcirc ω r z) k ω =
      HarmonicBalls.lqgApprox γ (hcirc ω) (dyadicScale k) := by
  simp [MatedCRTHarmonic.GMSLemma27.lqgApprox, HarmonicBalls.lqgApprox,
    dyadicRadius_eq_dyadicScale]

/-- The two circle-average definitions of the LQG measure are equivalent. -/
theorem isLQGMeasure_iff_isLQGAreaOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) :
    IsLQGMeasure P γ hcirc μ ↔
      MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ (fun r z ω => hcirc ω r z) μ P := by
  unfold IsLQGMeasure MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf
  constructor <;> intro h
  · filter_upwards [h] with ω hω
    exact ⟨hω.isLocallyFiniteMeasure, by
      simpa only [lqgApprox_eq_bonanno] using hω.tendsto_integral⟩
  · filter_upwards [h] with ω hω
    exact ⟨hω.1, by simpa only [lqgApprox_eq_bonanno] using hω.2⟩

end MatedCRT.Field
