import MatedCRT.FirstPass.Derived.ConeReferenceData
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.RadialProcess
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedDefs

/-! # Reference cone radial correction -/

noncomputable section

open MeasureTheory HarmonicBalls MarkovProcess
open scoped NNReal
open MatedCRTHarmonic.GMCFacts

namespace MatedCRT.FirstPass.Derived

/-- The two radial branches and a simultaneous circle-average readout identify
    the reference cone correction at every point, including the origin. -/
theorem radial_difference_eq_reference_correction
    (γ : ℝ) (A : ℝ → ℝ) (W V F : C(ℝ≥0, ℝ)) (c : ℝ → ℂ → ℝ)
    (hW0 : W 0 = 0) (hF0 : F 0 = 0)
    (hinner : ∀ t : ℝ≥0, A t = W t + γ * t)
    (houter : ∀ t : ℝ≥0, A (-(t : ℝ)) = F t - γ * t)
    (hc : ∀ t : ℝ, c (Real.exp (-t)) 0 = twoSided W V t) :
    ∀ z : ℂ, A (-Real.log ‖z‖) - radialW (twoSided W V) z =
      γ * (-Real.log ‖z‖) + coneRefField c F z := by
  have hc1 : c 1 0 = 0 := by
    simpa [twoSided_apply] using hc 0
  intro z
  by_cases hz : ‖z‖ ≤ 1
  · have ht : 0 ≤ -Real.log ‖z‖ :=
      neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hz)
    have hi := hinner (Real.toNNReal (-Real.log ‖z‖))
    rw [Real.coe_toNNReal _ ht] at hi
    have hw : twoSided W V (-Real.log ‖z‖) = W (Real.toNNReal (-Real.log ‖z‖)) := by
      rw [twoSided_apply, Real.toNNReal_of_nonpos (neg_nonpos.mpr ht)]
      simp [hW0]
    rw [radialW, hw, hi]
    simp [coneRefField, coneRefProfile_of_le hz]
  · have hz1 : 1 < ‖z‖ := lt_of_not_ge hz
    have hp : 0 < ‖z‖ := lt_trans zero_lt_one hz1
    have hs : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (le_of_lt hz1)
    have ho := houter (Real.toNNReal (Real.log ‖z‖))
    rw [Real.coe_toNNReal _ hs] at ho
    have hcR : c ‖z‖ 0 = twoSided W V (-Real.log ‖z‖) := by
      simpa [Real.exp_log hp] using hc (-Real.log ‖z‖)
    rw [radialW, ho, ← hcR]
    simp only [coneRefField, coneRefProfile, max_eq_left (le_of_lt hz1), hF0, hc1,
      sub_zero]
    ring

end MatedCRT.FirstPass.Derived
