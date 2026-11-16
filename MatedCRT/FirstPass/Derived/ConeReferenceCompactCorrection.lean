import MatedCRT.FirstPass.Derived.ConeReferenceData

/-! # Compact bounds for reference-cone approximants -/

noncomputable section

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

open LatticeProb.LQG LatticeProb.Gauss

/-- On a compact set of centers, all circle averages of the continuous radial
correction are uniformly bounded over radii in `[0, 1]`. -/
theorem exists_coneRefCircle_correction_bound
    (c : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ)
    (hc : ContinuousOn (fun ρ => c ρ 0) (Ioi 0)) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
      ∀ z : ℂ, z ∈ closedBall 0 R →
        |Real.circleAverage (coneRefField c w) z r| ≤ B := by
  have hcont := LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center
    (continuous_coneRefField hc w)
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun r hr z hz => ?_⟩
  have hb : |Real.circleAverage (coneRefField c w) z r| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB (r, z) ⟨hr, hz⟩
  exact hb.trans (le_max_left _ _)

/-- On compact sets, reference-cone approximant masses are bounded by a
fixed multiple of the corresponding singular-field approximant masses, at
every regularization radius at most one. -/
theorem coneRef_approximant_le_singular_on_compact
    (γ : ℝ) (c : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ)
    (hc : ContinuousOn (fun ρ => c ρ 0) (Ioi 0)) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ S : Set ℂ,
      MeasurableSet S → S ⊆ closedBall 0 R →
      lqgApprox γ (coneRefCircle γ c w) r S ≤
        ENNReal.ofReal C * lqgApprox γ (fieldCircleAverage γ c) r S := by
  obtain ⟨B, hB, hb⟩ := exists_coneRefCircle_correction_bound c w hc R
  refine ⟨Real.exp (|γ| * B), Real.exp_pos _, fun r hr hr1 S hS hSR => ?_⟩
  rw [lqgApprox, withDensity_apply _ hS, lqgApprox, withDensity_apply _ hS,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hS] with z hz
  have hcorr : γ * Real.circleAverage (coneRefField c w) z r ≤ |γ| * B :=
    (le_abs_self _).trans ((abs_mul γ _).le.trans (mul_le_mul_of_nonneg_left
      (hb r ⟨hr.le, hr1⟩ z (hSR hz)) (abs_nonneg γ)))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [coneRefCircle, mul_add, Real.exp_add]
  have he := Real.exp_le_exp.mpr hcorr
  have hp : 0 ≤ r ^ (γ ^ 2 / 2) := Real.rpow_nonneg hr.le _
  calc
    _ ≤ r ^ (γ ^ 2 / 2) * (Real.exp (γ * fieldCircleAverage γ c r z) *
        Real.exp (|γ| * B)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le) hp
    _ = _ := by ring

end MatedCRT.FirstPass.Derived
