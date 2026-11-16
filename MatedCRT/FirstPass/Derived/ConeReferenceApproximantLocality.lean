import MatedCRT.FirstPass.Derived.ConeReferenceLocalCircle
import MatedCRT.FirstPass.Derived.NormalizedFieldGivenVanishing

/-! # Locality of reference-cone approximations -/

noncomputable section

open MeasureTheory Filter Set Topology Metric MarkovProcess
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

open LatticeProb.LQG LatticeProb.Gauss

/-- Reference-cone and singular-field approximants have the same mass on a
ball whenever all their averaging circles lie in the closed unit disk. -/
theorem coneRef_approximant_ball_eq_singular
    (γ : ℝ) (c : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ)
    {r R : ℝ} (hr : 0 < r) (hR : R + r ≤ 1) :
    lqgApprox γ (coneRefCircle γ c w) r (ball (0 : ℂ) R) =
      lqgApprox γ (fieldCircleAverage γ c) r (ball 0 R) := by
  rw [lqgApprox, withDensity_apply _ measurableSet_ball,
    lqgApprox, withDensity_apply _ measurableSet_ball]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hzR : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hz
  rw [coneRefCircle_eq_fieldCircleAverage_of_add_le γ c w hr (by linarith)]
  rfl

/-- Vanishing singular-field approximant masses transfer to the reference
cone along regularization scales that are eventually at most one half. -/
theorem tendsto_coneRef_approximant_dyadic_ball
    (γ : ℝ) (c : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ) (k : ℕ → ℕ)
    (hk : ∀ᶠ J in atTop, dyadicScale (k J) ≤ (1 / 2 : ℝ))
    (hv : Tendsto (fun J => lqgApprox γ (fieldCircleAverage γ c)
      (dyadicScale (k J)) (ball 0 (dyadicScale J))) atTop (𝓝 0)) :
    Tendsto (fun J => lqgApprox γ (coneRefCircle γ c w)
      (dyadicScale (k J)) (ball 0 (dyadicScale J))) atTop (𝓝 0) := by
  have hs : ∀ᶠ J : ℕ in atTop, dyadicScale J ≤ (1 / 2 : ℝ) := by
    have ht : Tendsto dyadicScale atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ h => h.le
  apply hv.congr'
  filter_upwards [hk, hs] with J hkJ hsJ
  exact (coneRef_approximant_ball_eq_singular γ c w
    (by unfold dyadicScale; positivity) (by linarith)).symm

end MatedCRT.FirstPass.Derived
