import MatedCRT.FirstPass.Derived.ConeReferenceApproximantLocality
import LatticeProb.LQG.LQGMassFatou

/-! # Reference-cone approximants at arbitrary dyadic scales -/

noncomputable section

open MeasureTheory Filter Set Topology Metric MarkovProcess
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

open LatticeProb.LQG LatticeProb.Gauss

/-- A fixed-radius reference-cone approximant has vanishing mass on shrinking
balls about the origin. -/
theorem tendsto_coneRef_approximant_fixed_dyadic_ball
    (γ : ℝ) (c : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ) {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ)) :
    Tendsto (fun J => lqgApprox γ (coneRefCircle γ c w) r
      (ball (0 : ℂ) (dyadicScale J))) atTop (𝓝 0) := by
  let μ := lqgApprox γ (coneRefCircle γ c w) r
  have hslice : Continuous (coneRefCircle γ c w r) :=
    (continuousOn_coneRefCircle γ hc w).comp_continuous
      (continuous_const.prodMk continuous_id) (fun z => ⟨hr, mem_univ z⟩)
  have : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_lqgApprox_of_continuous γ hslice
  have hzero : μ {0} = 0 :=
    withDensity_absolutelyContinuous volume _ (measure_singleton (0 : ℂ))
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨U, hU, hUopen, hUε⟩ :=
    (isCompact_singleton : IsCompact ({0} : Set ℂ)).exists_isOpen_lt_of_lt
      (μ := μ) ε (by simpa [hzero] using hε)
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hUopen 0 (hU (by simp))
  have ht : Tendsto dyadicScale atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [ht.eventually (Iio_mem_nhds hδ)] with J hJ
  exact (measure_mono ((ball_subset_ball hJ.le).trans hδU)).trans hUε.le

/-- Singular-field vanishing transfers to the reference cone along every
sequence of dyadic regularization indices. -/
theorem tendsto_coneRef_approximant_all_dyadic_ball
    (γ : ℝ) (c : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ)
    (hc : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ))
    (hv : ∀ k : ℕ → ℕ, Tendsto (fun J => lqgApprox γ (fieldCircleAverage γ c)
      (dyadicScale (k J)) (ball 0 (dyadicScale J))) atTop (𝓝 0))
    (k : ℕ → ℕ) :
    Tendsto (fun J => lqgApprox γ (coneRefCircle γ c w)
      (dyadicScale (k J)) (ball 0 (dyadicScale J))) atTop (𝓝 0) := by
  let k' : ℕ → ℕ := fun J => max (k J) 1
  have hk' : ∀ᶠ J in atTop, dyadicScale (k' J) ≤ (1 / 2 : ℝ) := by
    filter_upwards with J
    simpa [dyadicScale] using
      (pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        (show (1 / 2 : ℝ) ≤ 1 by norm_num) (le_max_right (k J) 1))
  have hs := tendsto_coneRef_approximant_dyadic_ball γ c w k' hk' (hv k')
  have h0 := tendsto_coneRef_approximant_fixed_dyadic_ball γ c w (by norm_num : (0 : ℝ) < 1) hc
  rw [ENNReal.tendsto_nhds_zero] at hs h0 ⊢
  intro ε hε
  filter_upwards [hs ε hε, h0 ε hε] with J hsJ h0J
  by_cases hk : k J = 0
  · simpa [hk, dyadicScale] using h0J
  · have heq : k' J = k J := max_eq_left (Nat.one_le_iff_ne_zero.mpr hk)
    simpa [heq] using hsJ

end MatedCRT.FirstPass.Derived
