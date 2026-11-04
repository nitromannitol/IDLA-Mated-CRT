import MatedCRT.Defs.Notation

/-! The local uniform distance controls uniform distance on finite horizons. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

/-- Each term of the local uniform distance is bounded by the corresponding
geometric term and the series is summable even for discontinuous paths. -/
theorem summable_localUniformDist_terms (f g : ℝ≥0 → ℂ) :
    Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1) *
      (min 1 (⨆ t : Icc (0 : ℝ≥0) (k + 1 : ℕ), ENNReal.ofReal ‖f t - g t‖)).toReal) := by
  apply (summable_geometric_two.mul_left ((2 : ℝ)⁻¹)).of_nonneg_of_le
  · intro k
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  · intro k
    have h : (min 1 (⨆ t : Icc (0 : ℝ≥0) (k + 1 : ℕ),
        ENNReal.ofReal ‖f t - g t‖)).toReal ≤ 1 := by
      have := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤)
        (min_le_left 1 (⨆ t : Icc (0 : ℝ≥0) (k + 1 : ℕ), ENNReal.ofReal ‖f t - g t‖))
      simpa using this
    have := mul_le_mul_of_nonneg_left h (show 0 ≤ (2 : ℝ)⁻¹ ^ (k + 1) by positivity)
    convert this using 1
    simp only [one_div, pow_succ, mul_one]
    ring

/-- A weighted truncated pointwise distance is bounded by the local uniform distance. -/
theorem weighted_min_dist_le_localUniformDist (f g : ℝ≥0 → ℂ) (k : ℕ)
    {t : ℝ≥0} (ht : t ≤ (k + 1 : ℕ)) :
    (2 : ℝ)⁻¹ ^ (k + 1) * min 1 (dist (f t) (g t)) ≤ localUniformDist f g := by
  let a : ℕ → ℝ := fun j => (2 : ℝ)⁻¹ ^ (j + 1) *
    (min 1 (⨆ s : Icc (0 : ℝ≥0) (j + 1 : ℕ), ENNReal.ofReal ‖f s - g s‖)).toReal
  have ha : ∀ j, 0 ≤ a j := fun j => mul_nonneg (by positivity) ENNReal.toReal_nonneg
  have hsum : a k ≤ localUniformDist f g := by
    exact (summable_localUniformDist_terms f g).le_tsum k (fun j _ => ha j)
  have hsup : ENNReal.ofReal ‖f t - g t‖ ≤
      (⨆ s : Icc (0 : ℝ≥0) (k + 1 : ℕ), ENNReal.ofReal ‖f s - g s‖) :=
    le_iSup (fun s : Icc (0 : ℝ≥0) (k + 1 : ℕ) => ENNReal.ofReal ‖f s - g s‖)
      ⟨t, bot_le, ht⟩
  have hmin := min_le_min (le_refl (1 : ℝ≥0∞)) hsup
  have hreal := ENNReal.toReal_mono (by simp :
    min (1 : ℝ≥0∞) (⨆ s : Icc (0 : ℝ≥0) (k + 1 : ℕ),
      ENNReal.ofReal ‖f s - g s‖) ≠ ⊤) hmin
  have hreal' : min 1 (dist (f t) (g t)) ≤
      (min 1 (⨆ s : Icc (0 : ℝ≥0) (k + 1 : ℕ),
        ENNReal.ofReal ‖f s - g s‖)).toReal := by
    rw [ENNReal.toReal_min (by simp : (1 : ℝ≥0∞) ≠ ⊤) ENNReal.ofReal_ne_top,
      ENNReal.toReal_one, ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
    simpa only [dist_eq_norm] using hreal
  exact (mul_le_mul_of_nonneg_left hreal' (by positivity)).trans hsum

/-- Convergence in the local uniform distance gives uniform convergence on
every finite time interval, also for paths without continuity assumptions. -/
theorem locally_uniform_of_tendsto_localUniformDist {ι : Type*} {l : Filter ι}
    (g : ι → ℝ≥0 → ℂ) (f : ℝ≥0 → ℂ)
    (hconv : Tendsto (fun i => localUniformDist (g i) f) l (𝓝 0)) :
    ∀ v : ℝ≥0, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ i in l, ∀ t ≤ v, dist (g i t) (f t) < δ := by
  intro v δ hδ
  obtain ⟨k, hk⟩ := exists_nat_gt (v : ℝ)
  have hvk : v ≤ (k + 1 : ℕ) := by
    have h : (v : ℝ) ≤ (k + 1 : ℕ) := by exact le_trans hk.le (by exact_mod_cast Nat.le_succ k)
    exact_mod_cast h
  have hw : 0 < (2 : ℝ)⁻¹ ^ (k + 1) := by positivity
  have hε : 0 < (2 : ℝ)⁻¹ ^ (k + 1) * min 1 δ := by positivity
  filter_upwards [hconv.eventually (Iio_mem_nhds hε)] with i hi t ht
  have hbound := weighted_min_dist_le_localUniformDist (g i) f k (ht.trans hvk)
  by_contra hn
  have hle : δ ≤ dist (g i t) (f t) := le_of_not_gt hn
  have hmin : min 1 δ ≤ min 1 (dist (g i t) (f t)) := min_le_min le_rfl hle
  have hmul := mul_le_mul_of_nonneg_left hmin hw.le
  linarith

end MatedCRT
