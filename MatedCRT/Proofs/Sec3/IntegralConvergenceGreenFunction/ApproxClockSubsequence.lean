import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.CutoffMeasurable

/-!
# Lemma 3.4 (item 4): almost sure subsequences of approximate Liouville clocks

Borel–Cantelli extraction that passes from convergence in probability of the approximate clocks to almost sure convergence
along a subsequence, uniformly on compact time intervals for almost every path. The hypothesis is the form in which
`IsLQGClock` is stated: for every `T` and `η > 0`, the probability of the event that the approximate clock deviates from
the clock by at least `η` on `[0, T]` tends to zero. This is the subsequence step of `LBMPathFunctionalMeasurableStep`
(paper argument, `docs/campaign/GAPS-SEC3.md`, item 4).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MatedCRT

/-- **Borel–Cantelli extraction.** If for each `j` the masses `μ (A j k)` tend to zero as `k → ∞`, there is a strictly
increasing subsequence `φ` such that almost every point lies in only finitely many of the sets `A j (φ j)`. -/
theorem exists_strictMono_ae_eventually_notMem {β : Type*} [MeasurableSpace β] (μ : Measure β)
    (A : ℕ → ℕ → Set β) (hA : ∀ j, Tendsto (fun k => μ (A j k)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ b ∂μ, ∀ᶠ j in atTop, b ∉ A j (φ j) := by
  have hpos : ∀ j : ℕ, (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ (j + 1) := fun j =>
    ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _
  have hev : ∀ j : ℕ, ∀ᶠ k in atTop, μ (A j k) < (2⁻¹ : ℝ≥0∞) ^ (j + 1) := fun j => by
    filter_upwards [(hA j).eventually (Iio_mem_nhds (hpos j))] with k hk
    exact hk
  obtain ⟨φ, hφ, hφA⟩ := extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ?_⟩
  have hsum_eq : (∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 1)) = 1 := by
    simp only [pow_succ]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top
  have hle : (∑' j : ℕ, μ (A j (φ j))) ≤ ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 1) :=
    ENNReal.tsum_le_tsum fun j => (hφA j).le
  have hbad : (∑' j : ℕ, μ (A j (φ j))) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hsum_eq]; exact ENNReal.one_ne_top) hle
  filter_upwards [ae_eventually_notMem hbad] with b hb
  exact hb

/-- **Almost sure convergence of approximate clocks along a subsequence.** If the approximate clocks `C k b` converge to
the clock `G b` in probability uniformly on compact time intervals (the form of `IsLQGClock`), then along a subsequence
they converge uniformly on every compact time interval, for almost every path. -/
theorem exists_strictMono_ae_forall_eventually_close {β : Type*} [MeasurableSpace β] (μ : Measure β)
    (C : ℕ → β → ℝ≥0 → ℝ) (G : β → ℝ≥0 → ℝ)
    (hconv : ∀ (T : ℝ≥0) (η : ℝ), 0 < η →
      Tendsto (fun k => μ {b | ∃ t ≤ T, η ≤ |C k b t - G b t|}) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ b ∂μ, ∀ (T : ℝ≥0) (η : ℝ), 0 < η →
      ∀ᶠ j in atTop, ∀ t ≤ T, |C (φ j) b t - G b t| < η := by
  obtain ⟨φ, hφ, hae⟩ := exists_strictMono_ae_eventually_notMem μ
    (fun j k => {b | ∃ t ≤ (j : ℝ≥0), 1 / ((j : ℝ) + 1) ≤ |C k b t - G b t|})
    (fun j => hconv (j : ℝ≥0) (1 / ((j : ℝ) + 1)) (by positivity))
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with b hb T η hη
  filter_upwards [hb, tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hη),
    eventually_ge_atTop ⌈T⌉₊] with j hbj hsj hTj
  intro t ht
  have hTj' : T ≤ (j : ℝ≥0) := le_trans (Nat.le_ceil T) (Nat.cast_le.2 hTj)
  exact lt_trans (not_le.1 fun h => hbj ⟨t, ht.trans hTj', h⟩) hsj

end MatedCRT
