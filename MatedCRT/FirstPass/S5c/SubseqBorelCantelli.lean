import Mathlib

/-!
# FIRST PASS, Lemma 5.3 and E-c1-5: deterministic subsequence and Borel-Cantelli (B2)

No measurable selection of the threshold `τ` is needed. From convergence to zero of the level-`k` failure
probabilities along `ε → 0`, a deterministic sequence `ε_k → 0` with summable failure bounds `P(Bad_k(ε_k)) ≤ 2^{-k}` is chosen;
Borel-Cantelli then gives, almost surely, `ω ∉ Bad_k(ε_k)` for all large `k`. Pure probability: the failure events need no
measurability, since `P` is an outer measure.
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- **Deterministic subsequence** (B2, CHATGPT-5-1-B2-Ec15.md §1): if each level-`k` failure function `a k` tends to zero along
`ε → 0`, there is a deterministic sequence `ε_k ∈ (0, 1/(k+1))` with `a_k(ε_k) ≤ 2^{-k}`. -/
theorem exists_subseq_of_tendsto_zero {a : ℕ → ℝ → ℝ≥0∞} (ha : ∀ k, Tendsto (a k) (𝓝[>] 0) (𝓝 0)) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧ ∀ k, a k (ε k) ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
  have hex : ∀ k : ℕ, ∃ x : ℝ, (0 < x ∧ x < 1 / ((k : ℝ) + 1)) ∧ a k x ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have hc : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ k := ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) k
    have h1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), a k x < (2⁻¹ : ℝ≥0∞) ^ k :=
      (ha k).eventually (gt_mem_nhds hc)
    have h2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)) :=
      Ioo_mem_nhdsGT (by positivity)
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    exact ⟨x, hx2, hx1.le⟩
  choose ε hε1 hε2 using hex
  refine ⟨ε, fun k => (hε1 k).1, ?_, hε2⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun k => (hε1 k).1.le) (fun k => (hε1 k).2.le)

/-- **Borel-Cantelli, geometric form** (B2): if `P(Bad_k) ≤ 2^{-k}` for every `k`, then almost surely `ω ∉ Bad_k` for all
large `k`. No measurability of the sets is used. -/
theorem ae_eventually_not_mem_of_geometric {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Bad : ℕ → Set Ω)
    (hB : ∀ k, P (Bad k) ≤ (2⁻¹ : ℝ≥0∞) ^ k) : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ Bad k := by
  apply ae_eventually_notMem
  have hfin : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k ≠ ⊤ := by
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    simp
  exact ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum hB)

/-- **Subsequence Borel-Cantelli** (B2, the form used in CHATGPT-5-1-B2-Ec15.md §1): if for each level `k` the failure
probabilities `P(Bad ε k)` tend to zero as `ε ↓ 0` (convergence in probability), there is a deterministic `ε_k → 0` such
that almost surely `ω ∉ Bad (ε_k) k` for all large `k`. The threshold is never selected as a function of `ω`. -/
theorem exists_subseq_ae_eventually_good {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Bad : ℝ → ℕ → Set Ω)
    (hbad : ∀ k, Tendsto (fun ε => P (Bad ε k)) (𝓝[>] 0) (𝓝 0)) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ Bad (ε k) k := by
  obtain ⟨ε, hpos, hlim, hsmall⟩ := exists_subseq_of_tendsto_zero hbad
  exact ⟨ε, hpos, hlim, ae_eventually_not_mem_of_geometric (fun k => Bad (ε k) k) hsmall⟩

end MatedCRT.S5c
