import MatedCRT.FirstPass.S5c.SubseqBorelCantelli

/-!
# FIRST PASS, Lemma 5.3: subsequence along an arbitrary mesh sequence (B2 criterion, pure probability)

The argument uses the criterion: from any deterministic mesh sequence tending to zero, one can select a
subsequence along which the failure probabilities are summable (convergence in probability permits this). Here: given
failure families `Bad ε k` with `P(Bad ε k) → 0` as `ε ↓ 0` for each level `k`, and any positive sequence `x_n → 0`, there is
a strictly increasing `φ` with `P(Bad (x (φ k)) k) ≤ 2^{-k}`, hence almost surely `ω ∉ Bad (x (φ k)) k` for all large `k`.
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- **Subsequence along an arbitrary sequence** (B2 criterion): see the module docstring. -/
theorem exists_subseq_ae_eventually_good_of_seq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Bad : ℝ → ℕ → Set Ω) (hbad : ∀ k : ℕ, Tendsto (fun ε => P (Bad ε k)) (𝓝[>] 0) (𝓝 0))
    (x : ℕ → ℝ) (hpos : ∀ n, 0 < x n) (hx : Tendsto x atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ Bad (x (φ k)) k := by
  have hxw : Tendsto x atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hpos⟩
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop, P (Bad (x n) k) ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have h1 : Tendsto (fun n => P (Bad (x n) k)) atTop (𝓝 0) := (hbad k).comp hxw
    have hc : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ k := ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) k
    exact (h1.eventually (gt_mem_nhds hc)).mono fun n hn => hn.le
  obtain ⟨φ, hφ, hφk⟩ := Filter.extraction_forall_of_eventually hev
  exact ⟨φ, hφ, ae_eventually_not_mem_of_geometric (fun k => Bad (x (φ k)) k) (fun k => hφk k)⟩

end MatedCRT.S5c
