import Mathlib

/-!
# FIRST PASS, Lemma 5.3: subsequence criterion for limits along `ε ↓ 0` (B2, pure topology)

The argument concludes the full limit `P[F ∩ (E ε)ᶜ] → 0` (as `ε ↓ 0`, the statement `TendsToOneOn`) from the
subsequence property: every sequence `x_n ↓ 0` has a subsequence along which the failure probabilities vanish. This is the
standard subsequence criterion, proved here for `ℝ≥0∞`-valued functions on `𝓝[>] 0`.
-/

namespace MatedCRT.S5c

open Filter Topology Set
open scoped ENNReal

/-- **Subsequence criterion** (B2): if every positive sequence tending to zero has a subsequence along which `f` tends to zero,
then `f → 0` along `𝓝[>] 0`. -/
theorem tendsto_nhdsWithin_zero_of_subseq {f : ℝ → ℝ≥0∞}
    (h : ∀ x : ℕ → ℝ, (∀ n, 0 < x n) → Tendsto x atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => f (x (φ k))) atTop (𝓝 0)) :
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ y in 𝓝[>] (0 : ℝ), ε < f y :=
    (Filter.not_eventually.1 hcon).mono fun y hy => not_le.1 hy
  have hsmall : ∀ n : ℕ, ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)) :=
    fun n => Ioo_mem_nhdsGT (by positivity)
  have hx : ∀ n : ℕ, ∃ y : ℝ, (0 < y ∧ y < 1 / ((n : ℝ) + 1)) ∧ ε < f y := by
    intro n
    obtain ⟨y, h1, h2⟩ := (hfreq.and_eventually (hsmall n)).exists
    exact ⟨y, h2, h1⟩
  choose x hxI hxf using hx
  have hxpos : ∀ n, 0 < x n := fun n => (hxI n).1
  have hxlim : Tendsto x atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => (hxpos n).le) (fun n => (hxI n).2.le)
  obtain ⟨φ, _, hlim⟩ := h x hxpos hxlim
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact absurd (hxf (φ k)) (not_lt.2 hk.le)

end MatedCRT.S5c
