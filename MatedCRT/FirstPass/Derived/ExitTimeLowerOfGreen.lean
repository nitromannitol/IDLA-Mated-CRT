import MatedCRT.FirstPass.Derived.ExpectedExitGreenSum
import MatedCRT.Defs.Setting

/-!
# Deterministic steps of the lower bound for expected exit times

Two deterministic ingredients of the lower bound `E^ε_x[τ_{B_r(η(x))}] ≥ ε⁻¹ μ_h(B_{cr}(η(x)))` for the
expected exit time of the walk on the mated-CRT map from a Euclidean ball (Berestycki-Gwynne
arXiv:2003.10320, Proposition 4.1, proof refs (4.19)-(4.20)):

* `measure_le_mul_encard_cellVertices`: for an area-parametrized space-filling curve, every cell
  `H^ε_k = η([ε(k-1), εk])` has `μ`-mass `ε` and the cells cover the plane, so `μ(D) ≤ ε #V^ε(D)`.
* `encard_le_expectedExitTime_of_one_le_greenKernel`: if the Green's kernel `g_A(a, ·)` is at least `1`
  on a set `W ⊆ A` of vertices, then `#W ≤ E^a[τ_A]` (from `E^a[τ_A] = ∑_{b ∈ A} G_A(a, b)` and
  `G_A(a, b) = deg(b) g_A(a, b) ≥ g_A(a, b)`).
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace MatedCRT

/-- The cells `H^ε_k = η([ε(k-1), εk])` of an area-parametrized curve have `μ`-mass `ε`. -/
theorem measure_cell_of_isAreaParametrized {μ : Measure ℂ} {η : ℝ → ℂ} (hη : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (k : ℤ) : μ (cell ε η k) = ENNReal.ofReal ε := by
  unfold cell
  rw [hη.2.2.2 _ _ (by nlinarith)]
  congr 1
  ring

/-- For a surjective curve the cells cover the plane: `D ⊆ ⋃_{k ∈ V^ε(D)} H^ε_k`. -/
theorem subset_iUnion_cell_cellVertices {η : ℝ → ℂ} (hsurj : Function.Surjective η) {ε : ℝ}
    (hε : 0 < ε) (D : Set ℂ) : D ⊆ ⋃ k : cellVertices ε η D, cell ε η k := by
  intro z hz
  obtain ⟨t, rfl⟩ := hsurj z
  set k : ℤ := ⌈t / ε⌉ with hk
  have h1 : t / ε ≤ k := Int.le_ceil _
  have h2 : (k : ℝ) - 1 < t / ε := by
    have := Int.ceil_lt_add_one (t / ε)
    linarith
  have hmem : η t ∈ cell ε η k := by
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · have := (lt_div_iff₀ hε).1 h2
      linarith
    · have := (div_le_iff₀ hε).1 h1
      linarith
  exact mem_iUnion.2 ⟨⟨k, ⟨η t, hmem, hz⟩⟩, hmem⟩

/-- **Mass of a domain and its cell count.** For an area-parametrized curve `η` and `ε > 0`,
`μ(D) ≤ ε #V^ε(D)` (Berestycki-Gwynne arXiv:2003.10320, proof of Proposition 4.1: each cell has
`μ_h`-mass `ε`). -/
theorem measure_le_mul_encard_cellVertices {μ : Measure ℂ} {η : ℝ → ℂ} (hη : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (D : Set ℂ) :
    μ D ≤ ENNReal.ofReal ε * ((cellVertices ε η D).encard : ℝ≥0∞) := by
  calc μ D ≤ μ (⋃ k : cellVertices ε η D, cell ε η k) :=
        measure_mono (subset_iUnion_cell_cellVertices hη.2.2.1 hε D)
    _ ≤ ∑' k : cellVertices ε η D, μ (cell ε η k) := measure_iUnion_le _
    _ = ∑' _ : cellVertices ε η D, ENNReal.ofReal ε := by
        refine tsum_congr fun k => ?_
        exact measure_cell_of_isAreaParametrized hη hε k
    _ = ENNReal.ofReal ε * ((cellVertices ε η D).encard : ℝ≥0∞) := by
        rw [ENNReal.tsum_set_const, mul_comm]

/-- **Expected exit time from a Green's kernel lower bound.** If `g_A(a, b) ≥ 1` for every `b` in a set
`W ⊆ A`, then `#W ≤ E^a[τ_A]` (Berestycki-Gwynne arXiv:2003.10320, (4.20)). -/
theorem encard_le_expectedExitTime_of_one_le_greenKernel (m : ℤ → ℤ → ℕ) {A W : Set ℤ} (a : ℤ)
    (hWA : W ⊆ A) (hW : ∀ b ∈ W, 1 ≤ greenKernel m A a b) :
    (W.encard : ℝ≥0∞) ≤ expectedExitTime m A a := by
  by_cases hfin : expectedExitTime m A a = ⊤
  · rw [hfin]; exact le_top
  have hG : ∀ b ∈ W, 1 ≤ greenFn m A a b := by
    intro b hb
    have hg := hW b hb
    have hd : (mdeg m b : ℝ) ≠ 0 := by
      intro h0
      unfold greenKernel at hg
      rw [h0, div_zero] at hg
      norm_num at hg
    have hd1 : (1 : ℝ) ≤ mdeg m b := by
      have : 0 < mdeg m b := Nat.pos_of_ne_zero (by exact_mod_cast hd)
      exact_mod_cast this
    have hgn : 0 ≤ greenFn m A a b := ENNReal.toReal_nonneg
    unfold greenKernel at hg
    calc (1 : ℝ) ≤ greenFn m A a b / (mdeg m b : ℝ) := hg
      _ ≤ greenFn m A a b := div_le_self hgn hd1
  rw [ExitTimeMoment.expectedExitTime_eq_tsum_greenFn m A a hfin, ← ENNReal.tsum_set_one]
  calc ∑' _ : W, (1 : ℝ≥0∞) ≤ ∑' b : W, ENNReal.ofReal (greenFn m A a b) := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hG b b.2)
    _ ≤ ∑' b : A, ENNReal.ofReal (greenFn m A a b) :=
        ENNReal.tsum_mono_subtype (fun b => ENNReal.ofReal (greenFn m A a b)) hWA

end MatedCRT
