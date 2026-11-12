import MatedCRT.Defs.Map

/-!
# Block cells: a cell of size `N ε` is the union of `N` consecutive cells of size `ε`

The cell `H^{Nε}_{Nεj} = η([Nε(j-1), Nεj])` is the union of the cells `H^ε_{εk} = η([ε(k-1), εk])`
for `k` in the block `N(j-1) < k ≤ Nj`.
-/

namespace MatedCRT.FirstPass.Derived

open MatedCRT Set

/-- The interval `[Nε(j-1), Nεj]` is the union of the intervals `[ε(k-1), εk]`, `N(j-1) < k ≤ Nj`. -/
theorem Icc_mul_eq_iUnion {ε : ℝ} {N : ℕ} (hN : 0 < N) (j : ℤ) :
    Icc ((N : ℝ) * ε * ((j : ℝ) - 1)) ((N : ℝ) * ε * (j : ℝ)) =
      ⋃ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), Icc (ε * ((k : ℝ) - 1)) (ε * (k : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases lt_trichotomy ε 0 with hε | hε | hε
  · -- both sides are empty
    have h1 : (N : ℝ) * ε * (j : ℝ) < (N : ℝ) * ε * ((j : ℝ) - 1) := by
      have : (N : ℝ) * ε < 0 := mul_neg_of_pos_of_neg (by linarith) hε
      nlinarith
    rw [Icc_eq_empty (not_le.2 h1)]
    ext x
    simp only [mem_empty_iff_false, mem_iUnion, Finset.mem_Ioc, mem_Icc, exists_prop, false_iff]
    rintro ⟨k, -, h2, h3⟩
    nlinarith
  · subst hε
    ext x
    simp only [mul_zero, zero_mul, mem_Icc, mem_iUnion, Finset.mem_Ioc, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(N : ℤ) * j, ⟨?_, le_refl _⟩, h1, h2⟩
      have : (N : ℤ) * (j - 1) < (N : ℤ) * j := by
        have : (0 : ℤ) < N := by exact_mod_cast hN
        nlinarith
      exact this
    · rintro ⟨k, -, h1, h2⟩
      exact ⟨h1, h2⟩
  · ext x
    simp only [mem_Icc, mem_iUnion, Finset.mem_Ioc, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      set k : ℤ := max ⌈x / ε⌉ ((N : ℤ) * (j - 1) + 1) with hk
      have hxe1 : (N : ℝ) * ((j : ℝ) - 1) ≤ x / ε := by
        rw [le_div_iff₀ hε]; linarith
      have hxe2 : x / ε ≤ (N : ℝ) * (j : ℝ) := by
        rw [div_le_iff₀ hε]; linarith
      have hceil_le : ⌈x / ε⌉ ≤ (N : ℤ) * j := by
        rw [Int.ceil_le]; exact_mod_cast hxe2
      have hNj : (N : ℤ) * (j - 1) + 1 ≤ (N : ℤ) * j := by
        have : (1 : ℤ) ≤ N := by exact_mod_cast hN
        nlinarith
      refine ⟨k, ⟨?_, max_le hceil_le hNj⟩, ?_, ?_⟩
      · exact lt_of_lt_of_le (Int.lt_add_one_iff.2 le_rfl) (le_max_right _ _)
      · -- ε (k - 1) ≤ x
        rcases le_total ⌈x / ε⌉ ((N : ℤ) * (j - 1) + 1) with hle | hle
        · rw [hk, max_eq_right hle]
          push_cast
          have : (N : ℝ) * ((j : ℝ) - 1) + 1 - 1 = (N : ℝ) * ((j : ℝ) - 1) := by ring
          rw [this]
          nlinarith
        · rw [hk, max_eq_left hle]
          have h3 : ((⌈x / ε⌉ : ℤ) : ℝ) - 1 < x / ε := by
            have := Int.ceil_lt_add_one (x / ε)
            linarith [Int.lt_ceil.1 (show ⌈x / ε⌉ - 1 < ⌈x / ε⌉ by omega)]
          rw [lt_div_iff₀ hε] at h3
          linarith
      · -- x ≤ ε k
        have : x / ε ≤ (k : ℝ) := le_trans (Int.le_ceil _) (by exact_mod_cast le_max_left _ _)
        rw [div_le_iff₀ hε] at this
        linarith
    · rintro ⟨k, ⟨hk1, hk2⟩, h1, h2⟩
      have hk1' : (N : ℝ) * ((j : ℝ) - 1) ≤ (k : ℝ) - 1 := by
        have : (N : ℤ) * (j - 1) ≤ k - 1 := by omega
        have h' : ((N * (j - 1) : ℤ) : ℝ) ≤ ((k - 1 : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at h'
        exact h'
      have hk2' : (k : ℝ) ≤ (N : ℝ) * (j : ℝ) := by exact_mod_cast hk2
      constructor
      · nlinarith
      · nlinarith

/-- A cell of size `N ε` is the union of the `N` cells of size `ε` in its block. -/
theorem cell_mul_eq_iUnion (η : ℝ → ℂ) {ε : ℝ} {N : ℕ} (hN : 0 < N) (j : ℤ) :
    cell ((N : ℝ) * ε) η j =
      ⋃ k ∈ Finset.Ioc ((N : ℤ) * (j - 1)) ((N : ℤ) * j), cell ε η k := by
  unfold cell
  rw [Icc_mul_eq_iUnion hN j, image_iUnion₂]

end MatedCRT.FirstPass.Derived
