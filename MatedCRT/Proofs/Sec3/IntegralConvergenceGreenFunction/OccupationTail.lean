import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ExitTimeTail
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Geometry

/-! Pathwise control of the killed-walk occupation tail. -/

namespace MatedCRT

open Set Metric

/-- A marked point of an interior cell lies in the ball. -/
theorem vertexPoint_mem_ball_of_mem_interior {ε : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (hη : Continuous η) {z : ℂ} {r : ℝ} {k : ℤ}
    (hk : k ∈ interiorCellVertices ε η (ball z r)) :
    vertexPoint ε η k ∈ ball z r :=
  Sec7.interior_cell_subset_ball hη hk (Tightness.vertexPoint_mem_cell hε k)

/-- For a path with finite exit time, truncating its occupation sum at `N`
leaves at most the test-function bound times the exit time, and leaves no
remainder when exit has already occurred. -/
theorem abs_killed_occupation_tail_le (A : Set ℤ) (x : ℕ → ℤ) (g : ℤ → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hg : ∀ b ∈ A, |g b| ≤ M)
    (N : ℕ) (hτ : vExitTime A x ≠ ⊤) :
    |(∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n)) -
      ∑ n ∈ Finset.range N,
        if (n : ℕ∞) < vExitTime A x then g (x n) else 0| ≤
      if N < (vExitTime A x).toNat then M * (vExitTime A x).toNat else 0 := by
  have hτ' : vExitTime A x = ((vExitTime A x).toNat : ℕ∞) :=
    (ENat.natCast_toNat hτ).symm
  by_cases hN : N < (vExitTime A x).toNat
  · have htrunc : (∑ n ∈ Finset.range N,
        if (n : ℕ∞) < vExitTime A x then g (x n) else 0) =
        ∑ n ∈ Finset.range N, g (x n) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnτ : (n : ℕ∞) < vExitTime A x := by
        rw [hτ']
        exact Nat.cast_lt.mpr (lt_trans (Finset.mem_range.mp hn) hN)
      simp [hnτ]
    simp only [hN, ↓reduceIte, htrunc]
    rw [← Finset.sum_Ico_eq_sub _ hN.le]
    calc
      |∑ n ∈ Finset.Ico N (vExitTime A x).toNat, g (x n)| ≤
          ∑ n ∈ Finset.Ico N (vExitTime A x).toNat, |g (x n)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Ico N (vExitTime A x).toNat, M := by
        apply Finset.sum_le_sum
        intro n hn
        apply hg
        apply mem_of_lt_vExitTime
        rw [hτ']
        exact Nat.cast_lt.mpr (Finset.mem_Ico.mp hn).2
      _ ≤ M * (vExitTime A x).toNat := by
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have hle : (↑((vExitTime A x).toNat - N) : ℝ) ≤ (vExitTime A x).toNat := by
          exact_mod_cast Nat.sub_le (vExitTime A x).toNat N
        nlinarith
  · have hle : (vExitTime A x).toNat ≤ N := Nat.le_of_not_gt hN
    have htrunc : (∑ n ∈ Finset.range N,
        if (n : ℕ∞) < vExitTime A x then g (x n) else 0) =
        ∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n) := by
      rw [← Finset.sum_range_add_sum_Ico _ hle]
      have hfirst : (∑ n ∈ Finset.range (vExitTime A x).toNat,
          if (n : ℕ∞) < vExitTime A x then g (x n) else 0) =
          ∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnτ : (n : ℕ∞) < vExitTime A x := by
          rw [hτ']
          exact Nat.cast_lt.mpr (Finset.mem_range.mp hn)
        simp [hnτ]
      have hzero : (∑ n ∈ Finset.Ico (vExitTime A x).toNat N,
          if (n : ℕ∞) < vExitTime A x then g (x n) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hnτ : ¬ (n : ℕ∞) < vExitTime A x := by
          rw [hτ']
          exact not_lt.mpr (Nat.cast_le.mpr (Finset.mem_Ico.mp hn).1)
        simp [hnτ]
      rw [hfirst, hzero, add_zero]
    simp [hN, htrunc]

/-- Integrating the pathwise estimate bounds the error between the expected
full and truncated occupation sums by the expected exit-time tail. -/
theorem abs_integral_killed_occupation_tail_le (μ : MeasureTheory.Measure (ℕ → ℤ))
    (A : Set ℤ) (g : ℤ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg : ∀ b ∈ A, |g b| ≤ M) (N : ℕ)
    (hfinite : ∀ᵐ x ∂μ, vExitTime A x ≠ ⊤)
    (hfull : MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n)) μ)
    (htrunc : MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range N,
        if (n : ℕ∞) < vExitTime A x then g (x n) else 0) μ)
    (htail : MeasureTheory.Integrable
      (fun x => if N < (vExitTime A x).toNat then M * (vExitTime A x).toNat else 0) μ) :
    |(∫ x, ∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n) ∂μ) -
      ∫ x, ∑ n ∈ Finset.range N,
        if (n : ℕ∞) < vExitTime A x then g (x n) else 0 ∂μ| ≤
      ∫ x, if N < (vExitTime A x).toNat then M * (vExitTime A x).toNat else 0 ∂μ := by
  rw [← MeasureTheory.integral_sub hfull htrunc]
  calc
    |∫ x, ((∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n)) -
        ∑ n ∈ Finset.range N,
          if (n : ℕ∞) < vExitTime A x then g (x n) else 0) ∂μ| ≤
        ∫ x, |(∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n)) -
          ∑ n ∈ Finset.range N,
            if (n : ℕ∞) < vExitTime A x then g (x n) else 0| ∂μ :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ _ := by
      apply MeasureTheory.integral_mono_ae (hfull.sub htrunc).abs htail
      filter_upwards [hfinite] with x hx
      exact abs_killed_occupation_tail_le A x g M hM hg N hx

end MatedCRT
