import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkMeasurability
import MatedCRT.Proofs.Sec7.MassBoundOdometer.Count

/-!
# Lemma 3.6: the discrete exit lies in a window of the interpolated walk

Let `N` be the first step at which the walk leaves
`A = V^ε(B_r(z)) \ V^ε(∂B_r(z))`. Before step `N` the marked points lie in the convex
ball `B_r(z)`, so the interpolated walk `X̂` stays in `B_r(z)` up to time `(N - 1)/m_ε`.
The cell of `x_N` meets `∂B_r(z)`; if it has diameter `≤ d`, then `η(x_N) = X̂(N/m_ε)` lies
outside `B_{r-d}(z)`. Hence `τ_{B_{r-d}(z)}(X̂) ≤ N/m_ε ≤ τ_{B_r(z)}(X̂) + 1/m_ε`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The interpolated walk at a lattice time is the marked point of the walk. -/
theorem interpolatedWalk_natCast_div {ε mε : ℝ} (hm : 0 < mε) (η : ℝ → ℂ) (x : ℕ → ℤ)
    (N : ℕ) : interpolatedWalk ε η mε x ((N / mε : ℝ).toNNReal) = vertexPoint ε η (x N) := by
  have hs : mε * (((N / mε : ℝ).toNNReal : ℝ≥0) : ℝ) = N := by
    rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg N) hm.le), mul_div_cancel₀ _ hm.ne']
  simp only [interpolatedWalk, hs, Nat.floor_natCast, sub_self, Complex.ofReal_zero, sub_zero,
    Complex.ofReal_one, one_mul, zero_mul, add_zero]

/-- Before the step `N - 1`, the interpolated walk stays in the ball. -/
theorem interpolatedWalk_mem_ball_of_le {ε mε : ℝ} (hε : 0 ≤ ε) (hm : 0 < mε)
    {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} {r : ℝ} {x : ℕ → ℤ} {N : ℕ} (hN : 1 ≤ N)
    (hin : ∀ n < N, x n ∈ interiorCellVertices ε η (ball z r)) {t : ℝ≥0}
    (ht : mε * (t : ℝ) ≤ ((N - 1 : ℕ) : ℝ)) :
    interpolatedWalk ε η mε x t ∈ ball z r := by
  have hpt : ∀ n < N, vertexPoint ε η (x n) ∈ ball z r := fun n hn =>
    Sec7.cell_subset_ball_of_mem_interiorCellVertices hη (hin n hn)
      (Sec7.vertexPoint_mem_cell hε (x n))
  have h0 : 0 ≤ mε * (t : ℝ) := mul_nonneg hm.le t.2
  have hfl := Nat.floor_le h0
  have hlt := Nat.lt_floor_add_one (mε * (t : ℝ))
  have hnN : ⌊mε * (t : ℝ)⌋₊ < N := by
    have : (⌊mε * (t : ℝ)⌋₊ : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := hfl.trans ht
    have : ⌊mε * (t : ℝ)⌋₊ ≤ N - 1 := by exact_mod_cast this
    omega
  simp only [interpolatedWalk]
  rcases eq_or_lt_of_le (sub_nonneg.2 hfl) with hθ | hθ
  · rw [← hθ, sub_zero, Complex.ofReal_zero, Complex.ofReal_one, one_mul, zero_mul, add_zero]
    exact hpt _ hnN
  · have hnN' : ⌊mε * (t : ℝ)⌋₊ + 1 < N := by
      have h1 : (⌊mε * (t : ℝ)⌋₊ : ℝ) < ((N - 1 : ℕ) : ℝ) := by linarith
      have : ⌊mε * (t : ℝ)⌋₊ < N - 1 := by exact_mod_cast h1
      omega
    have hc := convex_ball z r (hpt _ hnN) (hpt _ hnN') (by linarith : (0 : ℝ) ≤
      1 - (mε * (t : ℝ) - ⌊mε * (t : ℝ)⌋₊)) hθ.le (by ring)
    simpa only [Complex.real_smul] using hc

/-- The interpolated walk does not leave the ball before time `(N - 1) / m_ε`. -/
theorem le_pathExitTime_interpolatedWalk {ε mε : ℝ} (hε : 0 ≤ ε) (hm : 0 < mε)
    {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} {r : ℝ} {x : ℕ → ℤ} {N : ℕ} (hN : 1 ≤ N)
    (hin : ∀ n < N, x n ∈ interiorCellVertices ε η (ball z r)) :
    ((((N - 1 : ℕ) : ℝ) / mε).toNNReal : ℝ≥0∞) ≤
      pathExitTime (ball z r) (interpolatedWalk ε η mε x) := by
  unfold pathExitTime
  refine le_sInf ?_
  rintro _ ⟨t, rfl, ht⟩
  rw [ENNReal.coe_le_coe, Real.toNNReal_le_iff_le_coe, div_le_iff₀ hm, mul_comm]
  by_contra hlt
  exact ht (interpolatedWalk_mem_ball_of_le hε hm hη hN hin (not_le.mp hlt).le)

/-- **The exit window.** The discrete exit marked point is `X̂(N/m_ε)`, with
`τ_{B_{r-d}(z)}(X̂) ≤ N/m_ε ≤ τ_{B_r(z)}(X̂) + 1/m_ε`. -/
theorem discreteExit_window {ε mε d : ℝ} (hε : 0 ≤ ε) (hm : 0 < mε) {η : ℝ → ℂ}
    (hη : Continuous η) {z : ℂ} {r : ℝ} {x : ℕ → ℤ} {N : ℕ} (hN : 1 ≤ N)
    (hin : ∀ n < N, x n ∈ interiorCellVertices ε η (ball z r))
    (hout : x N ∉ interiorCellVertices ε η (ball z r))
    (hstep : x N = x (N - 1) ∨ (cell ε η (x (N - 1)) ∩ cell ε η (x N)).Nonempty)
    (hdiam : ∀ a ∈ cell ε η (x N), ∀ b ∈ cell ε η (x N), dist a b ≤ d) :
    interpolatedWalk ε η mε x ((N / mε : ℝ).toNNReal) = vertexPoint ε η (x N) ∧
    pathExitTime (ball z (r - d)) (interpolatedWalk ε η mε x) ≤
      (((N / mε : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ∧
    (((N / mε : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤
      pathExitTime (ball z r) (interpolatedWalk ε η mε x) + ((1 / mε : ℝ).toNNReal : ℝ≥0∞) := by
  have hpos := interpolatedWalk_natCast_div (ε := ε) hm η x N
  have hprev : N - 1 < N := by omega
  have hmeet : (cell ε η (x N) ∩ ball z r).Nonempty := by
    rcases hstep with h | ⟨q, hq1, hq2⟩
    · exact absurd (h ▸ hin _ hprev) hout
    · exact ⟨q, hq2, Sec7.cell_subset_ball_of_mem_interiorCellVertices hη (hin _ hprev) hq1⟩
  have hfront : (cell ε η (x N) ∩ frontier (ball z r)).Nonempty := by
    by_contra hno
    exact hout ⟨hmeet, hno⟩
  obtain ⟨q, hqc, hqf⟩ := hfront
  have hr : r ≠ 0 := by
    rintro rfl
    obtain ⟨_, _, hb⟩ := hmeet
    simp at hb
  rw [frontier_ball z hr, mem_sphere] at hqf
  have hfar : vertexPoint ε η (x N) ∉ ball z (r - d) := by
    intro hb
    rw [mem_ball] at hb
    have h1 := hdiam _ (Sec7.vertexPoint_mem_cell hε (x N)) _ hqc
    have h2 := dist_triangle q (vertexPoint ε η (x N)) z
    rw [dist_comm] at h1
    linarith
  refine ⟨hpos, ?_, ?_⟩
  · unfold pathExitTime
    exact sInf_le ⟨_, rfl, by rw [hpos]; exact hfar⟩
  · have hlow := le_pathExitTime_interpolatedWalk hε hm hη hN hin (z := z) (r := r)
    have hsplit : ((N / mε : ℝ).toNNReal) =
        (((N - 1 : ℕ) : ℝ) / mε).toNNReal + (1 / mε : ℝ).toNNReal := by
      rw [← Real.toNNReal_add (div_nonneg (Nat.cast_nonneg _) hm.le)
        (div_nonneg zero_le_one hm.le), ← add_div, Nat.cast_sub hN, Nat.cast_one, sub_add_cancel]
    rw [hsplit, ENNReal.coe_add]
    gcongr

end MatedCRT
