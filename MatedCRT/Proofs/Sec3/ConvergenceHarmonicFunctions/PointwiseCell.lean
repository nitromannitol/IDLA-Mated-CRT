import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BadWindow
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellWindow

/-!
# Lemma 3.6: pathwise comparison of the discrete and interpolated exit values

For a fixed environment with cells of diameter `≤ d` meeting `B_r(z)` and a walk moving
along edges (adjacent cells meet), the boundary value at the discrete exit vertex and at
the (retracted) exit position of the interpolated walk differ by at most
`C (2η + d)^χ + 2K · exitWindowBad z r d h η X̂`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

theorem exitWindowBad_eq_zero_or_one (z : ℂ) (r d : ℝ) (h : ℝ≥0) (η : ℝ) (w : ℝ≥0 → ℂ) :
    exitWindowBad z r d h η w = 0 ∨ exitWindowBad z r d h η w = 1 := by
  unfold exitWindowBad
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The retraction moves a point by at most its distance outside the disk. -/
theorem dist_ballRetraction_self_le (z : ℂ) {r : ℝ} (hr : 0 < r) (e : ℂ) :
    dist (ballRetraction z r e) e ≤ max 0 (dist e z - r) := by
  have h1 : ballRetraction z r e - e = ((r / max r (dist e z) - 1 : ℝ) : ℂ) * (e - z) := by
    unfold ballRetraction
    push_cast
    ring
  rw [dist_eq_norm, h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← dist_eq_norm]
  rcases le_total (dist e z) r with h | h
  · rw [max_eq_left h, div_self hr.ne', sub_self, abs_zero, zero_mul]
    exact le_max_left _ _
  · rw [max_eq_right h]
    have hDpos : 0 < dist e z := hr.trans_le h
    rw [abs_of_nonpos (by rw [sub_nonpos, div_le_one hDpos]; exact h)]
    refine le_trans (le_of_eq ?_) (le_max_right _ _)
    rw [neg_sub, sub_mul, one_mul, div_mul_cancel₀ _ hDpos.ne']

/-- **Pathwise comparison** of the discrete and interpolated exit values. -/
theorem abs_exitValue_sub_le {ε mε d s η' : ℝ} {h : ℝ≥0} (hε : 0 ≤ ε) (hm : 0 < mε)
    (hmh : (1 / mε : ℝ).toNNReal ≤ h) {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : 0 ≤ d) (hds : d ≤ s) (hη' : 0 ≤ η') {ψ : ℂ → ℝ} {C χ : ℝ≥0}
    (hhol : HolderOnWith C χ ψ (closedBall z (r + s))) {K : ℝ}
    (hK : ∀ a ∈ closedBall z (r + s), |ψ a| ≤ K) {x : ℕ → ℤ}
    (hx0 : x 0 ∈ interiorCellVertices ε η (ball z r))
    (hstep : ∀ n, x (n + 1) = x n ∨ (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    (hdiam : ∀ k ∈ cellVertices ε η (ball z r), ∀ a ∈ cell ε η k, ∀ b ∈ cell ε η k,
      dist a b ≤ d) :
    |ψ (vertexPoint ε η (vExitPosition (interiorCellVertices ε η (ball z r)) x)) -
      ψ (ballRetraction z r (pathExitPosition (ball z r) (interpolatedWalk ε η mε x)))| ≤
      C * (2 * η' + d) ^ (χ : ℝ) + 2 * K * exitWindowBad z r d h η' (interpolatedWalk ε η mε x) := by
  classical
  have hs0 : 0 ≤ s := hd.trans hds
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK z (mem_closedBall_self (by linarith)))
  have hRHS0 : 0 ≤ C * (2 * η' + d) ^ (χ : ℝ) +
      2 * K * exitWindowBad z r d h η' (interpolatedWalk ε η mε x) := by
    have := exitWindowBad_nonneg z r d h η' (interpolatedWalk ε η mε x)
    have : 0 ≤ (C : ℝ) * (2 * η' + d) ^ (χ : ℝ) :=
      mul_nonneg C.2 (Real.rpow_nonneg (by linarith) _)
    positivity
  have hW0 : interpolatedWalk ε η mε x 0 = vertexPoint ε η (x 0) := by
    simpa using interpolatedWalk_natCast_div (ε := ε) hm η x 0
  have hpt0 : vertexPoint ε η (x 0) ∈ ball z r :=
    Sec7.cell_subset_ball_of_mem_interiorCellVertices hη hx0 (Sec7.vertexPoint_mem_cell hε (x 0))
  by_cases hex : ∃ n, x n ∉ interiorCellVertices ε η (ball z r)
  · set N := Nat.find hex with hNdef
    have hNout : x N ∉ interiorCellVertices ε η (ball z r) := Nat.find_spec hex
    have hlt : ∀ n < N, x n ∈ interiorCellVertices ε η (ball z r) := fun n hn => by
      by_contra hc
      exact Nat.find_min hex hn hc
    have hN1 : 1 ≤ N := by
      by_contra h0
      have : N = 0 := by omega
      exact hNout (this ▸ hx0)
    have hvexit : vExitPosition (interiorCellVertices ε η (ball z r)) x = x N := by
      simp only [vExitPosition, vExitTime, hex, ↓reduceDIte, ENat.toNat_natCast, hNdef]
    rw [hvexit]
    have hstepN : x N = x (N - 1) ∨ (cell ε η (x (N - 1)) ∩ cell ε η (x N)).Nonempty := by
      have := hstep (N - 1)
      rwa [Nat.sub_add_cancel hN1] at this
    have hprev := hlt (N - 1) (by omega)
    have hmeet : (cell ε η (x N) ∩ ball z r).Nonempty := by
      rcases hstepN with h' | ⟨q, hq1, hq2⟩
      · exact absurd (h' ▸ hprev) hNout
      · exact ⟨q, hq2, Sec7.cell_subset_ball_of_mem_interiorCellVertices hη hprev hq1⟩
    have hdN := hdiam (x N) hmeet
    obtain ⟨q, hqc, hqf⟩ : (cell ε η (x N) ∩ frontier (ball z r)).Nonempty := by
      by_contra hno
      exact hNout ⟨hmeet, hno⟩
    rw [frontier_ball z hr.ne', mem_sphere] at hqf
    have hpN := Sec7.vertexPoint_mem_cell hε (x N) (η := η)
    have ha : dist (vertexPoint ε η (x N)) z ≤ r + d := by
      have := hdN _ hpN _ hqc
      have := dist_triangle (vertexPoint ε η (x N)) q z
      linarith
    obtain ⟨hpos, hw1, hw2⟩ := discreteExit_window hε hm hη hN1 hlt hNout hstepN hdN
    have hw2' : (((N / mε : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤
        pathExitTime (ball z r) (interpolatedWalk ε η mε x) + h :=
      hw2.trans (by gcongr)
    set e := pathExitPosition (ball z r) (interpolatedWalk ε η mε x) with he
    have hRmem := ballRetraction_mem z hr e
    have hamem : vertexPoint ε η (x N) ∈ closedBall z (r + s) :=
      mem_closedBall.2 (by linarith)
    have hRmem' : ballRetraction z r e ∈ closedBall z (r + s) :=
      closedBall_subset_closedBall (by linarith) hRmem
    rcases exitWindowBad_eq_zero_or_one z r d h η' (interpolatedWalk ε η mε x) with hb | hb
    · have hdist : dist (vertexPoint ε η (x N)) e ≤ η' := by
        rw [← hpos]
        exact dist_le_of_exitWindowBad_eq_zero hb hw1 hw2'
      have hRe := dist_ballRetraction_self_le z hr e
      have hez : dist e z ≤ η' + r + d := by
        have := dist_triangle e (vertexPoint ε η (x N)) z
        rw [dist_comm] at hdist
        linarith
      have hRe' : dist (ballRetraction z r e) e ≤ η' + d :=
        hRe.trans (max_le (by linarith) (by linarith))
      have htot : dist (vertexPoint ε η (x N)) (ballRetraction z r e) ≤ 2 * η' + d := by
        have := dist_triangle (vertexPoint ε η (x N)) e (ballRetraction z r e)
        rw [dist_comm e] at this
        linarith
      have hhd := hhol.dist_le hamem hRmem'
      rw [hb, mul_zero, add_zero, ← Real.dist_eq]
      exact hhd.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg htot χ.2) C.2)
    · rw [hb, mul_one]
      have h1 := hK _ hamem
      have h2 := hK _ hRmem'
      have h3 := abs_sub (ψ (vertexPoint ε η (x N))) (ψ (ballRetraction z r e))
      have : 0 ≤ (C : ℝ) * (2 * η' + d) ^ (χ : ℝ) :=
        mul_nonneg C.2 (Real.rpow_nonneg (by linarith) _)
      linarith
  · have hall : ∀ n, x n ∈ interiorCellVertices ε η (ball z r) := fun n => by
      by_contra hc
      exact hex ⟨n, hc⟩
    have hvexit : vExitPosition (interiorCellVertices ε η (ball z r)) x = x 0 := by
      simp only [vExitPosition, vExitTime, hex, ↓reduceDIte]
      rfl
    have hin : ∀ t, interpolatedWalk ε η mε x t ∈ ball z r := fun t =>
      interpolatedWalk_mem_ball_of_le hε hm hη (N := ⌈mε * (t : ℝ)⌉₊ + 1) (by omega)
        (fun n _ => hall n) (by simpa using Nat.le_ceil (mε * (t : ℝ)))
    rw [hvexit, pathExitPosition_of_forall_mem hin, hW0,
      ballRetraction_of_mem z hr (ball_subset_closedBall hpt0), sub_self, abs_zero]
    exact hRHS0

end MatedCRT
