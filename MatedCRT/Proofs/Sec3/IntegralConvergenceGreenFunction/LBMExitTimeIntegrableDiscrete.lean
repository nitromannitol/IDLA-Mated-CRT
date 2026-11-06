import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LBMExitTimeIntegrableTruncated
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellWindow

/-!
# LBM exit time: discrete exit from an inner ball and the walk moment bound

For the interpolated walk of a mated-CRT map, the exit time from the inner ball `B(z, r - d)` is at most the
normalized exit index `N / m_ε` of the walk from the interior cells of `B(z, r)`, as soon as the exit cell has
diameter at most `d`. The truncated exit functional of the walk is therefore dominated by the normalized exit
index, and its lower Lebesgue integral is controlled by the second exit moment
(`lintegral_ofReal_truncatedExit_le`), which is the discrete input of `LBMExitTimeIntegrableStep`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- If the first exit index of `x` from `A` is the natural number `k`, then `x k ∉ A`. -/
theorem not_mem_of_vExitTime_eq {A : Set ℤ} {x : ℕ → ℤ} {k : ℕ} (h : vExitTime A x = (k : ℕ∞)) :
    x k ∉ A := by
  classical
  unfold vExitTime at h
  split_ifs at h with hex
  · have hk : Nat.find hex = k := by exact_mod_cast h
    rw [← hk]
    exact Nat.find_spec hex
  · exact absurd h.symm (ENat.natCast_ne_top k)

/-- The normalized lattice time `k / m_ε` in `ℝ≥0∞`, as a multiple of the scale `(m_ε)⁻¹`. -/
theorem toNNReal_natCast_div_eq (k : ℕ) (mε : ℝ) :
    ((((k : ℝ) / mε).toNNReal : ℝ≥0) : ℝ≥0∞) =
      (k : ℝ≥0∞) * ((Real.toNNReal mε⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [div_eq_mul_inv, Real.toNNReal_mul (Nat.cast_nonneg k), Real.toNNReal_natCast,
    ENNReal.coe_mul, ENNReal.coe_natCast]

/-- **Discrete exit window.** If the walk's vertex `x N` is not an interior cell vertex of `B(z, r)` and the cells
meeting the sphere `∂B(z, r)` have diameter at most `d`, then the interpolated walk leaves `B(z, r - d)` no later
than `N / m_ε`: its marked point at time `N / m_ε` is `η(x_N)`, which lies outside `B(z, r - d)`. -/
theorem pathExitTime_ball_sub_le_of_not_mem_interior {ε mε : ℝ} (hε : 0 ≤ ε) (hm : 0 < mε)
    {η : ℝ → ℂ} {z : ℂ} {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) {x : ℕ → ℤ} {N : ℕ}
    (hout : x N ∉ interiorCellVertices ε η (ball z r))
    (hdiam : (cell ε η (x N) ∩ frontier (ball z r)).Nonempty →
      ∀ p ∈ cell ε η (x N), ∀ q ∈ cell ε η (x N), dist p q ≤ d) :
    pathExitTime (ball z (r - d)) (interpolatedWalk ε η mε x) ≤
      ((((N : ℝ) / mε).toNNReal : ℝ≥0) : ℝ≥0∞) := by
  apply pathExitTime_le_of_not_mem
  rw [interpolatedWalk_natCast_div hm η x N]
  intro hball
  have hv : vertexPoint ε η (x N) ∈ cell ε η (x N) := Sec7.vertexPoint_mem_cell hε (x N)
  have hball' : dist (vertexPoint ε η (x N)) z < r - d := mem_ball.1 hball
  by_cases hmeet : (cell ε η (x N) ∩ ball z r).Nonempty
  · have hfront : (cell ε η (x N) ∩ frontier (ball z r)).Nonempty := by
      by_contra hno
      exact hout (Set.mem_sdiff_of_mem hmeet hno)
    obtain ⟨q, hqc, hqf⟩ := hfront
    have hqf' : q ∈ frontier (ball z r) := hqf
    rw [frontier_ball z hr.ne', mem_sphere] at hqf'
    have h1 := hdiam ⟨q, hqc, hqf⟩ (vertexPoint ε η (x N)) hv q hqc
    have h2 := dist_triangle q (vertexPoint ε η (x N)) z
    have h3 := dist_comm (vertexPoint ε η (x N)) q
    linarith
  · exact hmeet ⟨vertexPoint ε η (x N), hv, mem_ball.2 (by linarith)⟩

/-- **Pointwise domination.** The truncated exit functional of the interpolated walk, read in `ℝ≥0∞`, is at most
the normalized exit index times `(m_ε)⁻¹`, given the cell-diameter bound. -/
theorem ofReal_truncatedExit_le {ε mε : ℝ} (hε : 0 ≤ ε) (hm : 0 < mε) {η : ℝ → ℂ}
    {z : ℂ} {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (n : ℕ) {x : ℕ → ℤ}
    (hcell : ∀ k : ℤ, (cell ε η k ∩ frontier (ball z r)).Nonempty →
      ∀ p ∈ cell ε η k, ∀ q ∈ cell ε η k, dist p q ≤ d) :
    ENNReal.ofReal (truncatedExitFunctional (ball z (r - d)) n (interpolatedWalk ε η mε x)) ≤
      (vExitTime (interiorCellVertices ε η (ball z r)) x : ℝ≥0∞) *
        ((Real.toNNReal mε⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  have hc0 : ((Real.toNNReal mε⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    refine ENNReal.coe_ne_zero.2 ?_
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    exact inv_pos.2 hm
  rw [ofReal_truncatedExitFunctional]
  refine (min_le_left _ _).trans ?_
  generalize hN : vExitTime (interiorCellVertices ε η (ball z r)) x = N
  induction N using ENat.recTopCoe with
  | top => simp [hc0]
  | coe k =>
    simp only [ENat.toENNReal_coe]
    have hout := not_mem_of_vExitTime_eq hN
    refine (pathExitTime_ball_sub_le_of_not_mem_interior hε hm hr hd hout (hcell (x k))).trans ?_
    rw [toNNReal_natCast_div_eq]

/-- `X ≤ 1 + X²` in `ℝ≥0∞`. -/
theorem le_one_add_sq_ennreal (X : ℝ≥0∞) : X ≤ 1 + X ^ 2 := by
  rcases le_total X 1 with h | h
  · exact h.trans le_self_add
  · exact (le_mul_of_one_le_right zero_le h).trans (by rw [sq]; exact le_add_self)

/-- **Walk moment bound for the truncated exit functional.** Given the second exit moment of the walk from the
interior cells of `B(z, r)` (`hK`), the lower integral of the truncated exit functional of the interpolated walk
from `B(z, r - d)` is at most `1 + K`. -/
theorem lintegral_ofReal_truncatedExit_le {ε mε : ℝ} (hε : 0 ≤ ε) (hm : 0 < mε) {η : ℝ → ℂ}
    (m : ℤ → ℤ → ℕ) (a : ℤ)
    {z : ℂ} {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (n : ℕ)
    (hcell : ∀ k : ℤ, (cell ε η k ∩ frontier (ball z r)).Nonempty →
      ∀ p ∈ cell ε η k, ∀ q ∈ cell ε η k, dist p q ≤ d)
    {K : ℝ≥0∞}
    (hK : ((Real.toNNReal mε⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
      exitTimeMoment m (interiorCellVertices ε η (ball z r)) a 2 ≤ K) :
    ∫⁻ x, ENNReal.ofReal (truncatedExitFunctional (ball z (r - d)) n (interpolatedWalk ε η mε x))
      ∂srwLaw m a ≤ 1 + K := by
  have hcT : ((Real.toNNReal mε⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  calc ∫⁻ x, ENNReal.ofReal (truncatedExitFunctional (ball z (r - d)) n
        (interpolatedWalk ε η mε x)) ∂srwLaw m a
      ≤ ∫⁻ x, (1 + ((vExitTime (interiorCellVertices ε η (ball z r)) x : ℝ≥0∞) *
          ((Real.toNNReal mε⁻¹ : ℝ≥0) : ℝ≥0∞)) ^ 2) ∂srwLaw m a := by
        refine lintegral_mono fun x => ?_
        exact (ofReal_truncatedExit_le hε hm hr hd n hcell).trans (le_one_add_sq_ennreal _)
    _ = 1 + ((Real.toNNReal mε⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
          exitTimeMoment m (interiorCellVertices ε η (ball z r)) a 2 := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          exitTimeMoment, ← lintegral_const_mul' _ _ hcT]
        congr 1
        exact lintegral_congr fun x => by ring
    _ ≤ 1 + K := add_le_add le_rfl hK

end MatedCRT
