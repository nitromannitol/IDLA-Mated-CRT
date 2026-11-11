import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Steps.SecA.Basic
import MatedCRT.FirstPass.Frozen.S5c

/-!
# FIRST PASS, Lemma 5.3: superharmonicity of the rescaled obstacle (G-5-3 Section 1, eq. (5) input)

If `Δ v ≥ 0` distributionally on `U` (the Laplacian of the least supersolution is a nonnegative measure,
`ClusterOpenLaplacianStmt`, Harmonic-Balls Lemma 3.2), then `c·(-v)` is distributionally superharmonic for `c > 0`,
hence mean-value superharmonic by the frozen classical step `FPSuperharmonicOfLaplacianLE`. Used for
`R_n = -w_{s_n} / s_n`.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology Laplacian
open _root_.HarmonicBalls

/-- If `Δ v = μp ≥ 0` in `U`, then `Δ (-(c v)) ≤ 0` in `U` for `c > 0`. -/
lemma laplacianLE_neg_mul_of_hasLaplacian {v : ℂ → ℝ} {μp : Measure ℂ} {U : Set ℂ} {c : ℝ} (hc : 0 < c)
    (h : HasLaplacian v μp 0 U) : LaplacianLE (fun x => -(c * v x)) 0 U := by
  have hloc : LocallyIntegrableOn (fun x => -(c * v x)) U := by
    have e : (fun x => -(c * v x)) = fun x => (-c) * v x := by
      funext x
      ring
    rw [e]
    exact h.1.smul (-c)
  refine ⟨hloc, ?_⟩
  intro φ hφ hφ0 _
  obtain ⟨_, _, heq⟩ := h.2 φ hφ
  have hnn : 0 ≤ ∫ x, φ x ∂μp := integral_nonneg hφ0
  have e : (fun x => -(c * v x) * Δ φ x) = fun x => -c * (v x * Δ φ x) := by
    funext x
    ring
  simp only [integral_zero_measure]
  rw [e, integral_const_mul, heq, integral_zero_measure, sub_zero]
  have := mul_nonneg hc.le hnn
  linarith

/-- The rescaled obstacle `x ↦ -(c v x)` is mean-value superharmonic on an open set `U` when `Δ v ≥ 0` there,
given the frozen classical step. -/
lemma isSuperharmonicOn_neg_mul_of_hasLaplacian (hsup : FPSuperharmonicOfLaplacianLE) {v : ℂ → ℝ}
    {μp : Measure ℂ} {U : Set ℂ} {c : ℝ} (hU : IsOpen U) (hc : 0 < c) (hcont : ContinuousOn v U)
    (h : HasLaplacian v μp 0 U) : IsSuperharmonicOn U (fun x => -(c * v x)) :=
  hsup U _ hU (continuousOn_const.mul hcont).neg (laplacianLE_neg_mul_of_hasLaplacian hc h)

/-- Mean-value inequality of a superharmonic function at the centre of a closed disk inside its domain. -/
lemma circleAverage_le_of_isSuperharmonicOn {U : Set ℂ} {g : ℂ → ℝ} (hs : IsSuperharmonicOn U g)
    {x : ℂ} (hx : x ∈ U) {r : ℝ} (hr : 0 < r) (hsub : closedBall x r ⊆ U) :
    Real.circleAverage g x r ≤ g x :=
  (hs.2 x hx r hr hsub).2

end MatedCRT.S5c
