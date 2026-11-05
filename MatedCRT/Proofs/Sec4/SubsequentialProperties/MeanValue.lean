import MatedCRT.Proofs.Sec4.SubsequentialProperties.CircleAverage

/-!
# The mean value property of a weakly harmonic function at the centre of a disc

`eq_circleAverage_of_hasLaplacian_zero`: a function continuous on `cl(B_r(z))`, weakly harmonic on `B_r(z)`
(`HasLaplacian f 0 0`) and equal to `φ` on `∂B_r(z)` satisfies `f(z) = ⨍_{∂B_r(z)} φ`. This identifies the value at the
centre of the limit `f̄*_δ` of the discrete Dirichlet problems in Step 2 of the proof of Lemma 4.8
(paper/idla_mated_crt-corrected.tex, l.1846-1853: "by harmonicity", "by (eq:harmonic-function-same-bdry-values)").
The weak Laplacian bounds give the super- and sub-mean-value inequalities on the circles `∂B_s(z)`, `s < r`
(`superharmonicOfLaplacianLEStep_holds`, HarmonicBalls), and `s ↑ r` uses `tendsto_circleAverage`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls Real

/-- A weak lower bound `Δf ≥ 0` gives the weak upper bound `Δ(-f) ≤ 0`. -/
theorem laplacianLE_neg_of_laplacianGE_zero {f : ℂ → ℝ} {U : Set ℂ} (hge : LaplacianGE f 0 U) :
    LaplacianLE (-f) 0 U := by
  refine ⟨hge.1.neg, fun φ hφ hφ0 _ => ?_⟩
  have h := (hge.2 φ hφ hφ0).2
  simp only [integral_zero_measure] at h
  simpa only [integral_zero_measure, Pi.neg_apply, neg_mul, integral_neg] using neg_nonpos.mpr h

/-- **Mean value property at the centre.** If `f` is continuous on `cl(B_r(z))`, weakly harmonic on `B_r(z)` and
`f = φ` on `∂B_r(z)`, then `f(z) = ⨍_{∂B_r(z)} φ`. -/
theorem eq_circleAverage_of_hasLaplacian_zero {f φ : ℂ → ℝ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hfc : ContinuousOn f (closedBall z r)) (hlap : HasLaplacian f 0 0 (ball z r))
    (hbd : ∀ x ∈ sphere z r, f x = φ x) : f z = circleAverage φ z r := by
  have hfo : ContinuousOn f (ball z r) := hfc.mono ball_subset_closedBall
  have hsup : IsSuperharmonicOn (ball z r) f :=
    superharmonicOfLaplacianLEStep_holds _ f isOpen_ball hfo hlap.laplacianLE
  have hsub : IsSuperharmonicOn (ball z r) (-f) :=
    superharmonicOfLaplacianLEStep_holds _ (-f) isOpen_ball hfo.neg
      (laplacianLE_neg_of_laplacianGE_zero hlap.laplacianGE)
  have hmean : ∀ s : ℝ, 0 < s → s < r → f z = circleAverage f z s := by
    intro s hs hsr
    have hball : closedBall z s ⊆ ball z r := closedBall_subset_ball hsr
    have h1 := (hsup.2 z (mem_ball_self hr) s hs hball).2
    have h2 := (hsub.2 z (mem_ball_self hr) s hs hball).2
    rw [circleAverage_neg_fun, Pi.neg_apply] at h2
    linarith
  -- radii `R n ↑ r`
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set R : ℕ → ℝ := fun n => r - r * (1 / ((n : ℝ) + 1)) / 2 with hRdef
  have hRbounds : ∀ n, 0 < R n ∧ R n < r := by
    intro n
    have hu : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hu1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h1 : 0 < r * (1 / ((n : ℝ) + 1)) := mul_pos hr hu
    have h2 : r * (1 / ((n : ℝ) + 1)) ≤ r := mul_le_of_le_one_right hr.le hu1
    constructor <;> simp only [hRdef] <;> linarith
  have hR : Tendsto R atTop (𝓝 r) := by
    have := ((hinv.const_mul r).div_const 2).const_sub r
    simpa [hRdef] using this
  have hsph : ∀ᶠ n in atTop, sphere z |R n| ⊆ closedBall z r := Eventually.of_forall fun n => by
    rw [abs_of_pos (hRbounds n).1]
    exact sphere_subset_closedBall.trans (closedBall_subset_closedBall (hRbounds n).2.le)
  have hlim := tendsto_circleAverage hr.le hfc tendsto_const_nhds hR hsph
  have hconst : Tendsto (fun n => circleAverage f z (R n)) atTop (𝓝 (f z)) :=
    tendsto_const_nhds.congr fun n => hmean (R n) (hRbounds n).1 (hRbounds n).2
  rw [tendsto_nhds_unique hconst hlim]
  refine circleAverage_congr_sphere fun x hx => ?_
  rw [abs_of_pos hr] at hx
  exact hbd x hx

end MatedCRT
