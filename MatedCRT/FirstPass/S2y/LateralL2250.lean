import MatedCRT.FirstPass.S2y.ConeApproxIdentity

/-!
# L² limit of the lateral smear: dominated convergence for the lateral kernel

For a whole-plane GFF, the variance of `∫ g(x) L(x) dx` is the double integral of the lateral kernel
`K_L(x,y) = wholePlaneCov x y - radialCov ‖x‖ ‖y‖` against `g(x) g(y)`. The L² limit of the lateral smear follows from
dominated convergence on a compact square, once the kernel is integrable there and the mollified test functions
`g_n = circleKernel φ ε_n - φ` are uniformly bounded, supported in a fixed ball and tend to `0` pointwise.

This file proves the abstract dominated-convergence step; the kernel identities are in later files.
-/

open MeasureTheory Filter Topology Set Metric
open scoped Real

namespace MatedCRT.LQGMeasure

/-- **Dominated convergence for a bilinear kernel on a compact square.** If the kernel `K` is integrable on
`closedBall 0 R ×ˢ closedBall 0 R`, and the functions `g n` are measurable, bounded by `M`, vanish off `closedBall 0 R`
and tend to `0` pointwise, then `∬ g_n(x) g_n(y) K(x,y) dx dy → 0`. -/
theorem tendsto_double_integral_zero_of_pointwise {K : ℂ × ℂ → ℝ} {R M : ℝ} (hKm : Measurable K)
    (hK : IntegrableOn K (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R)) {g : ℕ → ℂ → ℝ}
    (hgm : ∀ n, Measurable (g n)) (hgM : ∀ n x, |g n x| ≤ M)
    (hgR : ∀ n x, x ∉ closedBall (0 : ℂ) R → g n x = 0)
    (hg : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p : ℂ × ℂ, g n p.1 * g n p.2 * K p ∂(volume.prod volume)) atTop (𝓝 0) := by
  set S : Set (ℂ × ℂ) := closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R with hSdef
  have hS : MeasurableSet S := measurableSet_closedBall.prod measurableSet_closedBall
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgM 0 0)
  have hbd : Integrable (S.indicator fun p : ℂ × ℂ => (M * M) * ‖K p‖) (volume.prod volume) :=
    (integrable_indicator_iff hS).mpr (hK.norm.const_mul (M * M))
  have hF : ∀ n, AEStronglyMeasurable (fun p : ℂ × ℂ => g n p.1 * g n p.2 * K p) (volume.prod volume) :=
    fun n => ((((hgm n).comp measurable_fst).mul ((hgm n).comp measurable_snd)).mul hKm).aestronglyMeasurable
  have hdom : ∀ n, ∀ᵐ p ∂(volume.prod volume),
      ‖g n p.1 * g n p.2 * K p‖ ≤ S.indicator (fun p : ℂ × ℂ => (M * M) * ‖K p‖) p := by
    intro n
    refine Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ S
    · rw [indicator_of_mem hp]
      have h1 : |g n p.1| ≤ M := hgM n p.1
      have h2 : |g n p.2| ≤ M := hgM n p.2
      have h3 : |g n p.1| * |g n p.2| ≤ M * M :=
        mul_le_mul h1 h2 (abs_nonneg _) hM0
      calc ‖g n p.1 * g n p.2 * K p‖ = (|g n p.1| * |g n p.2|) * ‖K p‖ := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ (M * M) * ‖K p‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    · rw [indicator_of_notMem hp]
      by_cases h1 : p.1 ∈ closedBall (0 : ℂ) R
      · have h2 : p.2 ∉ closedBall (0 : ℂ) R := fun h2 => hp ⟨h1, h2⟩
        simp [hgR n _ h2]
      · simp [hgR n _ h1]
  have hlim : ∀ᵐ p ∂(volume.prod volume),
      Tendsto (fun n => g n p.1 * g n p.2 * K p) atTop (𝓝 ((fun _ => (0 : ℝ)) p)) := by
    refine Eventually.of_forall fun p => ?_
    have := ((hg p.1).mul (hg p.2)).mul_const (K p)
    simpa using this
  have key := tendsto_integral_of_dominated_convergence _ hF hbd hdom hlim
  simpa using key

end MatedCRT.LQGMeasure
