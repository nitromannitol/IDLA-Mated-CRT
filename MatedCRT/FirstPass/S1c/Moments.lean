import MatedCRT.FirstPass.S1c.Retract

/-!
# Supersolutions tested on a countable family (Lemma 1 analytic layer, fleet note G-hT)

For a locally finite measure `ν` with `ν(B̄_R) < ∞`, a function `w` continuous on `B̄_R` satisfies the
`LaplacianLE` inequality on `B_R` (test class `IsTestFunction (ball 0 R)`, `0 ≤ φ`) if and only if its
pairing with the countable family `φs k` of `exists_dense_nonnegTest_family` satisfies the inequality
for each member. The direction `⇒` is the definition; `⇐` is approximation of an arbitrary test function by the
family in the sup norm of `φ` and `Δφ` on `B̄_R`, both sides being integrals over a set of finite volume.
Classical measure theory and potential theory (Armitage-Gardiner, `LaplacianLE` as the distributional
inequality `Δw ≤ ν`); no paper-specific input.
-/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory HarmonicBalls

variable {R : ℝ}

/-- A continuous function vanishing outside `B̄_R` is integrable against a measure finite on `B̄_R`. -/
theorem integrable_of_continuous_of_support {μ : Measure ℂ} (hμ : μ (closedBall (0 : ℂ) R) < ⊤)
    {f : ℂ → ℝ} (hf : Continuous f) (hsupp : ∀ x, x ∉ closedBall (0 : ℂ) R → f x = 0) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.mono' (g := indicator (closedBall (0 : ℂ) R) (fun _ => C))
    ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hμ.ne))
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ closedBall (0 : ℂ) R
  · rw [indicator_of_mem hx]
    exact hC x hx
  · rw [indicator_of_notMem hx, hsupp x hx, norm_zero]

/-- A function vanishing on the complement of its topological support vanishes outside the support. -/
theorem eq_zero_of_not_mem_tsupport_fn {φ : ℂ → ℝ} {U : Set ℂ} (hφ : tsupport φ ⊆ U) {x : ℂ}
    (hx : x ∉ U) : φ x = 0 :=
  (notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hφ h)).eq_of_nhds

/-- The product of a continuous function with the Laplacian of a test function on `B_R` is integrable against
Lebesgue measure, and vanishes outside `B̄_R`. -/
theorem integrable_mul_laplacian {w : ℂ → ℝ} (hw : Continuous w) {φ : ℂ → ℝ}
    (hφ : IsTestFunction (ball (0 : ℂ) R) φ) :
    Integrable (fun x => w x * Laplacian.laplacian φ x) := by
  have hΔ := continuous_laplacian_of_contDiff (contDiff_two_of_isTestFunction hφ)
  refine integrable_of_continuous_of_support (R := R) (μ := volume) measure_closedBall_lt_top
    (hw.mul hΔ) fun x hx => ?_
  have hxU : x ∉ ball (0 : ℂ) R := fun h => hx (ball_subset_closedBall h)
  rw [laplacian_eq_zero_of_not_mem_tsupport hφ.2.2 hxU, mul_zero]

/-- The pairing of a continuous function with `Δφ` for `φ` a test function on `B_R`: the integrand may be
computed with any continuous extension of `w` from `B̄_R`. -/
theorem integral_mul_laplacian_eq_extend (hR : 0 ≤ R) (w : ℂ → ℝ) (hw : ContinuousOn w (closedBall (0 : ℂ) R))
    {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) R) φ) :
    ∫ x, w x * Laplacian.laplacian φ x =
      ∫ x, extendCM R hR ⟨_, hw.domRestrict⟩ x * Laplacian.laplacian φ x := by
  congr 1
  funext x
  by_cases hx : x ∈ closedBall (0 : ℂ) R
  · exact congrArg (fun t => t * Laplacian.laplacian φ x) (extendCM_apply hR ⟨_, hw.domRestrict⟩ hx).symm
  · have hxU : x ∉ ball (0 : ℂ) R := fun h => hx (ball_subset_closedBall h)
    rw [laplacian_eq_zero_of_not_mem_tsupport hφ.2.2 hxU, mul_zero, mul_zero]

end MatedCRT
