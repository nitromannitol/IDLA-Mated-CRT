import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ExitCDF
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic

/-! Maximum-principle ingredients for the continuum obstacle comparison. -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls Laplacian
open scoped ENNReal

/-- Wherever a candidate lies strictly above the scaled least supersolution, it lies
strictly above the obstacle away from the pole. This does not require the obstacle
inequality to hold strictly on the interior of a closure. -/
theorem strict_comparison_subset_noncoincidence
    {μ : Measure ℂ} {ρ t c : ℝ} {w : ℂ → ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) :
    {x ∈ ball (0 : ℂ) ρ | c * leastSupersolution μ ρ 0 t x < w x} ⊆
      {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * c * greenFunction (ball 0 ρ) 0 x < w x} := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · right
    have h := mul_le_mul_of_nonneg_left (le_leastSupersolution (μ := μ) ht (ball_subset_closedBall hx.1) hx0) hc
    have hid : c * (-t * greenFunction (ball 0 ρ) 0 x) =
        -t * c * greenFunction (ball 0 ρ) 0 x := by ring
    rw [hid] at h
    exact h.trans_lt hx.2

/-- A nonempty bounded open set cannot support a positive weakly subharmonic
function that is continuous on its closure and nonpositive on its boundary. -/
theorem eq_empty_of_positive_laplacianGE_zero {W : Set ℂ} {f : ℂ → ℝ}
    (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hfc : ContinuousOn f (closure W))
    (hpos : ∀ x ∈ W, 0 < f x) (hfr : ∀ x ∈ frontier W, f x ≤ 0)
    (hLap : LaplacianGE f 0 W) : W = ∅ := by
  have hneg : LaplacianLE (-f) 0 W := by
    refine ⟨hLap.1.neg, fun φ hφ hφ0 _ => ?_⟩
    have h := (hLap.2 φ hφ hφ0).2
    simp only [integral_zero_measure] at h
    simpa only [integral_zero_measure, Pi.neg_apply, neg_mul, integral_neg] using neg_nonpos.mpr h
  have hsuper := superharmonicOfLaplacianLEStep_holds W (-f) hW
    ((hfc.mono subset_closure).neg) hneg
  apply eq_empty_of_pos_of_subMean hWb hfc hpos hfr
  intro x hx
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hW x hx
  have hr2 : 0 < r / 2 := half_pos hr
  have hsub : closedBall x (r / 2) ⊆ W :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrsub
  refine ⟨r / 2, hr2, hsub, ?_⟩
  have hm := (hsuper.2 x hx (r / 2) hr2 hsub).2
  rw [circleAverage_neg_fun, Pi.neg_apply] at hm
  linarith

end MatedCRT
