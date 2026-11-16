import MatedCRT.FirstPass.Derived.ConeReferenceData

/-! # Circle averages of the reference cone inside the unit disk -/

set_option autoImplicit false

open MeasureTheory Metric HarmonicBalls MarkovProcess LQGMetric

namespace MatedCRT.FirstPass.Derived

/-- A reference-cone circle average equals that of the logarithmically
singular field when the averaging circle lies in the closed unit disk. -/
theorem coneRefCircle_eq_fieldCircleAverage_of_add_le
    (γ : ℝ) (c : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (h : ‖z‖ + r ≤ 1) :
    coneRefCircle γ c w r z = fieldCircleAverage γ c r z := by
  have hzero : Real.circleAverage (coneRefField c w) z r = 0 := by
    have heq : Real.circleAverage (coneRefField c w) z r =
        Real.circleAverage (fun _ : ℂ => (0 : ℝ)) z r := by
      apply Real.circleAverage_congr_sphere
      intro x hx
      have hx' : ‖x - z‖ = r := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hr)
      have hxn : ‖x‖ ≤ 1 := by linarith [norm_le_insert' x z, norm_sub_rev x z]
      exact coneRefProfile_of_le hxn
    rw [heq, Real.circleAverage_const]
  unfold coneRefCircle
  rw [hzero, add_zero]

end MatedCRT.FirstPass.Derived
