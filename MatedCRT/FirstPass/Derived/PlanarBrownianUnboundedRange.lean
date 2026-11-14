import MatedCRT.FirstPass.Derived.PlanarBrownianBoundedExit

/-! # Unbounded range of planar Brownian paths -/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal

namespace MatedCRT

/-- A path has unbounded range exactly when it exits every natural-radius
ball about the origin in finite time. -/
theorem unbounded_range_iff_exit_all_origin_balls (b : ContinuousPath ℂ) :
    (¬ Bornology.IsBounded (Set.range b)) ↔
      ∀ n : ℕ, ContinuousPath.exitTime (ball (0 : ℂ) (n : ℝ)) b < ⊤ := by
  constructor
  · intro hunbounded n
    rw [ContinuousPath.exitTime_lt_top_iff]
    by_contra h
    push Not at h
    apply hunbounded
    exact isBounded_ball.subset (by rintro _ ⟨t, rfl⟩; exact h t)
  · intro hexits hbounded
    obtain ⟨r, hr⟩ := hbounded.subset_ball (0 : ℂ)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    obtain ⟨t, ht⟩ := (ContinuousPath.exitTime_lt_top_iff _ _).mp (hexits n)
    exact ht ((ball_subset_ball (le_of_lt hn)) (hr ⟨t, rfl⟩))

/-- Continuous paths of unbounded range form a measurable set. -/
theorem measurableSet_planarPath_unbounded_range :
    MeasurableSet {b : ContinuousPath ℂ | ¬ Bornology.IsBounded (Set.range b)} := by
  have heq : {b : ContinuousPath ℂ | ¬ Bornology.IsBounded (Set.range b)} =
      ⋂ n : ℕ, {b : ContinuousPath ℂ |
        ContinuousPath.exitTime (ball (0 : ℂ) (n : ℝ)) b < ⊤} := by
    ext b
    simp only [mem_ofPred_eq, mem_iInter, unbounded_range_iff_exit_all_origin_balls]
  rw [heq]
  exact MeasurableSet.iInter fun n =>
    measurableSet_lt (ContinuousPath.measurable_exitTime _ isOpen_ball) measurable_const

/-- Planar Brownian motion has unbounded range almost surely from every start. -/
theorem ae_planarBrownianMotion_unbounded_range (y : ℂ) :
    ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion y,
      ¬ Bornology.IsBounded (Set.range b) := by
  filter_upwards [ae_planarBrownianMotion_exit_all_balls y] with b hb
  exact (unbounded_range_iff_exit_all_origin_balls b).mpr (fun n => hb 0 n)

end MatedCRT
