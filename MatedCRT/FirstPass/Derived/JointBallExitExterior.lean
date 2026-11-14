import MatedCRT.FirstPass.Derived.JointBallExitContinuity

/-! # Ball-exit continuity at exterior initial points -/

set_option autoImplicit false

open Filter Metric MarkovProcess Topology
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- A path beginning strictly outside a ball has locally constant zero exit time,
    jointly in the path and the radius. -/
theorem continuousAt_planarBall_exitTime_joint_of_initial_exterior
    {b : ContinuousPath ℂ} {r : ℝ} (h : r < dist (b 0) 0) :
    ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
      ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) (b, r) := by
  have hopen : IsOpen {p : ContinuousPath ℂ × ℝ | p.2 < dist (p.1 0) 0} :=
    isOpen_lt continuous_snd (((continuous_eval_const 0).comp continuous_fst).dist continuous_const)
  have hevent : ∀ᶠ p : ContinuousPath ℂ × ℝ in 𝓝 (b, r),
      ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1 = 0 := by
    filter_upwards [hopen.mem_nhds h] with p hp
    apply le_antisymm
    · simpa using ContinuousPath.exitTime_le_of_notMem (ball (0 : ℂ) p.2) p.1 0
        (by simpa only [mem_ball, not_lt] using le_of_lt hp)
    · exact zero_le
  refine (continuousAt_const : ContinuousAt
    (fun _ : ContinuousPath ℂ × ℝ => (0 : ℝ≥0∞)) (b, r)).congr ?_
  filter_upwards [hevent] with p hp
  exact hp.symm

end MatedCRT.StopAtExitCmp
