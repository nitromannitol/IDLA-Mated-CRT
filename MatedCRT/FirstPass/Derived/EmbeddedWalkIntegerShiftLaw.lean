import MatedCRT.FirstPass.Derived.SrwRelabelLaw
import MatedCRT.FirstPass.Derived.PaperWalkIntegerShift
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkExitMeasurable

/-! # Integer time-grid shifts of embedded walk laws -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- The interpolated embedded path is measurable in the integer walk for the
product measurable structure on paths. -/
theorem measurable_interpolatedWalk_path (ε : ℝ) (η : ℝ → ℂ) (speed : ℝ) :
    Measurable (fun x : ℕ → ℤ => interpolatedWalk ε η speed x) :=
  Measurable.of_eval fun t => measurable_interpolatedWalk_apply ε η speed t

/-- Integer time-grid translation preserves the law of the embedded walk,
when the boundary paths, curve, and starting label are translated together. -/
theorem interpolatedWalkLaw_bmEdgeCount_timeShift_int
    (ε : ℝ) (η : ℝ → ℂ) (L R : ℝ → ℝ) (k a : ℤ) (speed : ℝ) :
    (srwLaw (bmEdgeCount ε (fun t => L (t + ε * k))
      (fun t => R (t + ε * k))) a).map
        (fun x => interpolatedWalk ε (fun t => η (t + ε * k)) speed x) =
    (srwLaw (bmEdgeCount ε L R) (a + k)).map (interpolatedWalk ε η speed) := by
  have hshift : Measurable (fun x : ℕ → ℤ => fun n => x n + k) :=
    Measurable.of_eval fun n => (measurable_pi_apply n).add measurable_const
  have hpath := measurable_interpolatedWalk_path ε η speed
  rw [← srwLaw_bmEdgeCount_timeShift_int ε L R k a, Measure.map_map hpath hshift]
  congr 1
  funext x t
  exact interpolatedWalk_timeShift_int ε η k speed x t

end MatedCRT
