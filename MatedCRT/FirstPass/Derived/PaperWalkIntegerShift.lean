import MatedCRT.Defs.Setting

/-! # Integer reindexing of embedded walks -/

set_option autoImplicit false

open scoped NNReal

namespace MatedCRT

/-- An integer time-grid translation relabels the embedded vertices. -/
theorem vertexPoint_timeShift_int (ε : ℝ) (η : ℝ → ℂ) (m k : ℤ) :
    vertexPoint ε (fun t => η (t + ε * m)) k = vertexPoint ε η (k + m) := by
  unfold vertexPoint
  push_cast
  ring

/-- Translating the time grid and relabeling the integer walk give the same
interpolated embedded path. -/
theorem interpolatedWalk_timeShift_int (ε : ℝ) (η : ℝ → ℂ) (m : ℤ)
    (speed : ℝ) (x : ℕ → ℤ) (t : ℝ≥0) :
    interpolatedWalk ε (fun s => η (s + ε * m)) speed x t =
      interpolatedWalk ε η speed (fun n => x n + m) t := by
  unfold interpolatedWalk
  simp only [vertexPoint_timeShift_int]

end MatedCRT
