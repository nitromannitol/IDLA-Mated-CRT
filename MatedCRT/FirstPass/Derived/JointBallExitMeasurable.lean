import MarkovProcess.Path.ExitTimeShift
import Mathlib.Topology.Maps.Proper.Basic

/-! # Joint measurability of ball exit times -/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

/-- The finite-time sublevel of the exit time is closed jointly in the path and radius. -/
theorem isClosed_planarBall_exitTime_le (t : ℝ≥0) :
    IsClosed {p : ContinuousPath ℂ × ℝ |
      ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1 ≤ (t : ℝ≥0∞)} := by
  have hcompact : IsCompact (Set.Iic t : Set ℝ≥0) := by
    have heq : Set.Iic t = Set.Icc 0 t := by
      ext u
      simp only [Set.mem_Iic, Set.mem_Icc, zero_le, true_and]
    rw [heq]
    exact isCompact_Icc
  let : CompactSpace (Set.Iic t) := isCompact_iff_compactSpace.mp hcompact
  let E : Set ((ContinuousPath ℂ × ℝ) × Set.Iic t) :=
    {p | p.1.2 ≤ dist (p.1.1 p.2) 0}
  have heval : Continuous (fun p : (ContinuousPath ℂ × ℝ) × Set.Iic t =>
      p.1.1 p.2) := by
    exact (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have hclosed : IsClosed E :=
    isClosed_le (continuous_snd.comp continuous_fst) (heval.dist continuous_const)
  have hproj := isClosedMap_fst_of_compactSpace E hclosed
  convert hproj using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right]
  rw [ContinuousPath.exitTime_le_iff_mem_hitsSetBy _ isOpen_ball]
  simp only [ContinuousPath.hitsSetBy, Set.mem_ofPred_eq, Set.mem_compl_iff,
    Metric.mem_ball, not_lt]
  rfl

/-- The exit time from an origin ball is Borel in the continuous path and radius. -/
theorem measurable_planarBall_exitTime_joint :
    Measurable (fun p : ContinuousPath ℂ × ℝ =>
      ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) := by
  apply measurable_of_Iic
  intro a
  by_cases ha : a = ⊤
  · subst a
    simp only [Set.preimage, Set.mem_Iic, le_top, ofPred_true]
    exact MeasurableSet.univ
  · rw [← ENNReal.coe_toNNReal ha]
    exact (isClosed_planarBall_exitTime_le a.toNNReal).measurableSet

end MatedCRT
