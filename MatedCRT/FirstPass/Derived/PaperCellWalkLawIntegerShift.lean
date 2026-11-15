import MatedCRT.FirstPass.Derived.PaperCellIntegerShift
import MatedCRT.FirstPass.Derived.EmbeddedWalkIntegerShiftLaw

/-! # Integer translations of embedded cell walk laws -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- Translating the curve by an integer number of mesh intervals relabels the
cell walk without changing its embedded path law. -/
theorem interpolatedCellWalkLaw_timeShift_int
    (ε : ℝ) (η : ℝ → ℂ) (k a : ℤ) (speed : ℝ) :
    (srwLaw (cellMult ε (fun t => η (t + ε * k))) a).map
        (interpolatedWalk ε (fun t => η (t + ε * k)) speed) =
      (srwLaw (cellMult ε η) (a + k)).map (interpolatedWalk ε η speed) := by
  let e : ℤ ≃ ℤ := Equiv.addRight k
  have hmult : cellMult ε (fun t => η (t + ε * k)) =
      fun x y => cellMult ε η (e x) (e y) := by
    funext x y
    exact cellMult_timeShift_int ε η k x y
  have hlaw : (srwLaw (cellMult ε (fun t => η (t + ε * k))) a).map
      (fun x n => x n + k) = srwLaw (cellMult ε η) (a + k) := by
    rw [hmult]
    exact srwLaw_map_relabel (cellMult ε η) e a
  have hshift : Measurable (fun x : ℕ → ℤ => fun n => x n + k) :=
    Measurable.of_eval fun n => (measurable_pi_apply n).add measurable_const
  have hpath := measurable_interpolatedWalk_path ε η speed
  rw [← hlaw, Measure.map_map hpath hshift]
  congr 1
  funext x t
  exact interpolatedWalk_timeShift_int ε η k speed x t

end MatedCRT
