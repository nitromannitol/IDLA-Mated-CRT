import MatedCRT.FirstPass.Derived.ShiftedPaperCell

/-! # Multiplicities of shifted cells -/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- The shifted-cell intersection multiplicity agrees with the paper
multiplicity of the translated curve. -/
theorem shifted_cell_component_count_eq_cellMult_timeShift
    (η : C(ℝ, ℂ)) {ε : ℝ} (hε : 0 ≤ ε) (θ : ℝ) (j k : ℤ) :
    (if j = k then 0 else
      {C ∈ HarmonicBalls.connectedComponentsIn
        ((LatticeProb.shiftedCompactCell η ε θ j : Set ℂ) ∩
          (LatticeProb.shiftedCompactCell η ε θ k : Set ℂ)) |
          ¬ C.Subsingleton}.ncard) =
      cellMult ε (fun t => η (t + ε * θ)) j k := by
  rw [shiftedCompactCell_eq_cell_timeShift η hε θ j,
    shiftedCompactCell_eq_cell_timeShift η hε θ k]
  rfl

end MatedCRT
