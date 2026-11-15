import MatedCRT.Defs.Map
import LatticeProb.Topology.CompactCurveRange
import LatticeProb.LQG.ShiftedGridWalkAnchors

/-! # Grid-shifted cells and time-translated curves -/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- A shifted compact cell is the paper cell of the time-translated curve. -/
theorem shiftedCompactCell_eq_cell_timeShift (η : C(ℝ, ℂ)) {ε : ℝ}
    (hε : 0 ≤ ε) (θ : ℝ) (k : ℤ) :
    (LatticeProb.shiftedCompactCell η ε θ k : Set ℂ) =
      cell ε (fun t => η (t + ε * θ)) k := by
  rw [LatticeProb.coe_shiftedCompactCell]
  have hle : ε * ((k : ℝ) - 1 + θ) ≤ ε * ((k : ℝ) + θ) := by
    apply mul_le_mul_of_nonneg_left _ hε
    linarith
  rw [uIcc_of_le hle]
  unfold cell
  ext z
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
    refine ⟨t - ε * θ, ⟨?_, ?_⟩, ?_⟩
    · nlinarith
    · nlinarith
    · congr 1
      ring
  · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
    refine ⟨t + ε * θ, ⟨?_, ?_⟩, rfl⟩ <;> nlinarith

/-- The shifted anchor is the paper vertex of the time-translated curve. -/
theorem shiftedGridAnchor_eq_vertexPoint_timeShift (η : C(ℝ, ℂ))
    (ε θ : ℝ) (k : ℤ) :
    LatticeProb.shiftedGridAnchor η ε θ k =
      vertexPoint ε (fun t => η (t + ε * θ)) k := by
  unfold LatticeProb.shiftedGridAnchor vertexPoint
  congr 1
  ring

end MatedCRT
