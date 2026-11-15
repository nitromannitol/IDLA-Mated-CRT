import MatedCRT.Defs.Map

/-! # Integer reindexing of cells -/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- Translating a curve by an integer number of mesh intervals relabels its cells. -/
theorem cell_timeShift_int (ε : ℝ) (η : ℝ → ℂ) (m k : ℤ) :
    cell ε (fun t => η (t + ε * m)) k = cell ε η (k + m) := by
  have hleft : ε * ((k + m : ℤ) - 1) = ε * (k - 1) + ε * m := by
    push_cast
    ring
  have hright : ε * ((k + m : ℤ) : ℝ) = ε * k + ε * m := by
    push_cast
    ring
  ext z
  constructor
  · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
    refine ⟨t + ε * m, ⟨?_, ?_⟩, rfl⟩
    · rw [hleft]; linarith
    · rw [hright]; linarith
  · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
    refine ⟨t - ε * m, ⟨?_, ?_⟩, ?_⟩
    · rw [hleft] at ht₁; linarith
    · rw [hright] at ht₂; linarith
    · ring

/-- Integer translation of the time grid preserves the cell intersection multiplicity
with both vertices relabeled. -/
theorem cellMult_timeShift_int (ε : ℝ) (η : ℝ → ℂ) (m j k : ℤ) :
    cellMult ε (fun t => η (t + ε * m)) j k = cellMult ε η (j + m) (k + m) := by
  classical
  by_cases h : j = k
  · simp [cellMult, h]
  · simp [cellMult, h, cell_timeShift_int]

end MatedCRT
