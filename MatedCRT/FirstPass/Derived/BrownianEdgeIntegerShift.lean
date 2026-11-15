import MatedCRT.Defs.Map

/-! # Integer reindexing of boundary-length edges -/

set_option autoImplicit false

open Set

namespace MatedCRT

private theorem image_Icc_timeShift (X : ℝ → ℝ) (a b c : ℝ) :
    (fun t => X (t + c)) '' Icc a b = X '' Icc (a + c) (b + c) := by
  ext x
  constructor
  · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
    exact ⟨t + c, ⟨by linarith, by linarith⟩, rfl⟩
  · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
    refine ⟨t - c, ⟨by linarith, by linarith⟩, ?_⟩
    ring

/-- Integer translation of the time grid relabels the boundary adjacency condition. -/
theorem bmAdjacent_timeShift_int (ε : ℝ) (X : ℝ → ℝ) (m j k : ℤ) :
    bmAdjacent ε (fun t => X (t + ε * m)) j k ↔
      bmAdjacent ε X (j + m) (k + m) := by
  unfold bmAdjacent
  rw [image_Icc_timeShift, image_Icc_timeShift, image_Icc_timeShift]
  push_cast
  have h₁ (i : ℝ) : ε * i - ε + ε * m = ε * (i + m) - ε := by ring
  have h₂ (i : ℝ) : ε * i + ε * m = ε * (i + m) := by ring
  simp only [h₁, h₂]

/-- Integer translation of both boundary paths relabels the entire edge count. -/
theorem bmEdgeCount_timeShift_int (ε : ℝ) (L R : ℝ → ℝ) (m j k : ℤ) :
    bmEdgeCount ε (fun t => L (t + ε * m)) (fun t => R (t + ε * m)) j k =
      bmEdgeCount ε L R (j + m) (k + m) := by
  classical
  by_cases h : j = k
  · simp [bmEdgeCount, h]
  · simp [bmEdgeCount, h, min_add_add_right, max_add_add_right,
      bmAdjacent_timeShift_int]

end MatedCRT
