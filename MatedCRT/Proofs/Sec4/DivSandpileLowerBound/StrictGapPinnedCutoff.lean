import HarmonicBalls.Proofs.Sec8.LocalSmoothShiftCutoff

/-! # Pinned smooth shifts on an interior disc -/

noncomputable section
open Set Metric HarmonicBalls
open scoped ContDiff

namespace MatedCRT

/-- A constant on a disc of radius less than one extends to a compactly
supported smooth shift with zero average on the unit circle. -/
theorem exists_pinned_smooth_shift {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (c : ℝ) :
    ∃ g : ℂ → ℝ, IsTestFunction univ g ∧
      Real.circleAverage g 0 1 = 0 ∧ ∀ z ∈ ball 0 r, g z = c := by
  let R := (r + 1) / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  obtain ⟨g, hg, hgc⟩ := exists_testFunction_eqOn_closedBall_of_contDiffOn_ball
    (c := (0 : ℂ)) hr hrR (g := fun _ => c) contDiffOn_const
  refine ⟨g, ⟨hg.1, hg.2.1, subset_univ _⟩, ?_, fun z hz => hgc (ball_subset_closedBall hz)⟩
  rw [Real.circleAverage_congr_sphere (f₂ := fun _ => (0 : ℝ)), Real.circleAverage_const]
  intro z hz
  have hzout : z ∉ ball (0 : ℂ) R := by
    have hzdist : dist z (0 : ℂ) = 1 := by simpa [mem_sphere] using hz
    simp [mem_ball, hzdist, not_lt.mpr hR1.le]
  exact image_eq_zero_of_notMem_tsupport (fun hs => hzout (hg.2.2 hs))

end MatedCRT
