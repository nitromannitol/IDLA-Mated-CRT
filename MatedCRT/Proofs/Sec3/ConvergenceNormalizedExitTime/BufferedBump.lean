import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.RescaledGreenBump
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Buffered bump functions for the near-pole comparison -/

namespace MatedCRT

open Set Metric

/-- A smooth bump for the near-pole comparison: it equals one on the
twice-enlarged ball and vanishes outside the four-times-enlarged ball. It is
globally Hölder continuous, as required by the discrete Dirichlet theorem. -/
theorem exists_buffered_holder_bump (y : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ φ : ℂ → ℝ,
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ ball y (2 * δ), φ x = 1) ∧
      (∀ x ∉ ball y (4 * δ), φ x = 0) ∧
      ∀ s : Set ℂ, IsHolderContinuousOn φ s := by
  let f : ContDiffBump y := ⟨2 * δ, 4 * δ, by linarith, by linarith⟩
  have hf : ∃ C, LipschitzWith C (f : ℂ → ℝ) :=
    ContDiff.lipschitzWith_of_hasCompactSupport f.hasCompactSupport
      (f.contDiff : ContDiff ℝ 1 f) (by norm_num)
  obtain ⟨C, hC⟩ := hf
  refine ⟨f, fun x => ⟨f.nonneg, f.le_one⟩, ?_, ?_, ?_⟩
  · intro x hx
    exact f.one_of_mem_closedBall (ball_subset_closedBall hx)
  · intro x hx
    exact f.zero_of_le_dist (not_lt.mp hx)
  · intro s
    exact ⟨C, 1, zero_lt_one, le_rfl, hC.holderWith.holderOnWith s⟩

end MatedCRT
