import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartSphereOrder
import MatedCRT.Defs.Setting

/-! # Interpolation after restarting a walk -/

namespace MatedCRT

open scoped NNReal

/-- Shifting the discrete walk by `k` steps shifts its linearly interpolated
path by the corresponding amount of rescaled time. -/
theorem interpolatedWalk_pathShift
    {ε mε : ℝ} (hm : 0 < mε) (η : ℝ → ℂ) (x : ℕ → ℤ)
    (k : ℕ) (t : ℝ≥0) :
    interpolatedWalk ε η mε (pathShift k x) t =
      interpolatedWalk ε η mε x (t + (k / mε).toNNReal) := by
  have hnonneg : 0 ≤ mε * (t : ℝ) := mul_nonneg hm.le t.2
  have htime : mε * ((t + ((k : ℝ) / mε).toNNReal : ℝ≥0) : ℝ) =
      mε * (t : ℝ) + k := by
    rw [NNReal.coe_add, Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hm.le)]
    field_simp
  unfold interpolatedWalk
  dsimp only
  rw [htime, Nat.floor_add_natCast hnonneg]
  simp only [pathShift, Nat.cast_add]
  congr 2
  all_goals push_cast; ring

end MatedCRT

#print axioms MatedCRT.interpolatedWalk_pathShift
