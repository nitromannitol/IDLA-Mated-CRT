import MatedCRT.FirstPass.Derived.InterpolatedWalkPrefix
import MatedCRT.FirstPass.Derived.StoppedWalkScaling

/-!
# Stopped interpolations of coupled walks

Walks that agree through a common vertex exit time have the same stopped
embedded interpolation.
-/

set_option autoImplicit false

open LatticeProb
open scoped NNReal
open MatedCRT.ExitCouplingGlue

namespace MatedCRT

/-- Agreement through a common exit time gives equal stopped interpolated paths. -/
theorem stoppedInterp_eq_of_exitTime_eq_of_prefix_eq (v : ℤ → ℂ) (m : ℝ≥0)
    (A : Set ℤ) (x y : ℕ → ℤ) (ht : vExitTime A x = vExitTime A y)
    (hp : ∀ j : ℕ, (j : ℕ∞) ≤ vExitTime A x → x j = y j) :
    stoppedInterp v m A x = stoppedInterp v m A y := by
  have hprefix : ∀ j ≤ (vExitTime A x).toNat, x j = y j := by
    intro j hj
    apply hp
    exact le_trans (by exact_mod_cast hj) (ENat.natCast_toNat_le_self _)
  by_cases hm : m = 0
  · subst m
    rw [StoppedWalkScaling.stoppedInterp_zero_speed, StoppedWalkScaling.stoppedInterp_zero_speed]
    ext t
    simp only [interpPathCM_apply, interpPathFn, NNReal.coe_zero, zero_mul]
    simp [linInterp, hprefix 0 (Nat.zero_le _)]
  · have hm' : (0 : ℝ) < m := by exact_mod_cast (pos_iff_ne_zero.mpr hm : 0 < m)
    have h := stopPath_interpPathCM_congr v hm' (vExitTime A x).toNat hprefix
    unfold stoppedInterp
    rw [← ht]
    convert h using 1 <;> congr 1 <;> ext <;>
      simp [Real.toNNReal_div, Real.toNNReal_natCast]

end MatedCRT
