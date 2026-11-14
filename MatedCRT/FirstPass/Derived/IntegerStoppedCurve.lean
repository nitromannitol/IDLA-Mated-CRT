import MatedCRT.FirstPass.Derived.ExitDecomposition
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveMeasurable

/-! # Integer walk exit times and stopped polygonal curves -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open BouRabeeGwynne
open BouRabeeGwynne.FiniteConductanceNetwork
open ExitDecomposition

/-- The two definitions give the same first exit time for an integer path. -/
theorem integer_exitTime_eq_vExitTime (A : Set ℤ) (x : ℕ → ℤ) :
    exitTime A x = vExitTime A x := by
  have hle (n : ℕ) : exitTime A x ≤ (n : ℕ∞) ↔ vExitTime A x ≤ (n : ℕ∞) :=
    (exitTime_le_iff A x n).trans (Lemma68Window.vExitTime_le_coe_iff A x n).symm
  induction he : exitTime A x using ENat.recTopCoe with
  | top =>
    symm
    apply (vExitTime_eq_top_iff).2
    exact (exitTime_eq_top_iff A x).1 he
  | coe n =>
    change exitTime A x = (n : ℕ∞) at he
    change (n : ℕ∞) = vExitTime A x
    have hv : vExitTime A x ≤ (n : ℕ∞) := (hle n).1 (by rw [he])
    apply le_antisymm
    · by_contra hn
      have hlt : vExitTime A x < (n : ℕ∞) := lt_of_not_ge hn
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      have hk' : vExitTime A x = (k : ℕ∞) := hk.symm
      have hkn : k < n := by simpa [hk'] using hlt
      have : exitTime A x ≤ (k : ℕ∞) := (hle k).2 (by rw [hk'])
      rw [he] at this
      exact (not_le_of_gt hkn) (by exact_mod_cast this)
    · simpa [he] using hv

/-- Stopping a discrete integer path preserves its stopped polygonal curve. -/
theorem stoppedPolygonalCurve_stoppedPath {d : ℕ} (pos : ℤ → Euc d)
    (A : Set ℤ) (x : ℕ → ℤ) :
    stoppedPolygonalCurve pos A (stoppedPath A x) = stoppedPolygonalCurve pos A x := by
  by_cases ht : vExitTime A x = ⊤
  · rw [stoppedPath_of_top ht]
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 ht
    have hk' : vExitTime A x = (k : ℕ∞) := hk.symm
    unfold stoppedPolygonalCurve
    rw [integer_exitTime_eq_vExitTime, integer_exitTime_eq_vExitTime,
      vExitTime_stoppedPath, hk']
    simp only [untopD_coe_enat]
    apply congrArg CurveSpace.project
    apply polygonalCurve_congr_prefix
    intro j hj
    exact stoppedPath_of_le hk' hj

end MatedCRT
