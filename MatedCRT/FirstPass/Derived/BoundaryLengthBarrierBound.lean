import MatedCRT.FirstPass.Derived.BoundaryLengthBarrier

/-!
# Boundary-length barriers bound later edges

Two dips below the respective cell minima give a common upper bound on the
positions of later vertices joined to the cell.
-/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- Separating dips in both coordinates rule out edges whose later endpoint
lies at least one mesh width beyond both dip times. -/
theorem bmEdgeCount_eq_zero_after_separating_dips {ε : ℝ} {L R : ℝ → ℝ}
    (hL : Continuous L) (hR : Continuous R) {j k : ℤ} (hjk : j < k)
    {tL tR : ℝ} (hstartL : ε * j ≤ tL) (hstartR : ε * j ≤ tR)
    (hdipL : L tL < sInf (L '' Icc (ε * j - ε) (ε * j)))
    (hdipR : R tR < sInf (R '' Icc (ε * j - ε) (ε * j)))
    (hafter : max tL tR + ε ≤ ε * k) :
    bmEdgeCount ε L R j k = 0 := by
  apply bmEdgeCount_eq_zero_of_separating_dips hL hR hjk
  · exact ⟨hstartL, by linarith [le_max_left tL tR]⟩
  · exact ⟨hstartR, by linarith [le_max_right tL tR]⟩
  · exact hdipL
  · exact hdipR

/-- Any later vertex joined to a cell lies before the common separating-dip
bound, enlarged by one mesh width. -/
theorem endpoint_lt_of_bmEdgeCount_ne_zero_of_separating_dips {ε : ℝ} {L R : ℝ → ℝ}
    (hL : Continuous L) (hR : Continuous R) {j k : ℤ} (hjk : j < k)
    {tL tR : ℝ} (hstartL : ε * j ≤ tL) (hstartR : ε * j ≤ tR)
    (hdipL : L tL < sInf (L '' Icc (ε * j - ε) (ε * j)))
    (hdipR : R tR < sInf (R '' Icc (ε * j - ε) (ε * j)))
    (hedge : bmEdgeCount ε L R j k ≠ 0) :
    ε * k < max tL tR + ε := by
  by_contra h
  exact hedge (bmEdgeCount_eq_zero_after_separating_dips hL hR hjk hstartL hstartR
    hdipL hdipR (le_of_not_gt h))

end MatedCRT
