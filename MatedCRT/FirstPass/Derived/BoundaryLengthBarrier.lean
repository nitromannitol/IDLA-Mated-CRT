import MatedCRT.Defs.Map

/-!
# Separating dips for mated-CRT edges

A strict dip in each boundary-length coordinate between two cells excludes an
edge between them.
-/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- A strict dip below the first cell infimum excludes the side condition. -/
theorem not_bmAdjacent_of_separating_dip {ε : ℝ} {X : ℝ → ℝ}
    (hX : Continuous X) {j k : ℤ} {t : ℝ}
    (ht : t ∈ Icc (ε * j) (ε * k - ε))
    (hdip : X t < sInf (X '' Icc (ε * j - ε) (ε * j))) :
    ¬ bmAdjacent ε X j k := by
  intro h
  have hmid : sInf (X '' Icc (ε * j) (ε * k - ε)) ≤ X t :=
    csInf_le (isCompact_Icc.bddBelow_image hX.continuousOn) ⟨t, ht, rfl⟩
  have hcell := (le_max_left _ _).trans h
  exact (not_lt_of_ge (hcell.trans hmid)) hdip

/-- Two separating dips exclude an edge in either coordinate. -/
theorem bmEdgeCount_eq_zero_of_separating_dips {ε : ℝ} {L R : ℝ → ℝ}
    (hL : Continuous L) (hR : Continuous R) {j k : ℤ} (hjk : j < k)
    {tL tR : ℝ}
    (htL : tL ∈ Icc (ε * j) (ε * k - ε))
    (htR : tR ∈ Icc (ε * j) (ε * k - ε))
    (hdipL : L tL < sInf (L '' Icc (ε * j - ε) (ε * j)))
    (hdipR : R tR < sInf (R '' Icc (ε * j - ε) (ε * j))) :
    bmEdgeCount ε L R j k = 0 := by
  have hL' := not_bmAdjacent_of_separating_dip hL htL hdipL
  have hR' := not_bmAdjacent_of_separating_dip hR htR hdipR
  simp [bmEdgeCount, ne_of_lt hjk, min_eq_left hjk.le, max_eq_right hjk.le, hL', hR']

end MatedCRT
