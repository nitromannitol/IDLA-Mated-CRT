import MatedCRT.Defs.Map

/-!
# Locality of mated-CRT edge multiplicities

Edges whose endpoints are before a separating time depend only on the two
boundary-length paths up to that time.
-/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- The adjacency condition uses only the path up to the endpoints of the two cells. -/
theorem bmAdjacent_iff_of_eqOn_past {ε s : ℝ} (hε : 0 ≤ ε)
    {X Y : ℝ → ℝ} (hXY : ∀ t ≤ s, X t = Y t) {j k : ℤ}
    (hj : ε * (j : ℝ) ≤ s) (hk : ε * (k : ℝ) ≤ s) :
    bmAdjacent ε X j k ↔ bmAdjacent ε Y j k := by
  have h₁ : X '' Icc (ε * j - ε) (ε * j) = Y '' Icc (ε * j - ε) (ε * j) :=
    Set.image_congr fun t ht => hXY t (ht.2.trans hj)
  have h₂ : X '' Icc (ε * k - ε) (ε * k) = Y '' Icc (ε * k - ε) (ε * k) :=
    Set.image_congr fun t ht => hXY t (ht.2.trans hk)
  have h₃ : X '' Icc (ε * j) (ε * k - ε) = Y '' Icc (ε * j) (ε * k - ε) :=
    Set.image_congr fun t ht => hXY t (ht.2.trans (by linarith))
  simp only [bmAdjacent, h₁, h₂, h₃]

/-- The edge multiplicity between vertices before a time is determined by the paths up to that time. -/
theorem bmEdgeCount_eq_of_eqOn_past {ε s : ℝ} (hε : 0 ≤ ε)
    {L R L' R' : ℝ → ℝ} (hL : ∀ t ≤ s, L t = L' t)
    (hR : ∀ t ≤ s, R t = R' t) {j k : ℤ}
    (hmax : ε * ((max j k : ℤ) : ℝ) ≤ s) :
    bmEdgeCount ε L R j k = bmEdgeCount ε L' R' j k := by
  have hmin : ε * ((min j k : ℤ) : ℝ) ≤ s := by
    apply le_trans (mul_le_mul_of_nonneg_left ?_ hε) hmax
    exact_mod_cast (min_le_max : min j k ≤ max j k)
  have hL' := bmAdjacent_iff_of_eqOn_past hε hL (j := min j k) (k := max j k) hmin hmax
  have hR' := bmAdjacent_iff_of_eqOn_past hε hR (j := min j k) (k := max j k) hmin hmax
  classical
  by_cases hjk : j = k <;> simp [bmEdgeCount, hjk, hL', hR']

end MatedCRT
