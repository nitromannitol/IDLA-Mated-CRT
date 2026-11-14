import MatedCRT.Defs.Map

/-!
# Future edges and protected cell minima

A side adjacency to a later cell prevents a path from dipping below the
initial cell minimum at every intervening mesh endpoint and between them.
-/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- A later side adjacency bounds the path below by the initial cell minimum
through any intervening mesh endpoint. -/
theorem cellMin_le_of_bmAdjacent_of_between {ε : ℝ} (hε : 0 < ε)
    {X : ℝ → ℝ} (hX : Continuous X) {j n k : ℤ}
    (hnk : n < k) (hadj : bmAdjacent ε X j k) :
    ∀ u ∈ Icc (ε * j) (ε * n),
      sInf (X '' Icc (ε * j - ε) (ε * j)) ≤ X u := by
  have hnkR : (n : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast (show n + 1 ≤ k by omega)
  have hend : ε * n ≤ ε * k - ε := by nlinarith
  intro u hu
  have hu' : u ∈ Icc (ε * j) (ε * k - ε) := ⟨hu.1, hu.2.trans hend⟩
  have hmid := csInf_le (isCompact_Icc.image hX).bddBelow ⟨u, hu', rfl⟩
  exact (le_max_left _ _).trans (hadj.trans hmid)

/-- A later edge protects the initial cell minimum in at least one of the two
boundary-length coordinates through any intervening mesh endpoint. -/
theorem cellMin_le_of_bmEdgeCount_ne_zero_of_between {ε : ℝ} (hε : 0 < ε)
    {L R : ℝ → ℝ} (hL : Continuous L) (hR : Continuous R) {j n k : ℤ}
    (hjn : j ≤ n) (hnk : n < k) (hedge : bmEdgeCount ε L R j k ≠ 0) :
    (∀ u ∈ Icc (ε * j) (ε * n),
      sInf (L '' Icc (ε * j - ε) (ε * j)) ≤ L u) ∨
    (∀ u ∈ Icc (ε * j) (ε * n),
      sInf (R '' Icc (ε * j - ε) (ε * j)) ≤ R u) := by
  have hjk : j < k := lt_of_le_of_lt hjn hnk
  have hadj : bmAdjacent ε L j k ∨ bmAdjacent ε R j k := by
    by_contra h
    simp [bmEdgeCount, ne_of_lt hjk, min_eq_left hjk.le, max_eq_right hjk.le, h] at hedge
  rcases hadj with h | h
  · exact Or.inl (cellMin_le_of_bmAdjacent_of_between hε hL hnk h)
  · exact Or.inr (cellMin_le_of_bmAdjacent_of_between hε hR hnk h)

end MatedCRT
