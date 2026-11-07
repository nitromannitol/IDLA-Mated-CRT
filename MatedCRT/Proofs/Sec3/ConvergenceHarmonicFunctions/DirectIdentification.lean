import MatedCRT.Proofs.MatingOfTrees.CellContacts

/-! # Direct identifications and mated-CRT cell adjacency -/

namespace MatedCRT

open Set

/-- A direct boundary-length identification between two cell intervals
satisfies the boundary-minimum adjacency criterion. -/
theorem bmAdjacent_of_directRel {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : Continuous X) {j k : ℤ} (hjk : j < k) {s t : ℝ}
    (hs : s ∈ Icc (ε * j - ε) (ε * j))
    (ht : t ∈ Icc (ε * k - ε) (ε * k))
    (hrel : MatedCRTHarmonic.MatedCRT.DirectRel X s t) :
    bmAdjacent ε X j k := by
  have hjkR : (j : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast (show j + 1 ≤ k by omega)
  have hgap : ε * j ≤ ε * k - ε := by nlinarith
  have hleft : sInf (X '' Icc (ε * j - ε) (ε * j)) ≤ X s :=
    csInf_le (isCompact_Icc.image hX).bddBelow ⟨s, hs, rfl⟩
  have hright : sInf (X '' Icc (ε * k - ε) (ε * k)) ≤ X s := by
    rw [hrel.2.1]
    exact csInf_le (isCompact_Icc.image hX).bddBelow ⟨t, ht, rfl⟩
  have hmid : X s ≤ sInf (X '' Icc (ε * j) (ε * k - ε)) := by
    apply le_csInf ((nonempty_Icc.mpr hgap).image X)
    rintro _ ⟨u, hu, rfl⟩
    have hsu : s ≤ u := hs.2.trans hu.1
    have hut : u ≤ t := hu.2.trans ht.1
    rcases hsu.eq_or_lt with rfl | hsu
    · exact le_rfl
    rcases hut.eq_or_lt with rfl | hut
    · exact hrel.2.1.le
    · exact (hrel.2.2 u ⟨hsu, hut⟩).le
  exact (max_le hleft hright).trans hmid

/-- A direct identification by either boundary-length coordinate joins the
two ordered cells by an edge of the mated-CRT map. -/
theorem bmEdgeCount_ne_zero_of_directRel {ε : ℝ} (hε : 0 < ε)
    {L R : ℝ → ℝ} (hL : Continuous L) (hR : Continuous R)
    {j k : ℤ} (hjk : j < k) {s t : ℝ}
    (hs : s ∈ Icc (ε * j - ε) (ε * j))
    (ht : t ∈ Icc (ε * k - ε) (ε * k))
    (hrel : MatedCRTHarmonic.MatedCRT.DirectRel L s t ∨
      MatedCRTHarmonic.MatedCRT.DirectRel R s t) :
    bmEdgeCount ε L R j k ≠ 0 := by
  have hadj : bmAdjacent ε L j k ∨ bmAdjacent ε R j k := by
    rcases hrel with h | h
    · exact Or.inl (bmAdjacent_of_directRel hε hL hjk hs ht h)
    · exact Or.inr (bmAdjacent_of_directRel hε hR hjk hs ht h)
  simp only [bmEdgeCount, ne_of_lt hjk, ↓reduceIte,
    min_eq_left hjk.le, max_eq_right hjk.le, hadj]
  split_ifs <;> decide

end MatedCRT
