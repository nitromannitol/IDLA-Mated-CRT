import MatedCRT.Defs.Map

/-!
# First crossings and mated-CRT edges

A cell that reaches the minimum of an earlier cell, before the path dips below
that minimum between the cells, is adjacent to the earlier cell.
-/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- A later cell reaching the earlier cell minimum forms a side adjacency if
the path between the cells stays above that minimum. -/
theorem bmAdjacent_of_first_crossing {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : Continuous X) {j k : ℤ} (hjk : j < k) {t : ℝ}
    (ht : t ∈ Icc (ε * k - ε) (ε * k))
    (hcross : X t ≤ sInf (X '' Icc (ε * j - ε) (ε * j)))
    (hbefore : ∀ u ∈ Icc (ε * j) (ε * k - ε),
      sInf (X '' Icc (ε * j - ε) (ε * j)) ≤ X u) :
    bmAdjacent ε X j k := by
  have hjkR : (j : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast (show j + 1 ≤ k by omega)
  have hgap : ε * j ≤ ε * k - ε := by nlinarith
  have hmid : sInf (X '' Icc (ε * j - ε) (ε * j)) ≤
      sInf (X '' Icc (ε * j) (ε * k - ε)) := by
    apply le_csInf ((nonempty_Icc.mpr hgap).image X)
    rintro _ ⟨u, hu, rfl⟩
    exact hbefore u hu
  have hright : sInf (X '' Icc (ε * k - ε) (ε * k)) ≤
      sInf (X '' Icc (ε * j - ε) (ε * j)) :=
    (csInf_le (isCompact_Icc.image hX).bddBelow ⟨t, ht, rfl⟩).trans hcross
  exact max_le hmid (hright.trans hmid)

/-- A side adjacency in either coordinate gives a nonzero edge multiplicity. -/
theorem bmEdgeCount_ne_zero_of_side_adjacent {ε : ℝ}
    {L R : ℝ → ℝ} {j k : ℤ} (hjk : j < k)
    (h : bmAdjacent ε L j k ∨ bmAdjacent ε R j k) :
    bmEdgeCount ε L R j k ≠ 0 := by
  simp only [bmEdgeCount, ne_of_lt hjk, ↓reduceIte,
    min_eq_left hjk.le, max_eq_right hjk.le, h]
  split_ifs <;> decide

end MatedCRT
