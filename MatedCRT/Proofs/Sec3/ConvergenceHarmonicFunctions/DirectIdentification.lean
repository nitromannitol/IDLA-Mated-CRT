import MatedCRT.Proofs.MatingOfTrees.CellContacts
import MatedCRT.Proofs.Infra.MatingOfTrees

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

/-- The mesh interval indexed by the ceiling contains its time. -/
theorem mem_mesh_interval_ceil {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    t ∈ Icc (ε * (⌈t / ε⌉ : ℤ) - ε) (ε * (⌈t / ε⌉ : ℤ)) := by
  constructor
  · have h := Int.ceil_lt_add_one (t / ε)
    have h' : ((⌈t / ε⌉ : ℤ) : ℝ) - 1 < t / ε := by linarith
    have := (lt_div_iff₀ hε).1 h'
    nlinarith
  · have := (div_le_iff₀ hε).1 (Int.le_ceil (t / ε))
    nlinarith

/-- A time in a closed mesh interval has either its own cell label or the
preceding label as its ceiling label. -/
theorem ceil_eq_or_pred_of_mem_mesh_interval {ε : ℝ} (hε : 0 < ε)
    {t : ℝ} {k : ℤ} (ht : t ∈ Icc (ε * k - ε) (ε * k)) :
    (⌈t / ε⌉ : ℤ) = k ∨ ⌈t / ε⌉ + 1 = k := by
  have hu : (⌈t / ε⌉ : ℤ) ≤ k := by
    apply Int.ceil_le.mpr
    apply (div_le_iff₀ hε).2
    nlinarith [ht.2]
  have hl : k ≤ (⌈t / ε⌉ : ℤ) + 1 := by
    have ht' : (k : ℝ) - 1 ≤ t / ε := by
      apply (le_div_iff₀ hε).2
      nlinarith [ht.1]
    have hc := Int.le_ceil (t / ε)
    have : (k : ℝ) ≤ (⌈t / ε⌉ : ℤ) + 1 := by linarith
    exact_mod_cast this
  omega

/-- A cell is equal or adjacent to the ceiling label of each time in its
closed mesh interval, including a time on the left endpoint. -/
theorem cell_eq_or_adj_ceil_of_mem {ε : ℝ} (hε : 0 < ε)
    {L R : ℝ → ℝ} (hL : Continuous L) {t : ℝ} {k : ℤ}
    (ht : t ∈ Icc (ε * k - ε) (ε * k)) :
    k = ⌈t / ε⌉ ∨ (adjGraph (bmEdgeCount ε L R)).Adj k ⌈t / ε⌉ := by
  rcases ceil_eq_or_pred_of_mem_mesh_interval hε ht with heq | heq
  · exact Or.inl heq.symm
  · right
    have hadj : (adjGraph (bmEdgeCount ε L R)).Adj ⌈t / ε⌉ k := by
      change (SimpleGraph.fromRel (fun a b => bmEdgeCount ε L R a b ≠ 0)).Adj _ _
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ?_⟩
      · omega
      · rw [← heq]
        exact bmEdgeCount_succ_ne_zero hε.le hL R _
    exact hadj.symm

/-- Directly identified times have equal or adjacent mesh labels. -/
theorem ceil_eq_or_adj_of_directRel {ε : ℝ} (hε : 0 < ε)
    {L R : ℝ → ℝ} (hL : Continuous L) (hR : Continuous R) {s t : ℝ}
    (hrel : MatedCRTHarmonic.MatedCRT.DirectRel L s t ∨
      MatedCRTHarmonic.MatedCRT.DirectRel R s t) :
    ⌈s / ε⌉ = ⌈t / ε⌉ ∨
      (adjGraph (bmEdgeCount ε L R)).Adj ⌈s / ε⌉ ⌈t / ε⌉ := by
  have hst : s < t := hrel.elim (fun h => h.1) (fun h => h.1)
  have hle : (⌈s / ε⌉ : ℤ) ≤ ⌈t / ε⌉ :=
    Int.ceil_mono (div_le_div_of_nonneg_right hst.le hε.le)
  rcases hle.eq_or_lt with heq | hlt
  · exact Or.inl heq
  · right
    change (SimpleGraph.fromRel (fun a b => bmEdgeCount ε L R a b ≠ 0)).Adj _ _
    rw [SimpleGraph.fromRel_adj]
    exact ⟨ne_of_lt hlt, Or.inl (bmEdgeCount_ne_zero_of_directRel hε hL hR hlt
      (mem_mesh_interval_ceil hε s) (mem_mesh_interval_ceil hε t) hrel)⟩

/-- The equivalence relation generated by direct identifications remains in
one fibre of a curve obeying the merge rule. -/
theorem curve_eq_of_directRel_eqvGen {L R : ℝ → ℝ} {η : ℝ → ℂ}
    (hmerge : ∀ s t, (MatedCRTHarmonic.MatedCRT.DirectRel L s t ∨
      MatedCRTHarmonic.MatedCRT.DirectRel R s t) → η s = η t)
    {s t : ℝ} (h : Relation.EqvGen (fun a b =>
      MatedCRTHarmonic.MatedCRT.DirectRel L a b ∨
      MatedCRTHarmonic.MatedCRT.DirectRel R a b) s t) : η s = η t := by
  induction h with
  | rel a b hab => exact hmerge a b hab
  | refl a => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ => exact ih₁.trans ih₂

/-- The mesh labels of equivalent times are connected inside any set that
contains the labels of all times in their common curve fibre. -/
theorem reachable_ceil_of_directRel_eqvGen {ε : ℝ} (hε : 0 < ε)
    {L R : ℝ → ℝ} (hL : Continuous L) (hR : Continuous R) {η : ℝ → ℂ}
    (hmerge : ∀ s t, (MatedCRTHarmonic.MatedCRT.DirectRel L s t ∨
      MatedCRTHarmonic.MatedCRT.DirectRel R s t) → η s = η t)
    (q : ℂ) (U : Set ℤ) (hsafe : ∀ t, η t = q → (⌈t / ε⌉ : ℤ) ∈ U)
    {s t : ℝ} (h : Relation.EqvGen (fun a b =>
      MatedCRTHarmonic.MatedCRT.DirectRel L a b ∨
      MatedCRTHarmonic.MatedCRT.DirectRel R a b) s t)
    (hs : η s = q) (ht : η t = q) :
    ((adjGraph (bmEdgeCount ε L R)).induce U).Reachable
      ⟨⌈s / ε⌉, hsafe s hs⟩ ⟨⌈t / ε⌉, hsafe t ht⟩ := by
  induction h with
  | rel a b hab =>
    rcases ceil_eq_or_adj_of_directRel hε hL hR hab with heq | hadj
    · have : (⟨⌈a / ε⌉, hsafe a hs⟩ : U) = ⟨⌈b / ε⌉, hsafe b ht⟩ := Subtype.ext heq
      rw [this]
    · exact SimpleGraph.Adj.reachable hadj
  | refl a => exact SimpleGraph.Reachable.refl _
  | symm a b hab ih => exact (ih ht hs).symm
  | trans a b c hab hbc ih₁ ih₂ =>
    have hb : η b = q := (curve_eq_of_directRel_eqvGen hmerge hab).symm.trans hs
    exact (ih₁ hs hb).trans (ih₂ hb ht)

/-- Cells containing equivalent times are connected in a set that contains
the cells and all ceiling labels in their common curve fibre. -/
theorem reachable_cells_of_directRel_eqvGen {ε : ℝ} (hε : 0 < ε)
    {L R : ℝ → ℝ} (hL : Continuous L) (hR : Continuous R) {η : ℝ → ℂ}
    (hmerge : ∀ s t, (MatedCRTHarmonic.MatedCRT.DirectRel L s t ∨
      MatedCRTHarmonic.MatedCRT.DirectRel R s t) → η s = η t)
    (q : ℂ) (U : Set ℤ) (hsafe : ∀ t, η t = q → (⌈t / ε⌉ : ℤ) ∈ U)
    {s t : ℝ} {j k : ℤ} (hj : j ∈ U) (hk : k ∈ U)
    (hsj : s ∈ Icc (ε * j - ε) (ε * j))
    (htk : t ∈ Icc (ε * k - ε) (ε * k))
    (h : Relation.EqvGen (fun a b =>
      MatedCRTHarmonic.MatedCRT.DirectRel L a b ∨
      MatedCRTHarmonic.MatedCRT.DirectRel R a b) s t)
    (hs : η s = q) (ht : η t = q) :
    ((adjGraph (bmEdgeCount ε L R)).induce U).Reachable ⟨j, hj⟩ ⟨k, hk⟩ := by
  have hleft : ((adjGraph (bmEdgeCount ε L R)).induce U).Reachable
      ⟨j, hj⟩ ⟨⌈s / ε⌉, hsafe s hs⟩ := by
    rcases cell_eq_or_adj_ceil_of_mem hε hL hsj with heq | hadj
    · have heq' : (⟨j, hj⟩ : U) = ⟨⌈s / ε⌉, hsafe s hs⟩ := Subtype.ext heq
      rw [heq']
    · exact SimpleGraph.Adj.reachable hadj
  have hright : ((adjGraph (bmEdgeCount ε L R)).induce U).Reachable
      ⟨k, hk⟩ ⟨⌈t / ε⌉, hsafe t ht⟩ := by
    rcases cell_eq_or_adj_ceil_of_mem hε hL htk with heq | hadj
    · have heq' : (⟨k, hk⟩ : U) = ⟨⌈t / ε⌉, hsafe t ht⟩ := Subtype.ext heq
      rw [heq']
    · exact SimpleGraph.Adj.reachable hadj
  exact (hleft.trans (reachable_ceil_of_directRel_eqvGen hε hL hR hmerge
    q U hsafe h hs ht)).trans hright.symm

end MatedCRT
