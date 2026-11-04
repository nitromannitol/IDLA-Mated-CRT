import MatedCRT.Steps.Infra.MatingOfTrees
import MatedCRT.Proofs.Infra.MatingOfTrees

/-!
# Consecutive cells of the mated-CRT embedding

Adapted from Leonardo Bonanno's lean-formalizations, source modules
`MatedCRTHarmonic.MoTInput.CellAdjacency` and `MatedCRTHarmonic.RouteM.PsiBundle`
at commit `31e7483`.

Consecutive cells meet at the common time endpoint. This part is deterministic and holds
simultaneously for all nonnegative mesh sizes.
-/

namespace MatedCRT

open Set Filter Topology

/-- If distinct local minima have distinct values, the direct merge rule identifies the
endpoints of an interval on which a coordinate stays above their common value. -/
theorem merge_of_level_interval {X : ℝ → ℝ} {η : ℝ → ℂ}
    (hdistinct : ∀ x y, x ≠ y → IsLocalMin X x → IsLocalMin X y → X x ≠ X y)
    (hmerge : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel X s t → η s = η t)
    {a b level : ℝ} (hab : a ≤ b) (ha : X a = level) (hb : X b = level)
    (habove : ∀ u ∈ Ioo a b, level ≤ X u) : η a = η b := by
  by_cases heq : a = b
  · subst b
    rfl
  have hab' : a < b := lt_of_le_of_ne hab heq
  have hlocal : ∀ x, x ∈ Ioo a b → X x = level → IsLocalMin X x := by
    intro x hx hxval
    change ∀ᶠ y in 𝓝 x, X x ≤ X y
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [hxval]
    exact habove y hy
  have hunique : ∀ x y, x ∈ Ioo a b → y ∈ Ioo a b →
      X x = level → X y = level → x = y := by
    intro x y hx hy hxval hyval
    by_contra hxy
    exact hdistinct x y hxy (hlocal x hx hxval) (hlocal y hy hyval)
      (hxval.trans hyval.symm)
  by_cases htouch : ∃ x ∈ Ioo a b, X x = level
  · obtain ⟨m, hm, hmval⟩ := htouch
    have hleft : MatedCRTHarmonic.MatedCRT.DirectRel X a m := by
      refine ⟨hm.1, ha.trans hmval.symm, ?_⟩
      intro x hx
      have hge := habove x ⟨hx.1, lt_trans hx.2 hm.2⟩
      have hge' : X a ≤ X x := by rw [ha]; exact hge
      apply lt_of_le_of_ne hge'
      intro hxval
      have hxm := hunique x m ⟨hx.1, lt_trans hx.2 hm.2⟩ hm
        (hxval.symm.trans ha) hmval
      exact (ne_of_lt hx.2) hxm
    have hright : MatedCRTHarmonic.MatedCRT.DirectRel X m b := by
      refine ⟨hm.2, hmval.trans hb.symm, ?_⟩
      intro x hx
      have hge := habove x ⟨lt_trans hm.1 hx.1, hx.2⟩
      have hge' : X m ≤ X x := by rw [hmval]; exact hge
      apply lt_of_le_of_ne hge'
      intro hxval
      have hxm := hunique x m ⟨lt_trans hm.1 hx.1, hx.2⟩ hm
        (hxval.symm.trans hmval) hmval
      exact (ne_of_gt hx.1) hxm
    exact (hmerge a m hleft).trans (hmerge m b hright)
  · apply hmerge a b
    refine ⟨hab', ha.trans hb.symm, ?_⟩
    intro x hx
    have hge : X a ≤ X x := by rw [ha]; exact habove x hx
    apply lt_of_le_of_ne hge
    intro hxval
    exact htouch ⟨x, hx, hxval.symm.trans ha⟩

/-- The cells indexed by consecutive integers meet at their common time endpoint. -/
theorem consecutive_cells_meet {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (j : ℤ) :
    (cell ε η j ∩ cell ε η (j + 1)).Nonempty := by
  refine ⟨η (ε * j), ⟨ε * j, ?_, rfl⟩, ⟨ε * j, ?_, rfl⟩⟩
  · constructor
    · exact mul_le_mul_of_nonneg_left (by linarith) hε
    · exact le_rfl
  · constructor
    · simp only [Int.cast_add, Int.cast_one]
      have heq : ε * ((j : ℝ) + 1 - 1) = ε * j := by ring
      rw [heq]
    · simp only [Int.cast_add, Int.cast_one]
      exact mul_le_mul_of_nonneg_left (by linarith) hε

end MatedCRT
