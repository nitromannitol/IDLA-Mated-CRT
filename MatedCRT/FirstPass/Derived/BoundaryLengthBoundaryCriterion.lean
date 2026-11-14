import MatedCRT.FirstPass.Derived.BoundaryLengthFirstCrossing
import MatedCRT.FirstPass.Derived.BoundaryLengthFutureEdge
import LatticeProb.Analysis.FirstMeshDipAfterInterval

/-!
# Past criterion for boundary-length edges

Protection of a cell minimum and a subsequent dip yield a later side edge.
This gives a criterion for an outside edge using only past edges and protected
cell minima.
-/

set_option autoImplicit false

open Set

namespace MatedCRT

/-- If a cell minimum is protected through a mesh endpoint and the path later
falls below it, the cell has a side edge beyond that endpoint. -/
theorem exists_bmAdjacent_after_of_protected {ε : ℝ} (hε : 0 < ε)
    {X : ℝ → ℝ} (hX : Continuous X) {j N : ℤ} (hjN : j ≤ N)
    (hprotected : ∀ u ∈ Icc (ε * j) (ε * N),
      sInf (X '' Icc (ε * j - ε) (ε * j)) ≤ X u)
    (hdip : ∃ t ≥ ε * j, X t < sInf (X '' Icc (ε * j - ε) (ε * j))) :
    ∃ k : ℤ, N < k ∧ bmAdjacent ε X j k := by
  have hjNreal : (j : ℝ) ≤ N := by exact_mod_cast hjN
  have hjNmesh : ε * j ≤ ε * N := mul_le_mul_of_nonneg_left hjNreal hε.le
  obtain ⟨n, t, ht, hlt, hbefore, hleft⟩ :=
    LatticeProb.exists_first_mesh_dip_after_of_forall_ge
      (a := ε * j) (b := ε * N - ε) (s := ε * N)
      (c := sInf (X '' Icc (ε * j - ε) (ε * j))) hε hjNmesh
      (by linarith) hprotected hdip
  let k : ℤ := j + (n : ℤ) + 1
  have hjk : j < k := by dsimp [k]; omega
  have hleft_eq : ε * k - ε = ε * j + (n : ℝ) * ε := by
    dsimp [k]
    push_cast
    ring
  have hright_eq : ε * k = ε * j + ((n : ℝ) + 1) * ε := by
    dsimp [k]
    push_cast
    ring
  have hNk : N < k := by
    by_contra h
    have hkN : k ≤ N := le_of_not_gt h
    have hkNreal : (k : ℝ) ≤ N := by exact_mod_cast hkN
    have hmesh : ε * k ≤ ε * N := mul_le_mul_of_nonneg_left hkNreal hε.le
    rw [← hleft_eq] at hleft
    linarith
  refine ⟨k, hNk, bmAdjacent_of_first_crossing hε hX hjk ?_ hlt.le ?_⟩
  · rw [hleft_eq, hright_eq]
    exact ht
  · simpa only [hleft_eq] using hbefore

/-- An outside edge is detected by past edges and protected cell minima,
provided both coordinates subsequently dip below the initial cell minima. -/
theorem exists_outside_bmEdge_iff_past_or_protected {ε α β : ℝ} (hε : 0 < ε)
    {L R : ℝ → ℝ} (hL : Continuous L) (hR : Continuous R)
    {j N : ℤ} (hjN : j ≤ N) (hβ : β < ε * ((N : ℝ) + 1))
    (hLdip : ∃ t ≥ ε * j, L t < sInf (L '' Icc (ε * j - ε) (ε * j)))
    (hRdip : ∃ t ≥ ε * j, R t < sInf (R '' Icc (ε * j - ε) (ε * j))) :
    (∃ k : ℤ, ¬ (α ≤ ε * k ∧ ε * k ≤ β) ∧ bmEdgeCount ε L R j k ≠ 0) ↔
    (∃ k : ℤ, k ≤ N ∧ ¬ (α ≤ ε * k ∧ ε * k ≤ β) ∧
      bmEdgeCount ε L R j k ≠ 0) ∨
    (∀ u ∈ Icc (ε * j) (ε * N),
      sInf (L '' Icc (ε * j - ε) (ε * j)) ≤ L u) ∨
    (∀ u ∈ Icc (ε * j) (ε * N),
      sInf (R '' Icc (ε * j - ε) (ε * j)) ≤ R u) := by
  constructor
  · rintro ⟨k, hout, hedge⟩
    by_cases hk : k ≤ N
    · exact Or.inl ⟨k, hk, hout, hedge⟩
    · exact Or.inr (cellMin_le_of_bmEdgeCount_ne_zero_of_between hε hL hR hjN
        (lt_of_not_ge hk) hedge)
  · rintro (⟨k, _, hout, hedge⟩ | hprotect | hprotect)
    · exact ⟨k, hout, hedge⟩
    · obtain ⟨k, hk, hadj⟩ := exists_bmAdjacent_after_of_protected hε hL hjN hprotect hLdip
      have hNk : (N : ℝ) + 1 ≤ k := by exact_mod_cast (show N + 1 ≤ k by omega)
      have hβk : β < ε * k := lt_of_lt_of_le hβ (mul_le_mul_of_nonneg_left hNk hε.le)
      exact ⟨k, fun h => (not_le_of_gt hβk) h.2,
        bmEdgeCount_ne_zero_of_side_adjacent (lt_of_le_of_lt hjN hk) (Or.inl hadj)⟩
    · obtain ⟨k, hk, hadj⟩ := exists_bmAdjacent_after_of_protected hε hR hjN hprotect hRdip
      have hNk : (N : ℝ) + 1 ≤ k := by exact_mod_cast (show N + 1 ≤ k by omega)
      have hβk : β < ε * k := lt_of_lt_of_le hβ (mul_le_mul_of_nonneg_left hNk hε.le)
      exact ⟨k, fun h => (not_le_of_gt hβk) h.2,
        bmEdgeCount_ne_zero_of_side_adjacent (lt_of_le_of_lt hjN hk) (Or.inr hadj)⟩

end MatedCRT
