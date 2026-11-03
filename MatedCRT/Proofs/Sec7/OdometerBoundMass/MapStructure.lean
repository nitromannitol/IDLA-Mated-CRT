import MatedCRT.Defs.Map

/-!
# Consecutive vertices of the mated-CRT map are adjacent (Definition 1.1, lines 173-177)

For continuous `L`, cell size `ε > 0` and every `k`, the adjacency condition (eq:edge-map, line 175) holds for the
vertices `εk` and `ε(k+1)`: the middle interval `[εk, ε(k+1) - ε]` is the point `εk`, which lies in both end
intervals. Hence `bmEdgeCount ε L R k (k + 1) ≠ 0` (`bmEdgeCount_succ_ne_zero`): the map of Definition 1.1 contains
the path `⋯ ∼ k ∼ k+1 ∼ ⋯` and is connected, for every continuous boundary-length pair.
-/

namespace MatedCRT.Sec7

open Set

theorem sInf_image_Icc_le {X : ℝ → ℝ} (hX : Continuous X) {a b s : ℝ} (hs : s ∈ Icc a b) :
    sInf (X '' Icc a b) ≤ X s :=
  csInf_le (isCompact_Icc.image hX).bddBelow ⟨s, hs, rfl⟩

/-- The adjacency condition (eq:edge-map) for consecutive vertices. -/
theorem bmAdjacent_succ {ε : ℝ} (hε : 0 < ε) {X : ℝ → ℝ} (hX : Continuous X) (k : ℤ) :
    bmAdjacent ε X k (k + 1) := by
  unfold bmAdjacent
  have h1 : ε * ((k + 1 : ℤ) : ℝ) - ε = ε * k := by push_cast; ring
  have h2 : ε * ((k + 1 : ℤ) : ℝ) = ε * k + ε := by push_cast; ring
  rw [h1, Set.Icc_self, Set.image_singleton, csInf_singleton]
  refine max_le (sInf_image_Icc_le hX ⟨by linarith, le_rfl⟩) (sInf_image_Icc_le hX ⟨le_rfl, ?_⟩)
  rw [h2]
  linarith

/-- **Consecutive vertices are adjacent** in the map of Definition 1.1, for a continuous path `L`. -/
theorem bmEdgeCount_succ_ne_zero {ε : ℝ} (hε : 0 < ε) {L : ℝ → ℝ} (hL : Continuous L) (R : ℝ → ℝ) (k : ℤ) :
    bmEdgeCount ε L R k (k + 1) ≠ 0 := by
  have hk : k ≠ k + 1 := by omega
  have hmin : min k (k + 1) = k := min_eq_left (by omega)
  have hmax : max k (k + 1) = k + 1 := max_eq_right (by omega)
  have hadj : bmAdjacent ε L (min k (k + 1)) (max k (k + 1)) := by
    rw [hmin, hmax]
    exact bmAdjacent_succ hε hL k
  unfold bmEdgeCount
  simp only [hk, ↓reduceIte]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inl hadj))]
  split_ifs <;> omega

end MatedCRT.Sec7
