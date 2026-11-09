import MatedCRT.Defs.Map
import MatedCRT.Defs.Notation

/-!
# FIRST PASS, Proposition 5.1: deterministic vertex-threshold geometry

Plane topology and the cell structure of `MatedCRT/Defs/Map.lean`; no probability and no paper input.
This is the geometric step of the proof of Proposition 5.1 (paper lines 2343-2358, after CORRECTION [C4]).
From `B⁻_{δ/2}(Λ) ⊆ Ā(D)` (the cell-union form of Proposition 4.2) and cell diameters `< δ/4` for the cells
meeting `Λ`, every point of `B⁻_δ(Λ)` lies in the cell of a vertex `a ∈ D` whose vertex point is at distance
`> δ/8` from the frontier of `Ā(D)`. Those vertices form the sets `O₁` of Lemma 5.2 (`GeneralIDLALowerBoundStmt`)
and the sets of Lemmas 5.3-5.4 with `δ/8` in place of `δ`.
-/

namespace MatedCRT

open Metric Set Topology

/-- Vertex-threshold covering: `B⁻_δ(Λ) ⊆ Ā(O)` for `O = {a ∈ D : δ/8 < dist(η(εa), ∂Ā(D))}`. -/
theorem innerNbhd_subset_fillCells_vertexThreshold (ε : ℝ) (η : ℝ → ℂ) (hε : 0 < ε) (D : Set ℤ) (Λ : Set ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hin : innerNbhd (δ / 2) Λ ⊆ fillCells ε η D)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ Λ).Nonempty → ∀ y ∈ cell ε η k, ∀ z ∈ cell ε η k, dist y z < δ / 4)
    (hcompl : fillCells ε η D ≠ univ) :
    innerNbhd δ Λ ⊆
      fillCells ε η {a | a ∈ D ∧ δ / 8 < infDist (vertexPoint ε η a) (frontier (fillCells ε η D))} := by
  intro y hy
  obtain ⟨hyΛ, hyfar⟩ := hy
  have hyhalf : y ∈ innerNbhd (δ / 2) Λ :=
    ⟨hyΛ, le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hyfar⟩
  have hyS : y ∈ fillCells ε η D := hin hyhalf
  unfold fillCells at hyS
  obtain ⟨k, hkD, hyk⟩ := mem_iUnion₂.1 hyS
  have hpk : η (ε * k) ∈ cell ε η k := by
    refine ⟨ε * k, ⟨?_, le_rfl⟩, rfl⟩
    have h1 : (k : ℝ) - 1 ≤ k := by linarith
    exact mul_le_mul_of_nonneg_left h1 hε.le
  have hdy : dist y (η (ε * k)) < δ / 4 :=
    hdiam k ⟨y, hyk, hyΛ⟩ y hyk _ hpk
  -- the ball of radius δ/4 around the vertex point lies in Ā(D)
  have hball : Metric.ball (η (ε * k)) (δ / 4) ⊆ fillCells ε η D := by
    intro z hz
    have hz' : dist z (η (ε * k)) < δ / 4 := mem_ball.1 hz
    have hyz : dist y z < δ / 2 := by
      have := dist_triangle y (η (ε * k)) z
      rw [dist_comm (η (ε * k)) z] at this
      linarith
    have hzΛ : z ∈ Λ := by
      by_contra hzΛ
      have h1 : ENNReal.ofReal δ ≤ edist y z :=
        le_trans hyfar (Metric.infEDist_le_edist_of_mem (show z ∈ Λᶜ from hzΛ))
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at h1
      linarith
    have hzin : z ∈ innerNbhd (δ / 2) Λ := by
      refine ⟨hzΛ, ?_⟩
      apply Metric.le_infEDist.2
      intro w hw
      have h1 : ENNReal.ofReal δ ≤ edist y w := le_trans hyfar (Metric.infEDist_le_edist_of_mem hw)
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at h1
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      linarith [dist_triangle y z w]
    exact hin hzin
  -- the vertex point is at distance at least δ/4 from the frontier of Ā(D)
  have hint : Metric.ball (η (ε * k)) (δ / 4) ⊆ interior (fillCells ε η D) :=
    interior_maximal hball isOpen_ball
  have hne : (frontier (fillCells ε η D)).Nonempty :=
    nonempty_frontier_iff.2 ⟨⟨y, by unfold fillCells; exact mem_iUnion₂.2 ⟨k, hkD, hyk⟩⟩, hcompl⟩
  have hlow : δ / 4 ≤ infDist (η (ε * k)) (frontier (fillCells ε η D)) := by
    rw [Metric.le_infDist hne]
    intro f hf
    rw [dist_comm]
    by_contra hlt
    exact hf.2 (hint (mem_ball.2 (not_le.1 hlt)))
  have hthr : k ∈ {a | a ∈ D ∧ δ / 8 < infDist (vertexPoint ε η a) (frontier (fillCells ε η D))} := by
    refine ⟨hkD, ?_⟩
    show δ / 8 < infDist (η (ε * k)) (frontier (fillCells ε η D))
    linarith
  unfold fillCells
  exact mem_biUnion hthr hyk

end MatedCRT
