import MatedCRT.Defs.Sandpile

/-!
# FIRST PASS, Lemma 5.3: per-outcome facts of the filled discrete cluster (hU, hUQ, hdiam, deterministic)

Structural facts for the hypotheses of `surplus_eventually_of_threshold` (SurplusEventually.lean):
* a vertex of the discrete cluster has a cell meeting the ball `B_ρ` (the cluster is a subset of `cellVertices (ball 0 ρ)`,
  Defs/Sandpile.lean:87-88, Defs/Map.lean:187);
* the filled cluster of a finite set of vertices is compact when the cells are compact (`hU`);
* if the cells meeting the ball have diameter at most `d`, the filled cluster lies in the closed ball of radius `ρ + d` (`hUQ`
  with `Q = closedBall 0 (ρ+1)` for `d ≤ 1`).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology

/-- A vertex of the discrete cluster has a cell meeting `B_ρ`. -/
theorem cell_meets_ball_of_mem_matedCluster {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ} {a : ℤ}
    (ha : a ∈ matedDiscreteCluster m ε η ρ t) : (cell ε η a ∩ ball (0 : ℂ) ρ).Nonempty := by
  unfold matedDiscreteCluster discreteCluster at ha
  exact ha.1

/-- The filled cluster of a finite set of vertices is compact when the curve is continuous. -/
theorem isCompact_fillCells_of_finite {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {A : Set ℤ} (hA : A.Finite) :
    IsCompact (fillCells ε η A) := by
  unfold fillCells
  exact hA.isCompact_biUnion fun k _ => isCompact_Icc.image hη

/-- The filled cluster lies in the closed ball of radius `ρ + d` when the cells meeting `B_ρ` have diameter at most `d`. -/
theorem fillCells_subset_closedBall_of_diam {ε ρ d : ℝ} {η : ℝ → ℂ} {A : Set ℤ}
    (hbdd : ∀ k : ℤ, Bornology.IsBounded (cell ε η k))
    (hA : ∀ k ∈ A, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty)
    (hdiam : ∀ k ∈ A, diam (cell ε η k) ≤ d) :
    fillCells ε η A ⊆ closedBall (0 : ℂ) (ρ + d) := by
  intro x hx
  obtain ⟨k, hkA, hxk⟩ := mem_iUnion₂.1 hx
  obtain ⟨y, hyk, hyb⟩ := hA k hkA
  have hxy : dist x y ≤ diam (cell ε η k) := dist_le_diam_of_mem (hbdd k) hxk hyk
  have hy : dist y 0 < ρ := mem_ball.1 hyb
  rw [mem_closedBall]
  have htri := dist_triangle x y (0 : ℂ)
  linarith [hdiam k hkA]

end MatedCRT.S5c
