import MatedCRT.Defs.Map
import MatedCRT.FirstPass.S5c.Core

/-!
# FIRST PASS, Lemma 5.3: depth vertices lie in the compact core (G-5-3 Section 3, eq. (10))

A vertex `a` of the discrete cluster `D` whose vertex point is at depth `> δ` from the frontier of the filled cluster
`U = fillCells D` has a cell point `x ∈ cell a` with `vertexOf x = a` (`hx`, from the area parametrization) lying in the
compact core `compactCore L ρ δ` of the harmonic ball, provided: the cell has diameter `< δ/4`, and the exterior mass of
`U` relative to `L` is below the threshold `τ` of the quantitative eq. (9) (`MassThreshold.lean`). Deterministic.
-/

namespace MatedCRT.S5c

open MeasureTheory Metric Set
open scoped ENNReal

/-- **Depth vertices in the compact core** (G-5-3 eq. (10)): see the module docstring. -/
theorem exists_core_point_of_depth {μ : Measure ℂ} {L Q : Set ℂ} {δ ε ρ : ℝ} {η : ℝ → ℂ} {a : ℤ} {D : Set ℤ}
    (hδ : 0 < δ) (hε : 0 < ε) (hLball : L ⊆ closedBall 0 ρ) (τ : ℝ≥0∞)
    (hτ : ∀ U : Set ℂ, IsCompact U → U ⊆ Q → μ (U \ L) < τ → ∀ z ∈ U,
      3 * δ / 4 < infDist z (frontier U) → 3 * (3 * δ / 4) / 4 ≤ infDist z Lᶜ)
    (hU : IsCompact (fillCells ε η D)) (hUQ : fillCells ε η D ⊆ Q) (hmass : μ (fillCells ε η D \ L) < τ)
    (haD : a ∈ D) (hbdd : Bornology.IsBounded (cell ε η a)) (hdiam : diam (cell ε η a) < δ / 4)
    (hdepth : δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η D)))
    (hx : ∃ x ∈ cell ε η a, vertexOf ε η x = a) :
    ∃ x ∈ compactCore L ρ δ, x ∈ cell ε η a ∧ vertexOf ε η x = a := by
  obtain ⟨x, hxcell, hxa⟩ := hx
  have hvc : vertexPoint ε η a ∈ cell ε η a := by
    refine ⟨ε * (a : ℝ), ⟨?_, le_refl _⟩, rfl⟩
    exact mul_le_mul_of_nonneg_left (by linarith) hε.le
  have hdist : dist x (vertexPoint ε η a) ≤ diam (cell ε η a) := dist_le_diam_of_mem hbdd hxcell hvc
  have h1 := infDist_le_infDist_add_dist (x := vertexPoint ε η a) (y := x)
    (s := frontier (fillCells ε η D))
  rw [dist_comm] at h1
  have hfr : 3 * δ / 4 < infDist x (frontier (fillCells ε η D)) := by linarith
  have hxU : x ∈ fillCells ε η D := mem_iUnion₂.2 ⟨a, haD, hxcell⟩
  have hcore : 3 * (3 * δ / 4) / 4 ≤ infDist x Lᶜ := hτ (fillCells ε η D) hU hUQ hmass x hxU hfr
  have hxL : x ∈ L := by
    by_contra hxL
    have h0 : infDist x Lᶜ = 0 := infDist_zero_of_mem hxL
    rw [h0] at hcore
    linarith
  have hxball : x ∈ closedBall (0 : ℂ) ρ := hLball hxL
  have hfin : δ / 2 ≤ infDist x Lᶜ := by linarith
  exact ⟨x, ⟨hxball, hfin⟩, hxcell, hxa⟩

end MatedCRT.S5c
