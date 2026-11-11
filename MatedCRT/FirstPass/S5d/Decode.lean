import MatedCRT.FirstPass.S5c.HExclusive
import MatedCRT.Defs.Sandpile

/-!
# Decoding the stopped odometer on a cell: deterministic part of the cluster-positivity step

Exclusive-point transfer. If the rescaled stopped odometer
`rescale mε ε η (stoppedOdometer m ε η ρ t)` is positive at every point of the cell `H^ε_a`, then the label `a` lies in the
strict discrete cluster `matedDiscreteCluster m ε η ρ t`. The proof uses an exclusive representative `x` of the cell
(`MatedCRT.S5c.exists_exclusive_mem_cell`, HExclusive.lean), at which the decoder returns `a`
(`MatedCRT.S5c.vertexOf_eq_of_exclusive`). No probability and no paper input.
-/

namespace MatedCRT

open MeasureTheory Set Metric

/-- **Exclusive decoding.** Let `η` be an area parametrization of `μ` and `ε > 0`. If the cell `H^ε_a` lies in `B_ρ` and the
rescaled stopped odometer `rescale mε ε η (stoppedOdometer m ε η ρ t)` is positive on the whole cell (with `mε > 0`), then
`a ∈ matedDiscreteCluster m ε η ρ t`, the strict discrete cluster `Λ^ε_t = {v_ε > 0}`. -/
theorem mem_matedDiscreteCluster_of_pos_on_cell {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η)
    {m : ℤ → ℤ → ℕ} {ε ρ t mε : ℝ} (hε : 0 < ε) (hmε : 0 < mε) {a : ℤ}
    (hcell : cell ε η a ⊆ ball (0 : ℂ) ρ)
    (hpos : ∀ x ∈ cell ε η a, 0 < rescale mε ε η (stoppedOdometer m ε η ρ t) x) :
    a ∈ matedDiscreteCluster m ε η ρ t := by
  obtain ⟨x, hxa, hex⟩ := MatedCRT.S5c.exists_exclusive_mem_cell hap hε a
  have hv : vertexOf ε η x = a := MatedCRT.S5c.vertexOf_eq_of_exclusive hxa hex
  have hx := hpos x hxa
  have hodo : 0 < stoppedOdometer m ε η ρ t a := by
    unfold rescale at hx
    rw [hv] at hx
    exact pos_of_mul_pos_right hx (inv_nonneg.mpr hmε.le)
  have hW : a ∈ cellVertices ε η (ball (0 : ℂ) ρ) := ⟨x, hxa, hcell hxa⟩
  have hWc : a ∈ cellVertices ε η (closedBall (0 : ℂ) ρ) :=
    ⟨x, hxa, ball_subset_closedBall (hcell hxa)⟩
  unfold stoppedOdometer at hodo
  simp only [hWc, ↓reduceIte] at hodo
  unfold matedDiscreteCluster discreteCluster
  exact ⟨hW, by linarith⟩

end MatedCRT
