import Mathlib

/-!
# FIRST PASS, Lemma 5.3: compact core of the harmonic ball (G-5-3 Section 3, eq. (10))

The compact core `K_δ = {x ∈ B̄_ρ : d(x, Λᶜ) ≥ δ/2}` of the harmonic ball `Λ` (G-5-3 eq. (10)) is a compact subset of
`Λ`, and it contains the vertex points at depth `> δ` of the discrete cluster by eq. (9) (`deep_points_of_exterior_mass_tendsto_zero`).
Pure plane topology; no paper input.
-/

namespace MatedCRT.S5c

open Metric Set Topology

/-- The compact core `K_δ = {x ∈ B̄_ρ : d(x, Lᶜ) ≥ δ/2}` of a set `L` with nonempty complement (G-5-3, eq. (10)). -/
def compactCore (L : Set ℂ) (ρ δ : ℝ) : Set ℂ :=
  closedBall (0 : ℂ) ρ ∩ {x | δ / 2 ≤ infDist x Lᶜ}

/-- The compact core is compact. -/
lemma isCompact_compactCore (L : Set ℂ) (ρ δ : ℝ) : IsCompact (compactCore L ρ δ) := by
  refine (isCompact_closedBall (0 : ℂ) ρ).inter_right ?_
  exact isClosed_le continuous_const (continuous_infDist_pt Lᶜ)

/-- The compact core lies in `L` when `δ > 0`: a point outside `L` has distance zero to `Lᶜ`. -/
lemma compactCore_subset {L : Set ℂ} {ρ δ : ℝ} (hδ : 0 < δ) : compactCore L ρ δ ⊆ L := by
  intro x hx
  by_contra hxL
  have h0 : infDist x Lᶜ = 0 := infDist_zero_of_mem hxL
  have h1 : δ / 2 ≤ infDist x Lᶜ := hx.2
  rw [h0] at h1
  linarith

end MatedCRT.S5c
