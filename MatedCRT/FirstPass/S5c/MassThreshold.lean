import MatedCRT.FirstPass.S5c.Geometry

/-!
# FIRST PASS, Lemma 5.3: quantitative form of the deterministic geometric lemma (G-5-3 Section 3, eq. (9))

Eq. (9) holds eventually along any sequence of compact sets with vanishing exterior mass. Argued by contradiction,
it gives a threshold: there is `τ > 0` such that every compact `U ⊆ Q` with exterior mass `μ(U \ L) < τ` satisfies
eq. (9). This is the form used with the probabilistic convergence of the exterior mass (eq. (8)) in the S3 step.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- **Mass threshold for eq. (9)** (G-5-3 Section 3): for a regular open `L` with nonempty complement and a compact
`Q`, there is `τ > 0` such that compact `U ⊆ Q` with `μ (U \ L) < τ` have no point at depth `> δ` in their interior
which is within `3δ/4` of `Lᶜ`. -/
theorem exists_mass_threshold_of_deep_points {μ : Measure ℂ} {L Q : Set ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hL : interior (closure L) = L) (hLc : Lᶜ.Nonempty) (hQ : IsCompact Q)
    (hfull : ∀ x : ℂ, ∀ r : ℝ, 0 < r → 0 < μ (ball x r)) :
    ∃ τ : ℝ≥0∞, 0 < τ ∧ ∀ U : Set ℂ, IsCompact U → U ⊆ Q → μ (U \ L) < τ →
      ∀ z ∈ U, δ < infDist z (frontier U) → 3 * δ / 4 ≤ infDist z Lᶜ := by
  by_contra hcon
  have key : ∀ τ : ℝ≥0∞, 0 < τ → ∃ U : Set ℂ, IsCompact U ∧ U ⊆ Q ∧ μ (U \ L) < τ ∧
      ∃ z ∈ U, δ < infDist z (frontier U) ∧ infDist z Lᶜ < 3 * δ / 4 := by
    intro τ hτ
    by_contra hno
    exact hcon ⟨τ, hτ, fun U hUc hUQ hμ z hz hδz => by
      by_contra hlt
      exact hno ⟨U, hUc, hUQ, hμ, z, hz, hδz, not_le.1 hlt⟩⟩
  choose U hUc hUQ hμU z hzU hzδ hzL using fun n : ℕ =>
    key ((n : ℝ≥0∞))⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
  have hmass : Tendsto (fun n => μ (U n \ L)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ENNReal.tendsto_inv_nat_nhds_zero
      (fun n => zero_le) (fun n => (hμU n).le)
  have deep := deep_points_of_exterior_mass_tendsto_zero (μ := μ) (L := L) (Q := Q) (U := U) hδ hL hLc hQ
    hfull hUc hUQ hmass
  obtain ⟨n, hn⟩ := deep.exists
  exact absurd (hn (z n) (hzU n) (hzδ n)) (not_le.2 (hzL n))

end MatedCRT.S5c
