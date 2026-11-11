import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundarySurvival

/-! # Polynomial bounds for hitting concentric boundaries -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- The GMS disconnection estimate and the cell-size event bound the chance
that a walk reaches the outermost annulus boundary before the boundary of
the target disk. The geometric scale hypotheses are left explicit. -/
theorem MatedCRTEnv.IsValid.ae_boundary_hit_order_le_power_of_gms_of_cell_size
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ (ε β ρ : ℝ) (z x : ℂ)
      (a : ℤ) (r : ℕ → ℝ) (n : ℕ) (R buffer margin bound : ℝ)
      (cutoff distance factor : ℝ),
      0 ≤ cutoff → 0 < distance → 0 ≤ factor →
      distance ≤ factor * cutoff * (2 : ℝ) ^ (n + 1) →
      0 < ε → 0 < R → 0 < buffer → bound ≤ margin →
      Antitone r → (∀ i ≤ n, 0 < r i ∧
        R + buffer - dist z x + margin < r i / 4 ∧
        ball z (2 * r i) ⊆ ball 0 ρ) →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        Metric.diam (cell ε (S.η ω) i) ≤ bound) →
      a ∈ interiorCellVertices ε (S.η ω) (ball z (r n)) →
      a ∈ cellVertices ε (S.η ω) (ball z (r n / 2)) →
      a ∈ interiorCellVertices ε (S.η ω) (ball x R) →
      (∀ v w, S.mult ε ω v w ≠ 0 →
        (cell ε (S.η ω) v ∩ cell ε (S.η ω) w).Nonempty) →
      (∀ i ≤ n, ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z (r i)), ∀ w,
        S.mult ε ω v w ≠ 0 → w ∈ interiorCellVertices ε (S.η ω) (ball z (r i)) ∪
          cellVertices ε (S.η ω) (sphere z (r i))) →
      (∀ v ∈ interiorCellVertices ε (S.η ω) (ball x R), ∀ w,
        S.mult ε ω v w ≠ 0 → w ∈ interiorCellVertices ε (S.η ω) (ball x R) ∪
          cellVertices ε (S.η ω) (sphere x R)) →
      (∀ᵐ path ∂srwLaw (S.mult ε ω) a,
        vExitTime (interiorCellVertices ε (S.η ω) (ball z (r 0))) path ≠ ⊤) →
      (∀ i < n, cellVertices ε (S.η ω) (sphere z (r (i + 1))) ∩
        cellVertices ε (S.η ω) (ball z (r (i + 1))) ⊆
          cellVertices ε (S.η ω) (ball z (r i / 2))) →
      z ∈ ball 0 ρ →
      (∀ i ≤ n, ε ^ β ≤ r i / 2 ∧ r i / 2 ≤ ρ ∧
        ball z (2 * (r i / 2)) ⊆ ball 0 ρ) →
      (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
        ball z (2 * s) ⊆ ball 0 ρ → ∀ v ∈ cellVertices ε (S.η ω) (ball z s),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) v
          {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}) →
      srwLaw (S.mult ε ω) a {path |
        vHitTime (cellVertices ε (S.η ω) (sphere z (r 0))) path ≤
          vHitTime (cellVertices ε (S.η ω) (sphere x R)) path} ≤
        ENNReal.ofReal ((factor * cutoff / distance) ^ ν) := by
  obtain ⟨ν, hν, hbound⟩ := hS.ae_nested_disk_survival_le_power_of_gms_of_cell_size hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hbound, hS.isAreaParametrized] with ω hbound harea
  intro ε β ρ z x a r n R buffer margin bound cutoff distance factor
    hcut hdist hfactor hscale hε hR hbuffer hmargin hr hgeometry hsize ha haS
    hatarget hadj hnb htargetnb hfin hnext hz hadmiss hgood
  calc
    _ ≤ srwLaw (S.mult ε ω) a {path | ∀ i ≤ n,
        vHitTime (cellVertices ε (S.η ω) (sphere z (r i))) path ≤
          vHitTime (cellVertices ε (S.η ω) (sphere x R)) path} := by
      apply measure_mono_ae
      filter_upwards [ae_nestedSphereCellHit_data harea.1 r hr n
        (fun i hi => (hgeometry i hi).1) ha hnb hfin] with path hordered
      intro houter i hi
      exact (hordered.2 0 i (Nat.zero_le i) hi).trans houter
    _ ≤ _ := (srwLaw_sphere_hit_order_le_nested_interior_survival hR hatarget htargetnb
      (fun i => cellVertices ε (S.η ω) (sphere z (r i))) n).trans
      (hbound ε β ρ z x a r (fun _ => R) n buffer margin bound cutoff distance factor
      hcut hdist hfactor hscale hε hbuffer hmargin hr hgeometry hsize ha haS
      hadj hnb hfin hnext hz hadmiss hgood)

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_boundary_hit_order_le_power_of_gms_of_cell_size
