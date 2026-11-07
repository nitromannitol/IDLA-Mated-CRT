import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSDyadicBoundaryHit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundaryCellAnnulusGeometry
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.DiskDecompositionGeometry

/-! # Annulus hitting from a boundary cell -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- On the GMS good event, the walk restarted at a small boundary cell has
polynomially small probability to reach an outer circle before the boundary
of the enlarged disk. -/
theorem MatedCRTEnv.IsValid.ae_boundary_cell_hit_order_le_power
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ (ε β ρ : ℝ) (z : ℂ)
      (a : ℤ) (r d cutoff distance : ℝ),
      0 < ε → 0 < r → 0 < d → 24 * d < cutoff → cutoff ≤ distance →
      2 * ε ^ β ≤ cutoff →
      2 * distance + dist (vertexPoint ε (S.η ω) a) 0 ≤ ρ →
      vertexPoint ε (S.η ω) a ∈ ball 0 ρ →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ d) →
      diam (cell ε (S.η ω) a) ≤ d →
      a ∈ cellVertices ε (S.η ω) (sphere z r) →
      (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
        ball z (2 * s) ⊆ ball 0 ρ → ∀ v ∈ cellVertices ε (S.η ω) (ball z s),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) v
          {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}) →
      srwLaw (S.mult ε ω) a {path |
        vHitTime (cellVertices ε (S.η ω)
          (sphere (vertexPoint ε (S.η ω) a) distance)) path ≤
          vHitTime (cellVertices ε (S.η ω) (sphere z (r + 3 * d))) path} ≤
        ENNReal.ofReal ((cutoff / distance) ^ ν) := by
  obtain ⟨ν, hν, hbound⟩ := hS.ae_boundary_hit_order_le_power_of_dyadic_scales hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hbound, hS.isAreaParametrized,
    hS.ae_disk_dirichlet_decomposition_geometry hγ hγ2,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hbound harea hgeometry hadj
  intro ε β ρ z a r d cutoff distance hε hr hd hcut hcd hmesh hcontain hcenter
    hsize hdiam ha hgood
  have hc : 0 < cutoff := by linarith
  have hdist : 0 < distance := lt_of_lt_of_le hc hcd
  have hR : 0 < r + 3 * d := by linarith
  obtain ⟨hstart, hstartS, htarget, hclear⟩ :=
    boundary_cell_annulus_geometry hε.le harea.1 hd hcut hdiam ha
  have hnb : ∀ s : ℝ, ∀ v ∈ interiorCellVertices ε (S.η ω)
      (ball (vertexPoint ε (S.η ω) a) s), ∀ w,
      S.mult ε ω v w ≠ 0 → w ∈ interiorCellVertices ε (S.η ω)
        (ball (vertexPoint ε (S.η ω) a) s) ∪
        cellVertices ε (S.η ω) (sphere (vertexPoint ε (S.η ω) a) s) := by
    intro s v hv w hvw
    obtain ⟨q, _, hq⟩ := hv.1
    have hs : 0 < s := lt_of_le_of_lt (dist_nonneg) (mem_ball.mp hq)
    exact (hgeometry ε hε _ s hs).2.2.1 v hv w hvw
  have hsub := interiorCellVertices_concentric_ball_mono (ε := ε) harea.1
    (vertexPoint ε (S.η ω) a) hcd
  have hfin := (hgeometry ε hε (vertexPoint ε (S.η ω) a) distance hdist).2.2.2.2 a (hsub hstart)
  exact hbound ε β ρ (vertexPoint ε (S.η ω) a) z a (r + 3 * d) d d d cutoff distance
    hε hR hd le_rfl hc hcd hmesh hclear hcontain hcenter hsize hstart hstartS htarget
    (hadj ε hε) hnb ((hgeometry ε hε z (r + 3 * d) hR).2.2.1) hfin hgood

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_boundary_cell_hit_order_le_power
