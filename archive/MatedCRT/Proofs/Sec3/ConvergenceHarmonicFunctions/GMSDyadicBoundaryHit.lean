import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AdmissibleAnnulusScales
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSBoundaryHit

/-! # Boundary hitting using admissible dyadic annuli -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- The GMS disconnection and cell-size estimates give polynomial decay for
hitting a prescribed outer circle before the target boundary. The cutoff
and outer distance carry the geometric admissibility conditions. -/
theorem MatedCRTEnv.IsValid.ae_boundary_hit_order_le_power_of_dyadic_scales
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ (ε β ρ : ℝ) (z x : ℂ)
      (a : ℤ) (R buffer margin bound cutoff distance : ℝ),
      0 < ε → 0 < R → 0 < buffer → bound ≤ margin →
      0 < cutoff → cutoff ≤ distance → 2 * ε ^ β ≤ cutoff →
      4 * (R + buffer - dist z x + margin) < cutoff →
      2 * distance + dist z 0 ≤ ρ → z ∈ ball 0 ρ →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ bound) →
      a ∈ interiorCellVertices ε (S.η ω) (ball z cutoff) →
      a ∈ cellVertices ε (S.η ω) (ball z (cutoff / 2)) →
      a ∈ interiorCellVertices ε (S.η ω) (ball x R) →
      (∀ v w, S.mult ε ω v w ≠ 0 →
        (cell ε (S.η ω) v ∩ cell ε (S.η ω) w).Nonempty) →
      (∀ s : ℝ, ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z s), ∀ w,
        S.mult ε ω v w ≠ 0 → w ∈ interiorCellVertices ε (S.η ω) (ball z s) ∪
          cellVertices ε (S.η ω) (sphere z s)) →
      (∀ v ∈ interiorCellVertices ε (S.η ω) (ball x R), ∀ w,
        S.mult ε ω v w ≠ 0 → w ∈ interiorCellVertices ε (S.η ω) (ball x R) ∪
          cellVertices ε (S.η ω) (sphere x R)) →
      (∀ᵐ path ∂srwLaw (S.mult ε ω) a,
        vExitTime (interiorCellVertices ε (S.η ω) (ball z distance)) path ≠ ⊤) →
      (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
        ball z (2 * s) ⊆ ball 0 ρ → ∀ v ∈ cellVertices ε (S.η ω) (ball z s),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) v
          {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}) →
      srwLaw (S.mult ε ω) a {path |
        vHitTime (cellVertices ε (S.η ω) (sphere z distance)) path ≤
          vHitTime (cellVertices ε (S.η ω) (sphere x R)) path} ≤
        ENNReal.ofReal ((cutoff / distance) ^ ν) := by
  obtain ⟨ν, hν, hbound⟩ := hS.ae_boundary_hit_order_le_power_of_gms_of_cell_size hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hbound, hS.isAreaParametrized] with ω hbound harea
  intro ε β ρ z x a R buffer margin bound cutoff distance hε hR hbuffer hmargin
    hc hd hmesh hclear hcontain hz hsize ha haS hatarget hadj hnb htargetnb hfin hgood
  obtain ⟨n, r, hr, hlast, hfirst, hscale, hgeometry, hadmiss, hnext⟩ :=
    exists_admissible_dyadic_annulus_scales (η := S.η ω) (x := x) hc hd hmesh hclear hcontain
  have ha' : a ∈ interiorCellVertices ε (S.η ω) (ball z (r n)) := by simpa [hlast] using ha
  have haS' : a ∈ cellVertices ε (S.η ω) (ball z (r n / 2)) := by simpa [hlast] using haS
  have hsub := interiorCellVertices_concentric_ball_mono (ε := ε) harea.1 z hfirst
  have hfin' : ∀ᵐ path ∂srwLaw (S.mult ε ω) a,
      vExitTime (interiorCellVertices ε (S.η ω) (ball z (r 0))) path ≠ ⊤ := by
    filter_upwards [hfin] with path hpath
    exact ne_top_of_le_ne_top hpath (vExitTime_mono_domain hsub path)
  have ha0 := interiorCellVertices_concentric_ball_mono (ε := ε) harea.1 z (hr (Nat.zero_le n)) ha'
  calc
    _ ≤ srwLaw (S.mult ε ω) a {path |
        vHitTime (cellVertices ε (S.η ω) (sphere z (r 0))) path ≤
          vHitTime (cellVertices ε (S.η ω) (sphere x R)) path} :=
      srwLaw_sphere_hit_order_le_of_radius_le harea.1 (hgeometry 0 (Nat.zero_le n)).1
        hfirst ha0 (fun s _ => hnb s) hfin _
    _ ≤ ENNReal.ofReal ((cutoff / distance) ^ ν) := by
      simpa only [one_mul] using hbound ε β ρ z x a r n R buffer margin bound
        cutoff distance 1 hc.le (lt_of_lt_of_le hc hd) (by norm_num) (by simpa using hscale)
        hε hR hbuffer hmargin hr hgeometry hsize ha' haS' hatarget hadj
        (fun i _ => hnb (r i)) htargetnb hfin' hnext hz hadmiss hgood

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_boundary_hit_order_le_power_of_dyadic_scales
