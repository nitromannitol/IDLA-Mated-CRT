import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSAnnulusSurvival
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.SafeRadialWalk

/-! # Annulus survival with geometrically constructed separating walks -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- The GMS nested-annulus bound with the separating walks derived from the
cell-size event. The walk's allowed region consists of the interior cells
of the target disk; the separating walks lie outside that region. -/
theorem MatedCRTEnv.IsValid.ae_nested_disk_survival_le_power_of_gms_of_cell_size
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ (ε β ρ : ℝ) (z x : ℂ)
      (a : ℤ) (r radius : ℕ → ℝ) (n : ℕ) (buffer margin bound : ℝ)
      (cutoff distance factor : ℝ),
      0 ≤ cutoff → 0 < distance → 0 ≤ factor →
      distance ≤ factor * cutoff * (2 : ℝ) ^ (n + 1) →
      0 < ε → 0 < buffer → bound ≤ margin →
      Antitone r → (∀ i ≤ n, 0 < r i ∧
        radius i + buffer - dist z x + margin < r i / 4 ∧
        ball z (2 * r i) ⊆ ball 0 ρ) →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        Metric.diam (cell ε (S.η ω) i) ≤ bound) →
      a ∈ interiorCellVertices ε (S.η ω) (ball z (r n)) →
      a ∈ cellVertices ε (S.η ω) (ball z (r n / 2)) →
      (∀ v w, S.mult ε ω v w ≠ 0 →
        (cell ε (S.η ω) v ∩ cell ε (S.η ω) w).Nonempty) →
      (∀ i ≤ n, ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z (r i)), ∀ w,
        S.mult ε ω v w ≠ 0 → w ∈ interiorCellVertices ε (S.η ω) (ball z (r i)) ∪
          cellVertices ε (S.η ω) (sphere z (r i))) →
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
      srwLaw (S.mult ε ω) a {path | ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) <
        vHitTime (cellVertices ε (S.η ω) (sphere z (r i))) path →
          path j ∈ interiorCellVertices ε (S.η ω) (ball x (radius i))} ≤
        ENNReal.ofReal ((factor * cutoff / distance) ^ ν) := by
  obtain ⟨ν, hν, hbound⟩ := measure_nested_disk_survival_le_power_of_gms hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hS.ae_nested_annulus_separating_walks_of_cell_size,
    hS.isAreaParametrized] with ω hwalk harea
  intro ε β ρ z x a r radius n buffer margin bound cutoff distance factor
    hcut hdist hfactor hscale hε hbuffer hmargin hr hgeometry hsize ha haS hadj
    hnb hfin hnext hz hadmiss hgood
  apply hbound (S.mult ε ω) ε β ρ (S.η ω) z a r n
    (fun i => interiorCellVertices ε (S.η ω) (ball x (radius i)))
    cutoff distance factor hcut hdist hfactor hscale harea.1 hr
    (fun i hi => (hgeometry i hi).1) ha haS hadj hnb hfin hnext
    ?_ hz hadmiss hgood
  intro i hi
  obtain ⟨y, b, hy, hb, w, hw⟩ := hwalk ε hε z x r
    (fun i => radius i + buffer) n margin bound ρ hmargin hgeometry hsize i hi
  refine ⟨y, b, hy, hb, w, ?_⟩
  intro v hv hinside
  apply hw v hv
  obtain ⟨q, hq, hqball⟩ := hinside.1
  refine ⟨q, hq, Metric.mem_ball.mpr ?_⟩
  have hdist := Metric.mem_ball.mp hqball
  linarith

end MatedCRT
