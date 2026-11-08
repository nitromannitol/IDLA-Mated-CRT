import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSAnnealedRate
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSCellAnnulusEvent
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSDiskMargin
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.StartingCellEventual
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.External.SLE

/-! Annealed same-walk comparison with the joint GMS good event. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- For a fixed valid environment, the cell-size estimate and GMS annulus
estimate give an annealed same-walk rate from any fixed interior point. -/
theorem MatedCRTEnv.IsValid.annealed_eventually_sameWalkExitDiscrepancy_of_gms
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ ρ' a : ℝ} (hS : S.IsValid 𝒮 γ)
    (hcell : CellSizeEstimateStmt 𝒮) (hgms : GMSAnnulusDisconnectionStmt 𝒮)
    (hm : MepsScalingInput 𝒮) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hρ'1 : ρ' < 1)
    (ha : 0 < a) (ha' : a < 2 / (2 + γ) ^ 2) :
    ∃ β κ D ν : ℝ, 0 < β ∧ 0 < κ ∧ 0 ≤ D ∧ 0 < ν ∧
      ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → HolderOnWith H χ ψ (closedBall z r) →
      ∀ q : ℝ, 0 < q → q / (χ : ℝ) < min a β →
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        sectionwiseOuterProb S.P (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
          {p | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2} ≤
        ENNReal.ofReal (D * ε ^ κ + ((2 : ℝ) ^ ν * (202 : ℝ) ^ ν) *
          ε ^ ((min a β - q / (χ : ℝ)) * ν)) := by
  obtain ⟨β, p, κ, D, δ, hβ, hp, hp1, hκ, hD, hδ, hbad⟩ :=
    hS.cellSize_and_annulus_polyHighProb hcell hgms hγ hγ2 (hρ.trans hρρ') hρ'1 ha'
  obtain ⟨ν, hν, hbound⟩ := hS.annealed_sameWalkExitDiscrepancy_le_of_uniform_gms hγ hγ2 hp hp1
  obtain ⟨M, hM, hms⟩ := hm γ hγ hγ2
  obtain ⟨δm, hδm, hms⟩ := hms Ω S hS
  have hMpos : 0 < M := by linarith
  have hloc := hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)
  have hadj := adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS
  refine ⟨β, κ, D, ν, hβ, hκ, hD, hν, ?_⟩
  intro r z y hr hball hy ψ H χ hχ hψ q hq hqbound
  have hχ' : 0 < (χ : ℝ) := by exact_mod_cast hχ
  have hc : 0 < q / (χ : ℝ) := div_pos hq hχ'
  have hmargin := eventually_gms_disk_margin hρ hρρ' ha hc
  have hscale := eventually_gms_mesoscopic_scale (lt_of_lt_of_le hqbound (min_le_left a β))
    (lt_of_lt_of_le hqbound (min_le_right a β))
  have hball' : ball z r ⊆ ball (0 : ℂ) ρ' :=
    hball.trans (ball_subset_ball hρρ'.le)
  have hstart := eventually_vertexOf_mem_interior_of_small_cells ha hy hball'
  filter_upwards [hmargin, hscale, hstart, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hδ), nhdsWithin_le_nhds (Iio_mem_nhds hδm),
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with ε hmargin hscale hstart hε hεδ hεδm hε1
  have hε0 : 0 < ε := hε
  have hmpos : 0 < S.mε ε :=
    (mul_pos (inv_pos.mpr hMpos) (inv_pos.mpr hε0)).trans_le (hms ε hε0 hεδm).1
  let B : Set Ω := {ω | ¬ ((∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ').Nonempty →
    diam (cell ε (S.η ω) i) ≤ ε ^ a) ∧
    (∀ z ∈ ball (0 : ℂ) ρ', ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ' →
      ball z (2 * s) ⊆ ball 0 ρ' → ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
      ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
        {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
          walkDisconnectsBeforeHit (S.mult ε ω)
            (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}))}
  have hB : S.P B ≤ ENNReal.ofReal (D * ε ^ κ) := hbad ε hε0 hεδ
  have hgood : ∀ᵐ ω ∂S.P, ω ∉ B →
      IsLocallyFiniteMult (S.mult ε ω) ∧
      (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) ∧ 0 < S.mε ε ∧
      Continuous (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
      vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (ball z r) ∧
      (∀ j k, S.mult ε ω j k ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) ∧
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ').Nonempty → diam (cell ε (S.η ω) i) ≤ ε ^ a) ∧
      (∀ z ∈ ball (0 : ℂ) ρ', ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ' →
        ball z (2 * s) ⊆ ball 0 ρ' → ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
          {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}) := by
    filter_upwards [hloc, hS.isAreaParametrized, hS.ae_tendsto_cocompact, hadj] with ω hloc hη hp hadj
    intro hω
    have hconditions := not_not.mp hω
    exact ⟨hloc ε hε0, S.mult_succ_ne_zero hε0.le ω, hmpos, hη.1, hp,
      hstart (S.μ ω) (S.η ω) hη hp hconditions.1, hadj ε hε0,
      hconditions.1, hconditions.2⟩
  exact hbound ε a β ρ' q z r ψ H χ (fun ω => vertexOf ε (S.η ω) y) B
    (D * ε ^ κ) hε0 hε1.le hr hχ (by positivity) hψ hscale
    (hmargin z r hr hball) hB hgood

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.annealed_eventually_sameWalkExitDiscrepancy_of_gms
