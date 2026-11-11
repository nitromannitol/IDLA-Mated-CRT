import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSMeanEventual
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSEventualRate
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSCellAnnulusEvent
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.External.SLE

/-! Joint quenched tail and mean estimates on one geometric event. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- For a fixed environment, one joint cell-size and annulus event has a
polynomially small complement and supports both quenched estimates almost
surely, for every sufficiently small mesh. -/
theorem MatedCRTEnv.IsValid.exists_joint_good_event_sameWalk_rates
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ ρ' a : ℝ} (hS : S.IsValid 𝒮 γ)
    (hcell : CellSizeEstimateStmt 𝒮) (hgms : GMSAnnulusDisconnectionStmt 𝒮)
    (hm : MepsScalingInput 𝒮) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hρ'1 : ρ' < 1)
    (ha : 0 < a) (ha' : a < 2 / (2 + γ) ^ 2) :
    ∃ β κ D νt νm : ℝ, 0 < β ∧ 0 < κ ∧ 0 ≤ D ∧ 0 < νt ∧ 0 < νm ∧
      ∃ E : ℝ → Set Ω, ∃ δ : ℝ, 0 < δ ∧
        (∀ ε : ℝ, 0 < ε → ε < δ → S.P (E ε)ᶜ ≤ ENNReal.ofReal (D * ε ^ κ)) ∧
        (∀ (χ : ℝ≥0) (q : ℝ), 0 < χ → 0 < q → q / (χ : ℝ) < min a β →
          ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ ω ∂S.P, ω ∈ E ε →
            ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
            ∀ (ψ : ℂ → ℝ) (H : ℝ≥0), HolderOnWith H χ ψ (closedBall z r) →
            ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
              srwLaw (S.mult ε ω) v
                {path | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω path} ≤
              ENNReal.ofReal (((2 : ℝ) ^ νt * (202 : ℝ) ^ νt) *
                ε ^ ((min a β - q / (χ : ℝ)) * νt))) ∧
        (∀ (r : ℝ) (χ : ℝ≥0), 0 < r → 0 < χ →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ ω ∂S.P, ω ∈ E ε →
            ∀ (z : ℂ) (ψ : ℂ → ℝ) (H : ℝ≥0) (v : ℤ),
              ball z r ⊆ ball 0 ρ → HolderOnWith H χ ψ (closedBall z r) →
              v ∈ interiorCellVertices ε (S.η ω) (ball z r) →
              (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
                C * (H : ℝ) *
                  (if (χ : ℝ) < νm then ε ^ (min a β * χ)
                   else if (χ : ℝ) = νm then ε ^ (min a β * νm) * (1 + |Real.log ε|)
                   else ε ^ (min a β * νm))) := by
  obtain ⟨β, p, κ, D, δ, hβ, hp, hp1, hκ, hD, hδ, hbad⟩ :=
    hS.cellSize_and_annulus_polyHighProb hcell hgms hγ hγ2 (hρ.trans hρρ') hρ'1 ha'
  obtain ⟨νt, hνt, htail⟩ := hS.uniform_mesh_ae_sameWalkExitDiscrepancy_le_of_gms hγ hγ2 hp hp1
  obtain ⟨νm, hνm, hmean⟩ := hS.uniform_mesh_ae_sameWalkExitDiscrepancy_mean_of_gms hγ hγ2 hp hp1
  obtain ⟨M, hM, hms⟩ := hm γ hγ hγ2
  obtain ⟨δm, hδm, hms⟩ := hms Ω S hS
  have hMpos : 0 < M := by linarith
  have hloc := hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)
  have hadj := adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS
  let E : ℝ → Set Ω := fun ε => {ω | (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ').Nonempty →
    diam (cell ε (S.η ω) i) ≤ ε ^ a) ∧
    (∀ z ∈ ball (0 : ℂ) ρ', ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ' →
      ball z (2 * s) ⊆ ball 0 ρ' → ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
      ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
        {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
          walkDisconnectsBeforeHit (S.mult ε ω)
            (cellVertices ε (S.η ω) (sphere z (2 * s))) y path})}
  refine ⟨β, κ, D, νt, νm, hβ, hκ, hD, hνt, hνm, E, δ, hδ, ?_, ?_, ?_⟩
  · exact hbad
  · intro χ q hχ hq hqbound
    obtain ⟨U, hU, htail⟩ := htail a β ρ ρ' q χ hρ hρρ' ha hχ hq hqbound
    filter_upwards [hU, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδm)] with ε hεU hε hεδm
    have hε0 : 0 < ε := hε
    have hmpos : 0 < S.mε ε :=
      (mul_pos (inv_pos.mpr hMpos) (inv_pos.mpr hε0)).trans_le (hms ε hε0 hεδm).1
    filter_upwards [htail, hloc, hS.isAreaParametrized, hS.ae_tendsto_cocompact, hadj] with
      ω htail hloc hη hp hadj
    intro hω
    exact htail ε hεU (hloc ε hε0) (S.mult_succ_ne_zero hε0.le ω) hmpos hη.1 hp
      (hadj ε hε0) hω.1 hω.2
  · intro r χ hr hχ
    obtain ⟨C, hC, U, hU, hmean⟩ := hmean ρ ρ' a β r χ hρ hρρ' ha hβ hr hχ
    refine ⟨C, hC, ?_⟩
    filter_upwards [hU, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδm)] with ε hεU hε hεδm
    have hε0 : 0 < ε := hε
    have hmpos : 0 < S.mε ε :=
      (mul_pos (inv_pos.mpr hMpos) (inv_pos.mpr hε0)).trans_le (hms ε hε0 hεδm).1
    filter_upwards [hmean, hloc, hS.isAreaParametrized, hS.ae_tendsto_cocompact, hadj] with
      ω hmean hloc hη hp hadj
    intro hω z ψ H v hball hψ hv
    exact hmean ε hεU z ψ H v hball hψ (hloc ε hε0) (S.mult_succ_ne_zero hε0.le ω)
      hmpos hη.1 hp hv (hadj ε hε0) hω.1 hω.2

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.exists_joint_good_event_sameWalk_rates
