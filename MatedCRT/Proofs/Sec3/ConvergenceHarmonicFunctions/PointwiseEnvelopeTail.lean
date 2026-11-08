import MatedCRT.Steps.Sec3.PointwiseAnnulusEnvelope
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSEventualRate
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.External.SLE

/-! # Almost-everywhere tail rate on a pointwise environment event -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The pointwise geometric envelope carries the quenched tail estimate
almost everywhere at each small mesh. -/
theorem MatedCRTEnv.IsValid.tail_on_pointwise_cellAnnulus_envelope
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ ρ' a β p κ : ℝ} (hS : S.IsValid 𝒮 γ)
    (henv : PointwiseCellAnnulusEnvelopeStep S ρ' a β p κ)
    (hm : MepsScalingInput 𝒮) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hp : 0 < p) (hp1 : p < 1) (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (ha : 0 < a) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ E : ℝ → Set Ω,
      (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
      (∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        S.P (E ε)ᶜ ≤ ENNReal.ofReal (D * ε ^ κ)) ∧
      ∀ (χ : ℝ≥0) (q : ℝ), 0 < χ → 0 < q → q / (χ : ℝ) < min a β →
        ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ ω ∂S.P, ω ∈ E ε →
          ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
          ∀ (ψ : ℂ → ℝ) (H : ℝ≥0), HolderOnWith H χ ψ (closedBall z r) →
          ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
            srwLaw (S.mult ε ω) v
              {path | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω path} ≤
            ENNReal.ofReal (((2 : ℝ) ^ ν * (202 : ℝ) ^ ν) *
              ε ^ ((min a β - q / (χ : ℝ)) * ν)) := by
  obtain ⟨E, hEm, D, δ, hD, hδ, hE⟩ := henv
  obtain ⟨ν, hν, htail⟩ := hS.uniform_mesh_ae_sameWalkExitDiscrepancy_le_of_gms hγ hγ2 hp hp1
  obtain ⟨M, hM, hms⟩ := hm γ hγ hγ2
  obtain ⟨δm, hδm, hms⟩ := hms Ω S hS
  have hMpos : 0 < M := by linarith
  have hloc := hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)
  have hadj := adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS
  refine ⟨ν, hν, E, hEm, ⟨D, δ, hD, hδ, fun ε he hs => (hE ε he hs).1⟩, ?_⟩
  intro χ q hχ hq hqbound
  obtain ⟨U, hU, htail⟩ := htail a β ρ ρ' q χ hρ hρρ' ha hχ hq hqbound
  filter_upwards [hU, self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ),
    nhdsWithin_le_nhds (Iio_mem_nhds hδm)] with ε hεU hε hεδ hεδm
  have hmpos : 0 < S.mε ε :=
    (mul_pos (inv_pos.mpr hMpos) (inv_pos.mpr hε)).trans_le (hms ε hε hεδm).1
  filter_upwards [htail, hloc, hS.isAreaParametrized, hS.ae_tendsto_cocompact, hadj] with
    ω htail hloc hη hproper hadj
  intro hω
  have hgeom := (hE ε hε hεδ).2 ω hω
  exact htail ε hεU (hloc ε hε) (S.mult_succ_ne_zero hε.le ω) hmpos hη.1 hproper
    (hadj ε hε) hgeom.1 hgeom.2

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.tail_on_pointwise_cellAnnulus_envelope
