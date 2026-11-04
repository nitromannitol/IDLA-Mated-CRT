import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudeProb
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudeAsymptotic
import MatedCRT.Proofs.Infra.Setting

/-! High-probability final crude confinement of the stopped cluster. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric HarmonicBalls Filter Topology

/-- On a polynomially high-probability event, an intermediate cluster whose boundary
odometer is at most `ε ^ (-ω₀)` confines the stopped cluster within any fixed positive
distance. The stopped cluster's closure must meet the ball cellwise so that Lemma 2.8
applies to its boundary cells. -/
theorem crude_confinement_fixed_radius_polyHighProb (𝒮 : SpaceFillingSLEModel)
    (hcell : CellSizeEstimateStmt 𝒮) (hcrude : CrudeUpperBoundStmt 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (ζ ρ ω₀ δ : ℝ)
    (hζ : 0 < ζ) (hζ1 : ζ < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hω : 0 < ω₀) (hωα : ω₀ < 2 / (2 + γ) ^ 2 - ζ) (hδ : 0 < δ)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (t : ℝ) (ht : 0 < t) :
    PolyHighProb S.P fun ε => {ω |
      let m := S.mult ε ω
      let η := S.η ω
      let A := matedDiscreteCluster m ε η ρ t
      ∀ Θ : Set ℤ, (0 : ℤ) ∈ Θ →
        vClosure m A ⊆ cellVertices ε η (ball 0 ρ) →
        (∀ c ∈ vBoundary m Θ, stoppedOdometer m ε η ρ t c ≤ ε ^ (-ω₀)) →
        fillCells ε η (insert 0 (vClosure m A)) ⊆ cthickening δ (fillCells ε η (vClosure m Θ))} := by
  have hα : 0 < 2 / (2 + γ) ^ 2 - ζ := lt_trans hω hωα
  have hlim := tendsto_crude_confinement_radius hα hωα
  have hev := (tendsto_order.1 hlim).2 δ hδ
  obtain ⟨ε₀, hε₀, hsmall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  apply polyHighProb_of_inter_subset
    (crude_confinement_polyHighProb 𝒮 hcell hcrude hadj γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω S hS t ht)
    (G := univ) (by simp) hε₀
  intro ε hε hε₀' ω hωgood
  obtain ⟨hgood, _⟩ := hωgood
  dsimp only at hgood ⊢
  intro Θ hzero hA hbound
  have hcontain := hgood Θ (ε ^ (-ω₀)) hzero (Real.rpow_nonneg hε.le _) hA hbound
  have hcontain' := hcontain.trans (cthickening_mono (hsmall ⟨hε, hε₀'⟩).le _)
  intro z hz
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
  rcases ha with rfl | ha
  · exact Metric.self_subset_cthickening _ (mem_iUnion₂.mpr ⟨0, Or.inl hzero, hza⟩)
  · exact hcontain' (mem_iUnion₂.mpr ⟨a, ha, hza⟩)

end MatedCRT.Sec7
