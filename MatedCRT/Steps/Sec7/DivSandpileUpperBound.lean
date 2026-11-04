import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section4
import MatedCRT.Draft.Section6
import MatedCRT.Draft.Section7
import MatedCRT.Steps.Infra.MatingOfTrees
import MatedCRT.Proofs.Sandpile.Witness

/-!
# Proposition 7.1: reduction to stopped-shell localization

The unresolved shell iteration and its probability estimates are isolated as a step.
The passage from the stopped cluster to the global sandpile cluster is deterministic.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The stopped-shell localization needed in the proof of Proposition 7.1. This step
includes the obstacle setting, the graph closure condition, interior containment of the
stopped cluster, and localization of its graph closure with the origin inserted. It remains
to establish these assertions from the numbered estimates and the mating-of-trees step. -/
def StoppedShellLocalizationStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConeHarmonicBallsStmt → ConstantOrderLowerBoundDivStmt 𝒮 → VolumeGrowthStmt →
  MassBoundOdometerStmt 𝒮 → ConvergenceDivisibleStmt 𝒮 →
  UniformConvergenceGreenKernelStmt 𝒮 → CellSizeEstimateStmt 𝒮 →
  OdometerBoundMassStmt 𝒮 → CrudeUpperBoundStmt 𝒮 → AdjacentCellsMeetAeStep 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε =>
      {ω | IsMatedObstacleSetting (S.mult ε ω) ε (S.η ω) ρ t ∧
        vClosure (S.mult ε ω) (ballInterior ε (S.η ω) ρ) ⊆
          cellVertices ε (S.η ω) (closedBall 0 ρ) ∧
        matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆
          vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) ∧
        fillCells ε (S.η ω)
          (insert 0 (vClosure (S.mult ε ω)
            (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) ⊆
          outerNbhd δ (Λ ω t)}

/-- Proposition 7.1 follows from stopped-shell localization and the numbered estimates
used to establish that localization. -/
theorem divSandpileUpperBound_of_steps (𝒮 : SpaceFillingSLEModel)
    (hcone : ConeHarmonicBallsStmt) (hlower : ConstantOrderLowerBoundDivStmt 𝒮)
    (hvolume : VolumeGrowthStmt) (hmass : MassBoundOdometerStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hodo : OdometerBoundMassStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮)
    (hloc : StoppedShellLocalizationStep 𝒮) : DivSandpileUpperBoundStmt 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have hlocal := hloc hcone hlower hvolume hmass hconv hgreen hcell hodo hcrude hadj
    γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ δ t hδ hδρ ht
  unfold TendsToOneOn at hlocal ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlocal
    (Eventually.of_forall fun _ => bot_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono
  intro ω hbad
  refine ⟨hbad.1, ?_⟩
  intro hgood
  obtain ⟨hsetting, hclosure, hinterior, hfill⟩ := hgood
  have hsubset := Sandpile.global_cluster_subset_stopped_closure hsetting hclosure hinterior
  apply hbad.2
  intro z hz
  rcases Set.mem_iUnion.mp hz with ⟨a, ha⟩
  rcases Set.mem_iUnion.mp ha with ⟨haD, hz⟩
  apply hfill
  exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨hsubset haD, hz⟩⟩

end MatedCRT
