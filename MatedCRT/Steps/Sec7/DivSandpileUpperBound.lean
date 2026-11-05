import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section4
import MatedCRT.Draft.Section6
import MatedCRT.Draft.Section7
import MatedCRT.Steps.Sec6.ConstantOrderLowerBoundDiv
import MatedCRT.Steps.Sec7.MassBoundOdometer
import MatedCRT.Steps.Infra.MatingOfTrees
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sandpile.Witness
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Geometry
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Interior
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellGeometry

/-!
# Proposition 7.1: reduction to stopped-shell localization

The unresolved shell iteration and its probability estimates are isolated as a step.
The passage from the stopped cluster to the global sandpile cluster is deterministic.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls

/-- The stopped-shell localization needed in the proof of Proposition 7.1. This step
includes the obstacle setting, interior containment of the
stopped cluster, and localization of its graph closure with the origin inserted. It remains
to establish these assertions from the numbered estimates and the mating-of-trees step. -/
def StoppedShellLocalizationStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConeHarmonicBallsStmt → ConstantOrderLowerBoundDivLogStmt 𝒮 → VolumeGrowthStmt →
  MassBoundOdometerAboveScaleStmt 𝒮 → ConvergenceDivisibleStmt 𝒮 →
  UniformConvergenceGreenKernelStmt 𝒮 → CellSizeEstimateStmt 𝒮 →
  OdometerBoundMassStmt 𝒮 → CrudeUpperBoundStmt 𝒮 → AdjacentCellsMeetAeStep 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε =>
      {ω | IsMatedObstacleSetting (S.mult ε ω) ε (S.η ω) ρ t ∧
        matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆
          vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) ∧
        fillCells ε (S.η ω)
          (insert 0 (vClosure (S.mult ε ω)
            (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) ⊆
          outerNbhd δ (Λ ω t)}

/-- The finite obstacle problem on the induced cell graph satisfies the hypotheses of
the deterministic least-action comparison. -/
def StoppedObstacleSetupStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  AdjacentCellsMeetAeStep 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ProbTendsToOne S.P fun ε =>
    {ω | IsMatedObstacleSetting (S.mult ε ω) ε (S.η ω) ρ t}

/-- The stopped support stays in the graph interior, and its closure lies in the
prescribed neighborhood. This is the shell iteration and the final crude bound. -/
def StoppedShellConfinementStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConeHarmonicBallsStmt → ConstantOrderLowerBoundDivLogStmt 𝒮 → VolumeGrowthStmt →
  MassBoundOdometerAboveScaleStmt 𝒮 → ConvergenceDivisibleStmt 𝒮 →
  UniformConvergenceGreenKernelStmt 𝒮 → CellSizeEstimateStmt 𝒮 →
  OdometerBoundMassStmt 𝒮 → CrudeUpperBoundStmt 𝒮 → AdjacentCellsMeetAeStep 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε =>
      {ω | matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆
          vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) ∧
        fillCells ε (S.η ω)
          (insert 0 (vClosure (S.mult ε ω)
            (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) ⊆
          outerNbhd δ (Λ ω t)}

/-- Assemble the obstacle and confinement events by the union bound. -/
theorem stoppedShellLocalization_of_steps (𝒮 : SpaceFillingSLEModel)
    (hsetup : StoppedObstacleSetupStep 𝒮) (hshell : StoppedShellConfinementStep 𝒮) :
    StoppedShellLocalizationStep 𝒮 := by
  intro hcone hlower hvolume hmass hconv hgreen hcell hodo hcrude hadj
    γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have h1 := hsetup hadj γ hγ hγ' ρ hρ hρ' Ω S hS t ht
  have h2 := hshell hcone hlower hvolume hmass hconv hgreen hcell hodo hcrude hadj
    γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ δ t hδ hδρ ht
  unfold ProbTendsToOne at h1
  unfold TendsToOneOn at h2 ⊢
  have hlim := h1.add h2
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  calc
    _ ≤ S.P ({ω | IsMatedObstacleSetting (S.mult ε ω) ε (S.η ω) ρ t}ᶜ ∪
        ({ω | t < clusterExitTime (Λ ω) ρ} ∩
          {ω | matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆
            vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) ∧
          fillCells ε (S.η ω) (insert 0 (vClosure (S.mult ε ω)
            (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) ⊆ outerNbhd δ (Λ ω t)}ᶜ)) := by
      apply measure_mono
      intro ω hω
      by_cases h : IsMatedObstacleSetting (S.mult ε ω) ε (S.η ω) ρ t
      · right
        exact ⟨hω.1, fun hs => hω.2 ⟨h, hs⟩⟩
      · exact Or.inl h
    _ ≤ _ := measure_union_le _ _

/-- Proposition 7.1 follows from stopped-shell localization and the numbered estimates
used to establish that localization. -/
theorem divSandpileUpperBound_of_steps (𝒮 : SpaceFillingSLEModel)
    (hcone : ConeHarmonicBallsStmt) (hlower : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (hvolume : VolumeGrowthStmt) (hmass : MassBoundOdometerAboveScaleStmt 𝒮)
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
  apply eventually_nhdsWithin_of_forall
  intro ε hε
  apply measure_mono_ae
  filter_upwards [hS.isAreaParametrized, hadj γ hγ hγ' Ω S hS] with ω hη hmeet
  intro hbad
  refine ⟨hbad.1, ?_⟩
  intro hgood
  obtain ⟨hsetting, hinterior, hfill⟩ := hgood
  have hclosure := Sec7.closure_ballInterior_subset (ρ := ρ) hη.1 (hmeet ε hε)
  have hsubset := Sandpile.global_cluster_subset_stopped_closure hsetting hclosure hinterior
  apply hbad.2
  intro z hz
  rcases Set.mem_iUnion.mp hz with ⟨a, ha⟩
  rcases Set.mem_iUnion.mp ha with ⟨haD, hz⟩
  apply hfill
  exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨hsubset haD, hz⟩⟩

/-- Proposition 7.1 from the obstacle setup and stopped-shell confinement steps. -/
theorem divSandpileUpperBound_of_carved_steps (𝒮 : SpaceFillingSLEModel)
    (hcone : ConeHarmonicBallsStmt) (hlower : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (hvolume : VolumeGrowthStmt) (hmass : MassBoundOdometerAboveScaleStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hodo : OdometerBoundMassStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮)
    (hsetup : StoppedObstacleSetupStep 𝒮) (hshell : StoppedShellConfinementStep 𝒮) :
    DivSandpileUpperBoundStmt 𝒮 :=
  divSandpileUpperBound_of_steps 𝒮 hcone hlower hvolume hmass hconv hgreen hcell hodo
    hcrude hadj (stoppedShellLocalization_of_steps 𝒮 hsetup hshell)

/-- Proposition 7.1 from stopped-shell localization and the numbered inputs,
using the proved almost-sure contact of adjacent cells. -/
theorem divSandpileUpperBound_of_inputs (𝒮 : SpaceFillingSLEModel)
    (hcone : ConeHarmonicBallsStmt) (hlower : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (hvolume : VolumeGrowthStmt) (hmass : MassBoundOdometerAboveScaleStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hodo : OdometerBoundMassStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) (hloc : StoppedShellLocalizationStep 𝒮) :
    DivSandpileUpperBoundStmt 𝒮 :=
  divSandpileUpperBound_of_steps 𝒮 hcone hlower hvolume hmass hconv hgreen hcell hodo
    hcrude (adjacentCellsMeetAeStep 𝒮) hloc

/-- Proposition 7.1 from the obstacle and shell steps, with adjacent-cell
contact discharged by the mating-of-trees construction. -/
theorem divSandpileUpperBound_of_carved_inputs (𝒮 : SpaceFillingSLEModel)
    (hcone : ConeHarmonicBallsStmt) (hlower : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (hvolume : VolumeGrowthStmt) (hmass : MassBoundOdometerAboveScaleStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hodo : OdometerBoundMassStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮)
    (hsetup : StoppedObstacleSetupStep 𝒮) (hshell : StoppedShellConfinementStep 𝒮) :
    DivSandpileUpperBoundStmt 𝒮 :=
  divSandpileUpperBound_of_carved_steps 𝒮 hcone hlower hvolume hmass hconv hgreen hcell
    hodo hcrude (adjacentCellsMeetAeStep 𝒮) hsetup hshell

/-- The unresolved shell construction produces an intermediate set with a small
boundary odometer and localized filled closure on the exit-time event. -/
def IntermediateShellStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConeHarmonicBallsStmt → ConstantOrderLowerBoundDivLogStmt 𝒮 → VolumeGrowthStmt →
  MassBoundOdometerAboveScaleStmt 𝒮 → ConvergenceDivisibleStmt 𝒮 →
  UniformConvergenceGreenKernelStmt 𝒮 → CellSizeEstimateStmt 𝒮 →
  OdometerBoundMassStmt 𝒮 → AdjacentCellsMeetAeStep 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
  ∃ ζ ω₀ : ℝ, 0 < ζ ∧ ζ < 1 ∧ 0 < ω₀ ∧ ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      let m := S.mult ε ω
      let η := S.η ω
      ∃ Θ : Set ℤ, (0 : ℤ) ∈ Θ ∧
          (∀ c ∈ vBoundary m Θ, stoppedOdometer m ε η ρ t c ≤ ε ^ (-ω₀)) ∧
          fillCells ε η (vClosure m Θ) ⊆ outerNbhd (δ / 2) (Λ ω t)}

/-- The final crude estimate turns the intermediate-shell step into the full
stopped-shell confinement step. -/
theorem stoppedShellConfinement_of_intermediateShell (𝒮 : SpaceFillingSLEModel)
    (hshell : IntermediateShellStep 𝒮) : StoppedShellConfinementStep 𝒮 := by
  intro hcone hlower hvolume hmass hconv hgreen hcell hodo hcrude hadj
    γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ δ t hδ hδρ ht
  apply Sec7.stopped_interior_of_filled_localization Ω S Λ hΛ ρ t hρ ht ?_ δ hδ
  intro d hd hdρ
  obtain ⟨ζ, ω₀, hζ, hζ1, hω, hωα, hstep⟩ :=
    hshell hcone hlower hvolume hmass hconv hgreen hcell hodo hadj
      γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ d t hd hdρ ht
  exact Sec7.stopped_filled_confinement_of_intermediate_shell 𝒮 hcell hcrude hadj
    γ hγ hγ' ζ ρ ω₀ d hζ hζ1 hρ hρ' hω hωα hd Ω S hS Λ t ht _ hstep

/-- The remaining shell iteration produces a finite sequence with controlled
boundary odometer and cumulative spatial growth. The certificate only asks for
cell diameters up to the stopping index. -/
def ShellIterationStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConeHarmonicBallsStmt → ConstantOrderLowerBoundDivLogStmt 𝒮 → VolumeGrowthStmt →
  MassBoundOdometerAboveScaleStmt 𝒮 → ConvergenceDivisibleStmt 𝒮 →
  UniformConvergenceGreenKernelStmt 𝒮 → CellSizeEstimateStmt 𝒮 →
  OdometerBoundMassStmt 𝒮 → AdjacentCellsMeetAeStep 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
  ∃ ζ ω₀ : ℝ, 0 < ζ ∧ ζ < 1 ∧ 0 < ω₀ ∧ ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∃ (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ) (D : ℝ),
        0 ≤ D ∧ (∀ k < n, 0 < r k) ∧ (0 : ℤ) ∈ Θ 0 ∧
        Θ 0 ⊆ cellVertices ε (S.η ω) (Λ ω t) ∧
        (∀ k < n, Θ (k + 1) = cellVertices ε (S.η ω)
          (thickening (r k) (fillCells ε (S.η ω) (Θ k)))) ∧
        (∀ k ≤ n, ∀ a ∈ vClosure (S.mult ε ω) (Θ k), diam (cell ε (S.η ω) a) ≤ D) ∧
        (∀ a ∈ vBoundary (S.mult ε ω) (Θ n), stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a ≤ ε ^ (-ω₀)) ∧
        (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D) ≤ δ / 2}

/-- The shell-iteration certificate implies the intermediate-shell step. -/
theorem intermediateShell_of_shellIteration (𝒮 : SpaceFillingSLEModel)
    (hiteration : ShellIterationStep 𝒮) : IntermediateShellStep 𝒮 := by
  intro hcone hlower hvolume hmass hconv hgreen hcell hodo hadj
    γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨ζ, ω₀, hζ, hζ1, hω, hωα, hiteration'⟩ :=
    hiteration hcone hlower hvolume hmass hconv hgreen hcell hodo hadj
      γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ δ t hδ hδρ ht
  refine ⟨ζ, ω₀, hζ, hζ1, hω, hωα, ?_⟩
  unfold TendsToOneOn at hiteration' ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hiteration'
    (Eventually.of_forall fun _ => zero_le) ?_
  apply eventually_nhdsWithin_of_forall
  intro ε hε
  apply measure_mono_ae
  filter_upwards [hS.isAreaParametrized, hadj γ hγ hγ' Ω S hS] with ω hη hmeet
  intro hbad
  refine ⟨hbad.1, ?_⟩
  intro hcert
  obtain ⟨Θ, r, n, D, hD, hr, hzero, h0, hstep, hdiam, hbound, hbudget⟩ := hcert
  apply hbad.2
  exact Sec7.exists_localized_intermediate_shell Θ r (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) n
    hε.le hη.1 hD hr (hmeet ε hε) hzero h0 hstep hdiam hbound hbudget

end MatedCRT
