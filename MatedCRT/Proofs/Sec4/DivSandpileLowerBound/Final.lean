import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.ClusterCriterion
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.OdometerComparisonProved
import MatedCRT.Steps.Sec5.IDLALowerBound
import MatedCRT.Steps.Sec2.MaximumPrinciple

/-!
# Proposition 4.2: final form

* `HarmonicBallStrictObstacleGapStep`: before the exit time, the harmonic ball `Λ_t` lies in the (unregularized)
  obstacle cluster `{x : x = 0 ∨ obstacle < least supersolution}`, i.e. the obstacle gap is strictly positive on
  `Λ_t`. This is `eq:strictly-above-in-interior` (corrected.tex:1652-1660), whose printed proof (continuity) is invalid
  in general (E-x3-1, `StrictGapCounterexample.lean`), and the missing ingredient (2) of E-c2-5.
* `obstacleClusterInnerApproximation_of_strictGap`: the step `ObstacleClusterInnerApproximationStep` of Proposition 4.2
  from the strict gap, Lemma 2.7, cone-family measurability and Lemma 2.4 (through m4's
  `innerNbhd_coverage_of_subset_cluster`, ClusterCriterion.lean).
* `divSandpileLowerBound_of_discreteClusterInnerBound`: the `Λ^ε_t` form of Proposition 4.2
  (`DiscreteClusterInnerBoundStep`, used by Proposition 5.1) implies `DivSandpileLowerBoundStmt` (the odometer
  comparison `Λ^ε_t ⊆ D_ε(t ε⁻¹)` is proved). The converse does not hold in general (Steps/Sec5/IDLALowerBound.lean,
  point 2): `DiscreteClusterInnerBoundStep` is the stronger form and the one 5.1 needs.
* `divSandpileLowerBound_final`, `discreteClusterInnerBound_final`: Proposition 4.2 in both forms from Theorem 4.1,
  Theorem 2.3, Lemma 2.4, Lemmas 2.7, 2.8 (cited), 3.3, `ConeFamilyAEMeasurableStep` and the strict gap step.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- **Strict positivity of the obstacle gap on the harmonic ball** (eq:strictly-above-in-interior, corrected.tex
1652-1660; E-x3-1, E-c2-5 (2)): for `t > 0`, almost surely, on `{t < T}`, `Λ_t ⊆ 𝒞_t`, where `𝒞_t` is the
unregularized obstacle cluster of `μ_h` in `B_ρ` with source `0` (`HarmonicBalls.cluster`): the least supersolution
is strictly above the obstacle on `Λ_t \ {0}`. -/
def HarmonicBallStrictObstacleGapStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t →
    ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → Λ ω t ⊆ _root_.HarmonicBalls.cluster (S.μ ω) ρ 0 t

/-- `ObstacleClusterInnerApproximationStep` (Proposition 4.2, lines 1621-1670) from the strict gap, Lemma 2.7,
cone-family measurability and Lemma 2.4. -/
theorem obstacleClusterInnerApproximation_of_strictGap (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hfam : ConeFamilyAEMeasurableStep) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮) : ObstacleClusterInnerApproximationStep 𝒮 := by
  intro h41 _ _ h33 h28 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ _ ht
  refine innerNbhd_coverage_of_subset_cluster 𝒮 h41 h33 h28 h27 hfam h24 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ ht ?_
  filter_upwards [hgap γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht] with ω hω hT
  exact fun x hx => hω hT hx.1

/-- The `Λ^ε_t` form of Proposition 4.2 implies the stated one: `Λ^ε_t ⊆ D_ε(t ε⁻¹)` (the odometer comparison,
`divSandpileOdometerComparison`). -/
theorem divSandpileLowerBound_of_discreteClusterInnerBound (𝒮 : SpaceFillingSLEModel)
    (hD : DiscreteClusterInnerBoundStep 𝒮) : DivSandpileLowerBoundStmt 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have happ := hD γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ δ t hδ hδρ ht
  have hcompare := divSandpileOdometerComparison 𝒮 γ hγ hγ' ρ hρ hρ' Ω S hS
  unfold TendsToOneOn at happ ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds happ
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply measure_mono_ae
  filter_upwards [hcompare] with ω hω
  intro hbad
  refine ⟨hbad.1, ?_⟩
  intro hgood
  obtain ⟨hlf, hloop, hdeg, hne, hlower⟩ := hω t ε ht hε
  have hsubset := matedDiscreteCluster_subset_sandpileCluster hlf hloop hdeg hne hlower
  exact hbad.2 (hgood.trans (fillCells_matedDiscreteCluster_subset_sandpileCluster hsubset))

/-- **Proposition 4.2, `Λ^ε_t` form** (`DiscreteClusterInnerBoundStep`, used by Proposition 5.1) from Theorem 4.1,
Theorem 2.3, Lemma 2.4, Lemmas 2.7, 2.8 (cited), Lemma 3.3, `ConeFamilyAEMeasurableStep` and the strict gap step.
Lemma 2.13 is proved. -/
theorem discreteClusterInnerBound_final (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hfam : ConeFamilyAEMeasurableStep)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮) : DiscreteClusterInnerBoundStep 𝒮 :=
  discreteClusterInnerBound_of_steps 𝒮 (obstacleClusterInnerApproximation_of_strictGap 𝒮 h27 hfam h24 hgap) h41 h23
    (maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)) h33 h28

/-- **Proposition 4.2** from Theorem 4.1, Theorem 2.3, Lemma 2.4, Lemmas 2.7, 2.8 (cited), Lemma 3.3,
`ConeFamilyAEMeasurableStep` and the strict gap step. -/
theorem divSandpileLowerBound_final (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hfam : ConeFamilyAEMeasurableStep)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮) : DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_of_discreteClusterInnerBound 𝒮
    (discreteClusterInnerBound_final 𝒮 h41 h23 h24 h27 h28 h33 hfam hgap)

end MatedCRT
