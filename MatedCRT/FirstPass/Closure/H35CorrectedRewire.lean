import MatedCRT.FirstPass.S4d
import MatedCRT.FirstPass.S4S6c
import MatedCRT.FirstPass.S3g
import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S2b
import MatedCRT.FirstPass.S5r.ExistsCorrected
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.Closure.CellRewire
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.Proofs.Measurability.BoundaryLayer
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.ClusterCriterion
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final

/-! # Consumers of Lemma 3.5 bound to its corrected form

The printed Lemma 3.5 (`DiscreteDirichletProblemStmt`, Draft/Section3.lean:132) is concluded by no counted
theorem; the counted theorem is the corrected form `DiscreteDirichletProblemCorrectedStmt`
(Draft/Section3DirichletCorrected.lean:13, concluded by `closed_3_5`, Closure/Section3.lean:68).
The copies below bind the corrected form. They obtain the printed form by the bridge
`FirstPass35Bridge.discreteDirichletProblem_of_corrected` (FirstPass/S3g.lean:49), which takes the
cell-size estimate `CellSizeEstimateStmt` and the discrete maximum principle `MaximumPrincipleStmt`
(`closed_2_13_cellRewire`, Closure/CellRewire.lean:21) as further inputs. The originals are unchanged.

Proposition 4.2 also binds the corrected Lemma 2.4 `ConeHarmonicBallsUpToFixedTimeCorrectedStmt`
(FirstPass/S2b.lean:43) in place of the Draft `ConeHarmonicBallsUpToFixedTimeStmt` (Draft/Section2.lean:66).
-/

namespace MatedCRT

open MeasureTheory Set

/-- Lemma 4.1 (`ConvergenceDivisibleStmt`), own-binder form `firstPass_4_1_ownBinders`
(Closure/OwnBinderRewire.lean:211), with the binder `h35` replaced by the corrected Lemma 3.5
`DiscreteDirichletProblemCorrectedStmt`. The cell-size estimate is `CertifiedReferenceModel.cellSizeEstimate hC`. -/
theorem firstPass_4_1_ownBinders_h35c (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hm : MepsScalingInput 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  firstPass_4_1_ownBinders 𝒮 ν hC hBG hm
    (FirstPass35Bridge.discreteDirichletProblem_of_corrected (CertifiedReferenceModel.cellSizeEstimate hC)
      closed_2_13_cellRewire h35c) hH hcone

/-- Lemma 4.1 (`ConvergenceDivisibleStmt`), repaired form `firstPass_4_1_coneLaw` (FirstPass/S4S6c.lean:45, with the
frozen input `FrozenConeScalingLaw` in place of the false `FrozenConeEnvironmentScaling`), with the binder `h35`
replaced by `DiscreteDirichletProblemCorrectedStmt`. -/
theorem firstPass_4_1_coneLaw_h35c {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h27 : VolumeGrowthStmt) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hcone : FrozenConeScalingLaw 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  firstPass_4_1_coneLaw hm h210 h34 h214 h28
    (FirstPass35Bridge.discreteDirichletProblem_of_corrected h28 closed_2_13_cellRewire h35c)
    h218 h27 hH hcone

/-- Lemma 4.1 (`ConvergenceDivisibleStmt`) with the Lemma 3.5 binder discharged by the counted corrected form
`closed_3_5` (Closure/Section3.lean:66). That form takes the frozen input `hexc : FrozenBrownianOutwardExcursionAtExit`
(through `closed_3_6_corrected`), which `firstPass_4_1_ownBinders` does not bind; it is therefore a binder here. -/
theorem firstPass_4_1_ownBinders_counted (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  firstPass_4_1_ownBinders_h35c 𝒮 ν hC hBG hm
    (closed_3_5 ν hC (volumeGrowthStmt_of_berestyckiGwynne hBG) hexc) hH hcone

/-- **Lemma 4.6** (`SubsequentialConvergencePreparedStmt`), with the binder `h35` (`DiscreteDirichletProblemStmt`)
replaced by the corrected Lemma 3.5 `DiscreteDirichletProblemCorrectedStmt`. The bridge input is the cell-size
estimate `h28 : CellSizeEstimateStmt 𝒮` (cited Lemma 2.8, BG20 Lemma 2.4; the same class as `h28` in `firstPass_5_2`,
FirstPass/S5S6S7.lean:36), which is added as a binder. `firstPass_4_6_corrected` (FirstPass/S3S4.lean:102) is unchanged. -/
theorem firstPass_4_6_h35c {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) :
    SubsequentialConvergencePreparedStmt 𝒮 :=
  firstPass_4_6_corrected hm h27 h218 hH
    (FirstPass35Bridge.discreteDirichletProblem_of_corrected h28 closed_2_13_cellRewire h35c) h37

/-! ### Proposition 4.2 with the corrected Lemma 2.4

Along the chain of Proposition 4.2 the Draft Lemma 2.4 is used only through its existence clause
`∃ T, 0 < T ∧ ∃ Λ, IsConeHarmonicBallFamilyOn (μ ω) Λ T ∧ IsStoppedAtHalfBall Λ T`: the measurability lemma
`exists_measurable_familyProcess` (Proofs/Measurability/BoundaryLayer.lean:369) binds `⟨T, hT, Λ', hΛ', hstop, -⟩`, and
`coneStoppedBaseExists_of_draft` (FirstPass/S4d/GlobalMeasurable.lean:156) does the same. The stopping-time uniqueness
clause `T' = T` (Draft/Section2.lean:66) is therefore not used, and the corrected form `ConeHarmonicBallsUpToFixedTimeCorrectedStmt`
(FirstPass/S2b.lean:43) can replace `h24` at every level below. The bodies are those of the originals; the measurability
input is `exists_measurable_familyProcess_corrected` (FirstPass/S5r/ExistsCorrected.lean:18). -/

section ChainH24c

open Set Metric MeasureTheory Filter _root_.HarmonicBalls

/-- `MatedCRTEnv.IsValid.nullMeasurableSet_lt_clusterExitTime` (Proofs/Measurability/BoundaryLayer.lean:402) with
the corrected Lemma 2.4 `h24c`. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_lt_clusterExitTime_h24c {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hfam : ConeFamilyAEMeasurableStep) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) {t : ℝ}
    (ht : 0 < t) : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P := by
  obtain ⟨X, hXm, hX⟩ := hS.exists_measurable_familyProcess_corrected hγ hγ2 hfam h24c
  refine (measurableSet_exitTest hXm t ρ).nullMeasurableSet.congr ?_
  filter_upwards [hΛ, hX] with ω hΛω hXω
  obtain ⟨T, Λ', hT, hΛ', hstop, hXω⟩ := hXω
  exact propext (lt_clusterExitTime_iff_of_familyProcess hΛω hT hΛ' hstop hXω hρ hρ1 ht).1.symm

/-- `innerNbhd_coverage_of_subset_cluster` (Proofs/Sec4/DivSandpileLowerBound/ClusterCriterion.lean:73) with the
corrected Lemma 2.4 `h24c`; the proof is that of the original, with the null-measurability input taken from
`nullMeasurableSet_lt_clusterExitTime_h24c`. -/
theorem innerNbhd_coverage_of_subset_cluster_h24c (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hfam : ConeFamilyAEMeasurableStep) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t)
    (hcluster : ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
      innerNbhd δ (Λ ω t) ⊆ cluster (S.μ ω) ρ 0 t) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      (fun ε => {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}) := by
  have hexit := hS.nullMeasurableSet_lt_clusterExitTime_h24c hγ hγ' hfam h24c hρ hρ' hΛ ht
  apply innerNbhd_coverage_of_strict_gap_of_volumeGrowth 𝒮 h41 h33 h28 h27
    γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ δ t hδ ht hexit
  have hc : 0 < S.c₀ / 6 := matedCRTScalingConstantPositive 𝒮 γ hγ hγ' Ω S hS
  filter_upwards [hΛ, hS.isLQGMeasure, hcluster] with ω hω hμ hcl hT
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  have hsub := (coneFamily_innerNbhd_compact_subset hω hρ ht hT hδ).2
  have hsub' : innerNbhd δ (Λ ω t) ⊆ ball 0 ρ :=
    hsub.trans (closedBall_subset_ball (by linarith))
  exact (subset_cluster_iff_scaled_strict_gap hc hsub').mp (hcl hT)

/-- `obstacleClusterInnerApproximation_of_strictGap` (Proofs/Sec4/DivSandpileLowerBound/Final.lean:41) with `h24c`. -/
theorem obstacleClusterInnerApproximation_of_strictGap_h24c (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hfam : ConeFamilyAEMeasurableStep) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮) : ObstacleClusterInnerApproximationStep 𝒮 := by
  intro h41 _ _ h33 h28 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ _ ht
  refine innerNbhd_coverage_of_subset_cluster_h24c 𝒮 h41 h33 h28 h27 hfam h24c γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ ht ?_
  filter_upwards [hgap γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht] with ω hω hT
  exact fun x hx => hω hT hx.1

/-- `discreteClusterInnerBound_final` (Proofs/Sec4/DivSandpileLowerBound/Final.lean:73) with `h24c`. -/
theorem discreteClusterInnerBound_final_h24c (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hfam : ConeFamilyAEMeasurableStep)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮) : DiscreteClusterInnerBoundStep 𝒮 :=
  discreteClusterInnerBound_of_steps 𝒮 (obstacleClusterInnerApproximation_of_strictGap_h24c 𝒮 h27 hfam h24c hgap)
    h41 h23 (maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)) h33 h28

/-- `divSandpileLowerBound_final` (Proofs/Sec4/DivSandpileLowerBound/Final.lean:81) with `h24c`. -/
theorem divSandpileLowerBound_final_h24c (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hfam : ConeFamilyAEMeasurableStep)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮) : DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_of_discreteClusterInnerBound 𝒮
    (discreteClusterInnerBound_final_h24c 𝒮 h41 h23 h24c h27 h28 h33 hfam hgap)

/-- `firstPass_4_2_of_coneFamilyStep` (FirstPass/S4d.lean:37) with `h24c`; the Lemma 3.5 binder stays the Draft form
(it is consumed by `firstPass_4_1`). -/
theorem firstPass_4_2_of_coneFamilyStep_h24c {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) :
    DivSandpileLowerBoundStmt 𝒮 :=
  divSandpileLowerBound_final_h24c 𝒮 (firstPass_4_1 hm h210 h34 h214 h28 h35 h218 h27 hH hcone) h23 h24c h27 h28 h33
    hfam hgap

/-- `firstPass_4_2_of_strictGapSteps` (FirstPass/S4d.lean:58) with `h24c`. -/
theorem firstPass_4_2_of_strictGapSteps_h24c {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hdet : StrictGapDeterministicComparisonStep) (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_coneFamilyStep_h24c hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24c h33
    (harmonicBallStrictObstacleGapStep_of_steps 𝒮 hdet hnj) hfam

/-- `firstPass_4_2_of_frozen_strictGap` (FirstPass/S4d.lean:110) with `h24c`. -/
theorem firstPass_4_2_of_frozen_strictGap_h24c {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_strictGapSteps_h24c hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24c h33
    (strictGapDeterministicComparison_of_frozen hG hpc hsmp hwmp hpole) hnj hfam

end ChainH24c

/-- Proposition 4.2 (`DivSandpileLowerBoundStmt`), final form `firstPass_4_2_final` (FirstPass/S4d.lean:146), with the
binder `h35` replaced by the corrected Lemma 3.5 `DiscreteDirichletProblemCorrectedStmt` and the binder `h24` replaced by
the corrected Lemma 2.4 `ConeHarmonicBallsUpToFixedTimeCorrectedStmt`. The bridge input is `h28`. The binder
`hcone : FrozenConeEnvironmentScaling 𝒮` is kept from `firstPass_4_2_final`; it is documented FALSE (FirstPass/S3S4.lean:27,
FirstPass/S4S6c.lean:7). All other binders and the conclusion are those of `firstPass_4_2_final`. -/
theorem firstPass_4_2_final_h35c {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_frozen_strictGap_h24c hm h210 h34 h214 h28
    (FirstPass35Bridge.discreteDirichletProblem_of_corrected h28 closed_2_13_cellRewire h35c)
    h218 h27 hH hcone h23 h24c h33 hG hpc hsmp hwmp hpole hnj
    (coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22)

#print axioms firstPass_4_1_coneLaw_h35c
#print axioms firstPass_4_1_ownBinders_h35c
#print axioms firstPass_4_1_ownBinders_counted
#print axioms firstPass_4_6_h35c
#print axioms firstPass_4_2_final_h35c

end MatedCRT
