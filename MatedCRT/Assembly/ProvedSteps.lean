import MatedCRT.FirstPass.S4S5b
import MatedCRT.FirstPass.S5c.FinalSurplus
import MatedCRT.FirstPass.S3S4c
import MatedCRT.FirstPass.S3t.CellGeometry
import MatedCRT.FirstPass.S3t.BLEnvelopeClosure
import MatedCRT.FirstPass.Closure.HLsRewire53
import MatedCRT.FirstPass.Closure.Steps42
import MatedCRT.FirstPass.Closure.HSCDerived
import MatedCRT.FirstPass.Derived.HBBallMassHolds
import MatedCRT.FirstPass.Derived.LQGMeasureInputs
import MatedCRT.FirstPass.Derived.DiscGreenCentre
import MatedCRT.FirstPass.Derived.ConeLogLocalCodeLawStdDerived
import MatedCRT.FirstPass.Derived.InsertionCoordinateRule
import MatedCRT.FirstPass.Derived.ConeCircleLawUnique
import MatedCRT.FirstPass.Derived.ConeReferenceExistsDerived
import MatedCRT.FirstPass.Derived.ConeDilationRatioHolds
import MatedCRT.FirstPass.Derived.RevuzOccupationHolds
import MatedCRT.FirstPass.Derived.QuantumConeScalingDerived
import MatedCRT.FirstPass.LPBridge.PairingLawIG4
import MatedCRT.FirstPass.LPBridge.InRepoProofs
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion
import MatedCRT.FirstPass.Derived.CoreExitTimeFromBG20
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd
import MatedCRT.FirstPass.Derived.HarmonicBallsVolumeGrowth
import MatedCRT.Proofs.Sec4.Prop42Closure.LQGMeasureLocalityProof
import MatedCRT.FirstPass.S5u
import MatedCRT.FirstPass.S3i.GoodEvent
import MatedCRT.FirstPass.S3c.ExitTimeBridge
import MatedCRT.FirstPass.Derived.CellInballDisjoint
import MatedCRT.FirstPass.Derived.GreenFunctionCrudeBoundHolds
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences

/-!
# Steps of `MainHypotheses` proved from the first-pass results

Three of the named steps of `MainHypotheses 𝒮` (`MatedCRT/Assembly/Hypotheses.lean`) are consequences of results
proved on the first-pass route:

* the strict obstacle gap of Propositions 4.2 and 5.1 (`HarmonicBallStrictObstacleGapStep`), for every model:
  `firstPass_strictObstacleGap` with its inputs supplied by the hypothesis-free theorems of this repository and of
  Harmonic-Balls-LQG;
* the lower surplus estimate of Lemma 5.3 (`MeanValueSurplusLowerStep`), for every model satisfying the scaling of
  the expected exit time (`MepsScalingInput`): `firstPass_5_3_step`, with the first-hit property of the curve from
  its properness, and the coded scale invariance of the cone harmonic balls from `coneScaleInvarianceCoded_ownBinders`;
* the canonical form of Berestycki-Gwynne, Lemma 5.6 (`FrozenBG20GreenCrudeCanonical`, the Green function killed on
  `V^ε(B_ρ)`), for every model: Lemma 2.15 at a larger radius `ρ' = (1 + ρ)/2` and domain monotonicity, since with
  polynomially high probability the cells meeting `B_ρ` have diameter less than `ρ' - ρ` (Lemma 2.8);
* Lemma 3.4 (`IntegralConvergenceGreenFunctionStmt`), for every model satisfying Theorem 2.11, Lemma 2.18 and the
  scaling of the expected exit time: `S3S4c.firstPass_3_4`, with the occupation identity of Appendix B
  (`KilledOccupation.frozenLBMGreenOccupationRescaled_holds`) and the truncated quenched laws
  (`TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs`).

## Main statements

* `harmonicBallStrictObstacleGapStep_holds`
* `fpFirstHitVisits_holds`
* `coneScaleInvarianceCodedStmt_holds`
* `meanValueSurplusLowerStep_of_meps`
* `frozenBG20GreenCrudeCanonical_holds`
* `integralConvergenceGreenFunction_of_walk`
-/

set_option autoImplicit false

open MeasureTheory Metric Set Filter _root_.HarmonicBalls

namespace MatedCRT

/-- **The strict obstacle gap** (eq:strictly-above-in-interior, Propositions 4.2 and 5.1) for every model. -/
theorem harmonicBallStrictObstacleGapStep_holds (𝒮 : SpaceFillingSLEModel) : HarmonicBallStrictObstacleGapStep 𝒮 :=
  have d10 := FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  firstPass_strictObstacleGap 𝒮 (HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d10))
    (HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only (hI2 := d10))
    FirstPass.Derived.frozenTypicalPointManyGoodScales_holds d10
    (volumeGrowthStmt_of_berestyckiGwynne (hBG := FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds))
    (FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence
      (hE := FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds))
    ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds LQGMeasureLocalityFunctionalStep_proof
    fpPairingLawIG4_holds

/-- **The first-hit property of the space-filling curve** (Duplantier-Miller-Sheffield, Lemma 8.11) for every model:
the curve of a valid environment is almost surely proper, so the preimage of each point is compact. -/
theorem fpFirstHitVisits_holds (𝒮 : SpaceFillingSLEModel) : FPFirstHitVisits 𝒮 :=
  fun _ _ _ _ _ _ hS =>
    hS.ae_tendsto_cocompact.mono fun _ hp x => TruncatedLaws.cellGeom_bddBelow_preimage hp x

/-- **Coded scale invariance of the cone harmonic balls** (Lemma 2.6, coded form), with no hypothesis. -/
theorem coneScaleInvarianceCodedStmt_holds : ConeScaleInvarianceCodedStmt :=
  have d10 := FirstPass.Derived.frozenLQGVolumeGrowthAllScales_holds
  have d3 := FirstPass.Derived.existenceHarmonicBallsStmt_holds
  have d4 := FirstPass.Derived.frozenBerestyckiGwynneConeBallMass_holds
  have d21 := uniquenessHarmonicBallsStmt_of_volumeGrowth (hI2 := d10)
  have hcan : ConeCanonicalHalfBallStep :=
    FirstPassClosure.coneCanonicalHalfBallStep_proof FirstPass.Derived.frozenConeLogLocalCodeLawStd_holds
      frozenGreenBallCentre_holds (HarmonicBalls.clusterOpenLaplacian_proved (hI2 := d10))
      (HarmonicBalls.leastSupersolutionMem_proved (hI2 := d10))
      (HarmonicBalls.clusterConservationOfMass_proved (hI2 := d10))
      (HarmonicBalls.clusterMonotone_proved (hI2 := d10)) (HarmonicBalls.clusterCompatibility_proved (hI2 := d10))
      FirstPass.Derived.frozenClusterBoundaryMeasureZero_holds d3
      (HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5 (h55 := d3) (h56 := d21)) d21
      FirstPass.Derived.frozenHBInitialConfinement_holds d10 FirstPass.Derived.frozenInsertionCoordinateRule_holds
      FirstPass.Derived.harmonicBallLocalSetStmt_holds (frozenClusterStrongCompatibility_of_volumeGrowth d10)
      FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
      ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds d4
  have hcl : ConeHalfBallClosureInsideStep :=
    FirstPassClosure.coneHalfBallClosureInsideStep_proof d10 FirstPass.Derived.frozenInsertionCoordinateRule_holds
      FirstPass.Derived.harmonicBallLocalSetStmt_holds d3 FirstPass.Derived.frozenLQGMeasureExistenceInsertion_holds
      ConeWholePlaneFieldLaw.coneWholePlaneFieldLawStep_holds d4
  coneScaleInvarianceCoded_ownBinders d4 FirstPass.Derived.lqgMeasureNonDyadicDilationPart_holds
    FirstPass.Derived.quantumConeScalingInput_derived hcan hcl coneCircleLawUniqueStep_holds
    FirstPass.Derived.coneReferenceExistsStep_holds

/-- **Lemma 5.3, lower surplus estimate**, for every model satisfying the scaling of the expected exit time. -/
theorem meanValueSurplusLowerStep_of_meps {𝒮 : SpaceFillingSLEModel} (hM : MepsScalingInput 𝒮) :
    MeanValueSurplusLowerStep 𝒮 :=
  firstPass_5_3_step (frozenLQGMeasureFieldMeasurable_holds 𝒮) frozenUniversalMeasurabilityOfAnalytic_holds
    frozenDiskGreenNonnegCont_holds HBRewire.FrozenGreenDiscPole_of_hb fpStrongMinimumPrinciple_holds
    coneScaleInvarianceCodedStmt_holds (coneScaleRadiusPosStep_of_input FirstPass.Derived.quantumConeScalingInput_derived)
    (fpFirstHitVisits_holds 𝒮) hM

/-- **Lemma 3.4** (convergence of integrals of the Green function) for every model satisfying Theorem 2.11, Lemma 2.18
and the scaling of the expected exit time. -/
theorem integralConvergenceGreenFunction_of_walk {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hM : MepsScalingInput 𝒮) : IntegralConvergenceGreenFunctionStmt 𝒮 :=
  S3S4c.firstPass_3_4 FirstPass.Derived.volumeGrowthStmt_holds h218 hM
    (KilledOccupation.frozenLBMGreenOccupationRescaled_holds 𝒮)
    (TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs h211 (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮) hM
      frozenBrownianOutwardExcursionAtExit_holds)

/-- **Berestycki-Gwynne, Lemma 5.6, canonical form** (`FrozenBG20GreenCrudeCanonical`) for every model: with
polynomially high probability, `G^ε_{V^ε(B_ρ)}(a, b) ≤ ε^{-ζ}` for `a, b ∈ V^ε(B_ρ)`. With `ρ' = (1 + ρ)/2`, Lemma 2.15
bounds the Green function killed on `V^ε(B_ρ') \ V^ε(∂B_ρ')`; when the cells meeting `B_ρ` have diameter less than
`ρ' - ρ` (Lemma 2.8, polynomially high probability), `V^ε(B_ρ)` is contained in that set, and the Green function
increases with the killing set (`greenFn_mono_of_firstStep`). -/
theorem frozenBG20GreenCrudeCanonical_holds (𝒮 : SpaceFillingSLEModel) : FrozenBG20GreenCrudeCanonical 𝒮 := by
  intro γ hγ0 hγ2 ρ ζ hρ0 hρ1 hζ0 hζ1 Ω _ S hS
  have hρ'0 : 0 < (1 + ρ) / 2 := by linarith
  have hρ'1 : (1 + ρ) / 2 < 1 := by linarith
  have hδ : 0 < (1 + ρ) / 2 - ρ := by linarith
  have he0 : 0 < 2 / (2 + γ) ^ 2 := by positivity
  have he2 : 2 / (2 + γ) ^ 2 < 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hG := greenFunctionCrudeBoundStmt_holds 𝒮 γ hγ0 hγ2 ((1 + ρ) / 2) ζ hρ'0 hρ'1 hζ0 hζ1 Ω S hS
  have hC := FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮 γ hγ0 hγ2 (2 / (2 + γ) ^ 2 / 2) ρ (half_pos he0)
    (by linarith) hρ0 hρ1 Ω S hS
  have hq : ∀ᵐ ω ∂S.P, (Continuous (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)) ∧
      ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω) := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      MatedCRTEnv.IsValid.ae_isLocallyFiniteMult hγ0 hγ2 hS (adjacentCellsMeetAeStep 𝒮)] with ω hap hp hlf
    exact ⟨⟨hap.1, hp⟩, hlf⟩
  refine S3cBridge.polyHighProb_mono_ae_small (r₁ := ((1 + ρ) / 2 - ρ) ^ (2 / (2 + γ) ^ 2 / 2)⁻¹)
    (by positivity) (FirstPass36.polyHighProb_inter hG hC) hq ?_
  intro ε hε hεr ω hω hqω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨hωG, hωC⟩ := hω
  have hsmall : ε ^ (2 / (2 + γ) ^ 2 - 2 / (2 + γ) ^ 2 / 2) < (1 + ρ) / 2 - ρ := by
    have he : 2 / (2 + γ) ^ 2 - 2 / (2 + γ) ^ 2 / 2 = 2 / (2 + γ) ^ 2 / 2 := by ring
    rw [he]
    calc ε ^ (2 / (2 + γ) ^ 2 / 2)
        < (((1 + ρ) / 2 - ρ) ^ (2 / (2 + γ) ^ 2 / 2)⁻¹) ^ (2 / (2 + γ) ^ 2 / 2) :=
          Real.rpow_lt_rpow hε.le hεr (half_pos he0)
      _ = (1 + ρ) / 2 - ρ := Real.rpow_inv_rpow hδ.le (half_pos he0).ne'
  have hsub : cellVertices ε (S.η ω) (ball 0 ρ) ⊆ interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)) := by
    intro k hk
    obtain ⟨z, hzc, hzb⟩ := hk
    have hdiam := (hωC k ⟨z, hzc, hzb⟩).2
    have hz : ‖z‖ < ρ := mem_ball_zero_iff.1 hzb
    have hcellsub : ∀ x ∈ cell ε (S.η ω) k, ‖x‖ < (1 + ρ) / 2 := by
      intro x hx
      have h1 : dist x z ≤ diam (cell ε (S.η ω) k) := dist_le_diam_of_mem (isBounded_cell hqω.1.1 k) hx hzc
      have h2 : ‖x‖ ≤ ‖z‖ + dist x z := by
        rw [dist_eq_norm]
        calc ‖x‖ = ‖z + (x - z)‖ := by rw [add_sub_cancel]
          _ ≤ ‖z‖ + ‖x - z‖ := norm_add_le _ _
      linarith
    refine ⟨⟨z, hzc, mem_ball_zero_iff.2 (by linarith)⟩, ?_⟩
    rintro ⟨x, hxc, hxf⟩
    rw [frontier_ball (0 : ℂ) hρ'0.ne', mem_sphere_zero_iff_norm] at hxf
    linarith [hcellsub x hxc]
  have hA : (cellVertices ε (S.η ω) (ball 0 ρ)).Finite := cellVertices_ball_finite_of_proper hqω.1.1 hqω.1.2 hε 0 ρ
  have hB : (interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))).Finite :=
    (cellVertices_ball_finite_of_proper hqω.1.1 hqω.1.2 hε 0 ((1 + ρ) / 2)).subset Set.sdiff_subset
  have hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := fun k => S.mult_succ_ne_zero hε.le ω k
  have hlf := hqω.2 ε hε
  intro a ha b hb
  exact (greenFn_mono_of_firstStep hlf hcons hA hsub (fun c => WalkPotential.mLaplacian_greenFn hlf hcons hA c)
    (fun c => WalkPotential.mLaplacian_greenFn hlf hcons hB c) a b).trans (hωG a (hsub ha).1 b (hsub hb).1)

end MatedCRT
