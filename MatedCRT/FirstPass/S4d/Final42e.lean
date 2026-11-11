import MatedCRT.FirstPass.S4d.Final42
import MatedCRT.Proofs.Sec1.EnvironmentScaling

/-!
# FIRST PASS, Proposition 4.2: the environment-scaling input `hEnvS`

`firstPass_4_2_of_wholeplane_model` (`FirstPass/S4d/Final42.lean:60`) takes `hEnvS : ConeEnvironmentScalingUnderSLE 𝒮`
(`FirstPass/Frozen/S1d.lean:38`). That Prop is `hsc → hrp → hind → ConeEnvironmentScalingStep 𝒮`, so under the three SLE
premises `hEnvS` is exactly `ConeEnvironmentScalingStep 𝒮` (`coneEnvironmentScalingUnderSLE_iff`,
`FirstPass/SLERef/Extended.lean:162`).

Audit claim checked (`notes/fp-gaps/CHATGPT-209-idla-3-1-4-2-5-3-audit-PRO.md`, §(b) and item 5: "prove `hEnvS` from `hsc`,
`hrp`, `hind` and remove it"). In Lean it is not a removal:
* `ConeEnvironmentScalingStep 𝒮` is proved in the repo only by `coneEnvironmentScalingStep_of_inputs`
  (`Proofs/Sec1/EnvironmentScaling.lean:273`). That lemma also needs `hscale`, `h22` and three named steps:
  `RescaledConeFieldStep` (:113), `RescaledConeClockStep` (:130), `RescaledMatingOfTreesStep` (:139).
* `RescaledMatingOfTreesStep 𝒮` has no proof anywhere in the repo. `RescaledConeFieldStep` and `RescaledConeClockStep`
  are proved only from further named steps (`Proofs/Sec1/EnvironmentScaling/FieldAssembly.lean:276`, `Field.lean:1242`,
  `AllStartsClock.lean:1594`).
* The audit's written argument (`notes/fp-gaps/CHATGPT-idla-sle-frozen-7.md` §2) uses the cone/GMC covariance construction
  and the auxiliary-witness reconstruction; neither is formalized in the repo.

So the three steps stay named hypotheses in `firstPass_4_2_of_wholeplane_model_noEnvS`. Together with `hscale`, `h22`,
`hsc`, `hrp`, `hind` they entail `hEnvS`. The new theorem therefore has a stronger hypothesis set than
`firstPass_4_2_of_wholeplane_model`: it trades `hEnvS` for three representation steps and removes no assumption.
-/

namespace MatedCRT

/-- `ConeEnvironmentScalingUnderSLE 𝒮` from the three representation steps and the inputs `hscale`, `h22`. The SLE premises
`hsc`, `hrp`, `hind` are the antecedents of the conclusion; they are also passed to `coneEnvironmentScalingStep_of_inputs`. -/
theorem coneEnvironmentScalingUnderSLE_of_inputs {𝒮 : SpaceFillingSLEModel}
    (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (hfield : RescaledConeFieldStep 𝒮) (hclock : RescaledConeClockStep 𝒮)
    (hmating : RescaledMatingOfTreesStep 𝒮) :
    ConeEnvironmentScalingUnderSLE 𝒮 :=
  fun _ _ _ => coneEnvironmentScalingStep_of_inputs 𝒮 hscale h22 hsc hrp hind hfield hclock hmating

open _root_.HarmonicBalls in
/-- **Proposition 4.2 without the separate `hEnvS` binder.** Same conclusion and binders as
`firstPass_4_2_of_wholeplane_model`, with `hEnvS` replaced by the named steps `hfield`, `hclock`, `hmating`.
`coneEnvironmentScalingUnderSLE_of_inputs` rebuilds `hEnvS` from them, and the counted theorem is applied unchanged. -/
theorem firstPass_4_2_of_wholeplane_model_noEnvS {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h36 : CorrectedHarmonicConvergenceStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮)
    (hfield : RescaledConeFieldStep 𝒮) (hclock : RescaledConeClockStep 𝒮)
    (hmating : RescaledMatingOfTreesStep 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : MatedCRT.FPConeWholePlaneFieldLaw)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_wholeplane_model hm h210 h214 h28 h36 h218 h27 hH
    (coneEnvironmentScalingUnderSLE_of_inputs hsc hrp hind hscale h22 hfield hclock hmating) hsc hrp hind
    hrevuz hdet hrescale hG hpc hsmp hwmp hpole hU hmeasT hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist
    hThm11 hProp56 hconf hI2 hK hloc hSC hE hFL hE1 hE2 hscale h22

#print axioms MatedCRT.coneEnvironmentScalingUnderSLE_of_inputs
#print axioms MatedCRT.firstPass_4_2_of_wholeplane_model_noEnvS

end MatedCRT
