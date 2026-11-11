import MatedCRT.FirstPass.S4d
import MatedCRT.FirstPass.S4S6c
import MatedCRT.FirstPass.S3g
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.Closure.CellRewire
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.Proofs.Sec3.ConeBallMass

/-! # Consumers of Lemma 3.5 bound to its corrected form

The printed Lemma 3.5 (`DiscreteDirichletProblemStmt`, Draft/Section3.lean:132) is concluded by no counted
theorem; the counted theorem is the corrected form `DiscreteDirichletProblemCorrectedStmt`
(Draft/Section3DirichletCorrected.lean:13, concluded by `closed_3_5`, Closure/Section3.lean:68).
The copies below bind the corrected form. They obtain the printed form by the bridge
`FirstPass35Bridge.discreteDirichletProblem_of_corrected` (FirstPass/S3g.lean:49), which takes the
cell-size estimate `CellSizeEstimateStmt` and the discrete maximum principle `MaximumPrincipleStmt`
(`closed_2_13_cellRewire`, Closure/CellRewire.lean:21) as further inputs. The originals are unchanged.
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

/-- Proposition 4.2 (`DivSandpileLowerBoundStmt`), final form `firstPass_4_2_final` (FirstPass/S4d.lean:146),
with the binder `h35` replaced by the corrected Lemma 3.5 `DiscreteDirichletProblemCorrectedStmt`. All other
binders and the conclusion are those of `firstPass_4_2_final`. -/
theorem firstPass_4_2_final_h35c {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_final hm h210 h34 h214 h28
    (FirstPass35Bridge.discreteDirichletProblem_of_corrected h28 closed_2_13_cellRewire h35c)
    h218 h27 hH hcone h23 h24 h33 hG hpc hsmp hwmp hpole hnj hcan hcl hE1 hE2 hscale h22

#print axioms firstPass_4_1_coneLaw_h35c
#print axioms firstPass_4_1_ownBinders_h35c
#print axioms firstPass_4_1_ownBinders_counted
#print axioms firstPass_4_2_final_h35c

end MatedCRT
