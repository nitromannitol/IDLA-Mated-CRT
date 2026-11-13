import MatedCRT.Proposed.BouRabeeGwynneHarmonicBalls2022
import MatedCRT.FirstPass.Frozen.S5k
import MatedCRT.FirstPass.Closure.AppendixA
import MatedCRT.FirstPass.Closure.AuditCore
import MatedCRT.FirstPass.Closure.AuditRewire14
import MatedCRT.FirstPass.Closure.Final14
import MatedCRT.FirstPass.Closure.Final14Composed
import MatedCRT.FirstPass.Closure.Final14Full
import MatedCRT.FirstPass.Closure.Final22
import MatedCRT.FirstPass.Closure.Final23
import MatedCRT.FirstPass.S3i.LensStep
import MatedCRT.FirstPass.S3i.ExitAlmostSure
import MatedCRT.FirstPass.S3i.QuenchedBoundsCorrected
import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.FirstPass.Closure.Prop51
import MatedCRT.FirstPass.Closure.Prop51Canon
import MatedCRT.FirstPass.Closure.Prop51Cited
import MatedCRT.FirstPass.Closure.Rewire53
import MatedCRT.FirstPass.Closure.SLEPackage
import MatedCRT.FirstPass.Closure.Section2
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.Closure.Section4
import MatedCRT.FirstPass.Closure.Section5
import MatedCRT.FirstPass.Closure.Section6
import MatedCRT.FirstPass.Closure.Section7
import MatedCRT.FirstPass.Closure.Theorem14
import MatedCRT.FirstPass.Closure.Theorem14d
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.S5k
import MatedCRT.FirstPass.S5qd

/-!
# Harmonic balls, Lemma 3.1: least-supersolution membership, and the wrappers of the counted closures

The frozen input `FrozenLeastSupersolutionMemCone 𝒮` is replaced by the printed HB22 Lemma 3.1
(`HarmonicBallsLemma31Printed`) through the transfer step `ConeLeastSupersolutionTransfer 𝒮`. The transfer
is a named hypothesis: the corrected paper has no written argument for it (see the report).
-/


namespace MatedCRT

/-- The transfer step from HB22 Lemma 3.1 (whole-plane GFF with insertion `α₀ = γ`) to the quantum cone:
the least-supersolution membership `FrozenLeastSupersolutionMemCone 𝒮`. Named hypothesis; no written
argument in `paper/idla_mated_crt-corrected.tex` (location and missing claim in the report). -/
def ConeLeastSupersolutionTransfer (𝒮 : SpaceFillingSLEModel) : Prop :=
  HarmonicBallsLemma31Printed → FrozenLeastSupersolutionMemCone 𝒮

/-- `FrozenLeastSupersolutionMemCone 𝒮` from HB22 Lemma 3.1 through the transfer step. -/
theorem frozenLeastSupersolutionMemCone_of_lemma31 {𝒮 : SpaceFillingSLEModel}
    (hT : ConeLeastSupersolutionTransfer 𝒮) (h : HarmonicBallsLemma31Printed) :
    FrozenLeastSupersolutionMemCone 𝒮 :=
  hT h

end MatedCRT

namespace MatedCRT

section
open MatedCRT.FirstPassClosure
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/AuditRewire14.lean
/-- Wrapper of `closed_1_4_p3`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_p3_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    : ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_p3 ν hC hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF3 hexc (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hrescale

-- from MatedCRT/FirstPass/Closure/AuditRewire14.lean
/-- Wrapper of `closed_1_6_p3`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_p3_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    : ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_p3 ν hC hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF3 hexc (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hrescale

end

section
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Final14.lean
/-- Wrapper of `closed_1_4_final`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_final_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
   : ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_final ν hcore hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hcone hrevuz h23 hdiv hF3 (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hrescale

-- from MatedCRT/FirstPass/Closure/Final14.lean
/-- Wrapper of `closed_1_6_final`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_final_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
   : ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_final ν hcore hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hcone hrevuz h23 hdiv hF3 (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hrescale

end

section
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Final14Composed.lean
/-- Wrapper of `closed_1_4_composed`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_composed_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)

   : ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_composed ν hcore hscale hsc hrp hind hEnvS hBG h0 h2 hV h23 hdiv hF3 (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hrescale

-- from MatedCRT/FirstPass/Closure/Final14Composed.lean
/-- Wrapper of `closed_1_6_composed`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_composed_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)

   : ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_composed ν hcore hscale hsc hrp hind hEnvS hBG h0 h2 hV h23 hdiv hF3 (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hrescale

end

section
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Final14Full.lean
/-- Wrapper of `closed_1_4_full`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_full_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hSCHB : ClusterStrongCompatibilityStmt.{0})
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)

   : ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_full ν hcore hscale hsc hrp hind hEnvS hBG h0 h2 hV hdiv hF3 (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hrescale hND hBdryHB hExistHB hProp56HB hI2HB hlocHB hSCHB hU hmeasT hmin hGB hpole

-- from MatedCRT/FirstPass/Closure/Final14Full.lean
/-- Wrapper of `closed_1_6_full`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_full_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hSCHB : ClusterStrongCompatibilityStmt.{0})
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)

   : ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_full ν hcore hscale hsc hrp hind hEnvS hBG h0 h2 hV hdiv hF3 (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hrescale hND hBdryHB hExistHB hProp56HB hI2HB hlocHB hSCHB hU hmeasT hmin hGB hpole

end

section
open MatedCRT.FirstPassClosure
open MeasureTheory
open MeasureTheory Filter Topology Set Metric
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_1_4_p3_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_p3_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
   : ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_p3_bm ν hC hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF3 (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hrescale

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_1_6_p3_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_p3_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
   : ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_p3_bm ν hC hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF3 (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hrescale

end

section
open MeasureTheory Filter Topology Set Metric

-- from MatedCRT/FirstPass/S5k.lean
/-- Wrapper of `stoppedFloorObstacleVersion_proved`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem stoppedFloorObstacleVersion_proved_lemma31 (𝒮 : SpaceFillingSLEModel)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hG : FrozenGreenDiscPole) :
    StoppedFloorObstacleVersion 𝒮 :=
  stoppedFloorObstacleVersion_proved 𝒮 hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hG

end

section
open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/S5qd.lean
/-- Wrapper of `firstPass_5_1_derived`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem firstPass_5_1_derived_lemma31 (𝒮 : SpaceFillingSLEModel)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hT : RandomWalkToLBMStmt 𝒮 → CellSizeEstimateStmt 𝒮 → MepsScalingInput 𝒮 →
      BrownianOutwardExcursionAtExitStep → FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (hG : FrozenGreenDiscPole) (hG15 : GreenFunctionCrudeBoundStmt 𝒮) (hG16 : GreenKernelLowerBoundStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hmeasT : FrozenLQGTestIntegralMeasurable) (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) :
    IDLALowerBoundStmt 𝒮 :=
  firstPass_5_1_derived 𝒮 hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) h27 h28 hE1 hE2 hscale h22 h24c h218 hU hm h210 h214 h211 hrevuz hT hexc h35 hH hcone hG hG15 hG16 h41 h33 h32 h611 h82 hI2 hmodel hFL hLoc hpair hmeasT hstd hmin hC hGB hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hconf hK hloc hSC hE

-- from MatedCRT/FirstPass/S5qd.lean
/-- Wrapper of `firstPass_5_1_derived_closed`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem firstPass_5_1_derived_closed_lemma31 (𝒮 : SpaceFillingSLEModel)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (hG : FrozenGreenDiscPole) (hG15 : GreenFunctionCrudeBoundStmt 𝒮) (hG16 : GreenKernelLowerBoundStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hmeasT : FrozenLQGTestIntegralMeasurable) (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) :
    IDLALowerBoundStmt 𝒮 :=
  firstPass_5_1_derived_closed 𝒮 hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) h27 h28 hE1 hE2 hscale h22 h24c h218 hU hm h210 h214 h211 hrevuz hexc h35 hH hcone hG hG15 hG16 h41 h33 h32 h611 h82 hI2 hmodel hFL hLoc hpair hmeasT hstd hmin hC hGB hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hconf hK hloc hSC hE

end

end MatedCRT

namespace MatedCRT.FirstPassClosure

section
open MatedCRT.FirstPassClosure
open MeasureTheory
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/AuditCore.lean
/-- Wrapper of `closed_1_4_wired_certCore`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_wired_certCore_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hcore : CertifiedReferenceModelCore ν 𝒮) (hBM : BrownianOutwardExcursionAtExitStep) (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮) (h23 : ConeHarmonicBallsStmt) (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel) (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple) (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : FrozenGreenFunctionCrudeBound 𝒮) (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType) (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales) (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls) (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected) (hsmp : FPStrongMinimumPrinciple) (hpole : FrozenGreenDiscPole) (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_wired_certCore ν hcore hBM hscale hsc hrp hind hEnvS hm hdeg h27 h28 h29 h210 h214 h216 h218 hH h0 h2 hV hR hcone hrevuz hdet h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/AuditCore.lean
/-- Wrapper of `closed_1_6_wired_certCore`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_wired_certCore_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hcore : CertifiedReferenceModelCore ν 𝒮) (hBM : BrownianOutwardExcursionAtExitStep) (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮) (h23 : ConeHarmonicBallsStmt) (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel) (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple) (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : FrozenGreenFunctionCrudeBound 𝒮) (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType) (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales) (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls) (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected) (hsmp : FPStrongMinimumPrinciple) (hpole : FrozenGreenDiscPole) (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_wired_certCore ν hcore hBM hscale hsc hrp hind hEnvS hm hdeg h27 h28 h29 h210 h214 h216 h218 hH h0 h2 hV hR hcone hrevuz hdet h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/AuditCore.lean
/-- Wrapper of `closed_1_4_derived_certCore`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_derived_certCore_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hcore : CertifiedReferenceModelCore ν 𝒮) (hBM : BrownianOutwardExcursionAtExitStep) (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮) (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (h23 : ConeHarmonicBallsStmt) (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel) (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple) (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : FrozenGreenFunctionCrudeBound 𝒮) (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType) (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales) (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls) (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected) (hsmp : FPStrongMinimumPrinciple) (hpole : FrozenGreenDiscPole) (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_derived_certCore ν hcore hBM hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/AuditCore.lean
/-- Wrapper of `closed_1_6_derived_certCore`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_derived_certCore_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hcore : CertifiedReferenceModelCore ν 𝒮) (hBM : BrownianOutwardExcursionAtExitStep) (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮) (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (h23 : ConeHarmonicBallsStmt) (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel) (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple) (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : FrozenGreenFunctionCrudeBound 𝒮) (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType) (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales) (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls) (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected) (hsmp : FPStrongMinimumPrinciple) (hpole : FrozenGreenDiscPole) (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_derived_certCore ν hcore hBM hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

end

section
open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Prop51.lean
/-- Wrapper of `closed_5_1`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_5_1_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    
    (hscale : QuantumConeScalingInput)
    
    (h27 : VolumeGrowthStmt) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : GreenFunctionCrudeBoundStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0}) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1 ν hC hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hcell hU hexc hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK hE hE1 hE2 hscale h27 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC

end

section
open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Prop51Canon.lean
/-- Wrapper of `closed_5_1_canon`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_5_1_canon_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    
    (hscale : QuantumConeScalingInput)
    
    (h27 : VolumeGrowthStmt) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_canon ν hC hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hcell hU hexc hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK hE hE1 hE2 hscale h27 h22 h24c hcanon h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC

-- from MatedCRT/FirstPass/Closure/Prop51Canon.lean
/-- Wrapper of `closed_5_1_canon_noCell`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_5_1_canon_noCell_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    
    (hscale : QuantumConeScalingInput)
    
    (h27 : VolumeGrowthStmt) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_canon_noCell ν hC hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hU hexc hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK hE hE1 hE2 hscale h27 h22 h24c hcanon h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC

end

section
open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Prop51Cited.lean
/-- Wrapper of `closed_5_1_cited`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_5_1_cited_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    
    (hscale : QuantumConeScalingInput)
    
    (h27 : VolumeGrowthStmt) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_cited ν hC hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hcell hU hexc hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK hE hE1 hE2 hscale h27 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC

end

section
open MatedCRT.FirstPassClosure
open MeasureTheory
open MeasureTheory Filter Topology Set Metric
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_1_4_wired_certCore_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_wired_certCore_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_wired_certCore_bm ν hcore hscale hsc hrp hind hEnvS hm hdeg h27 h28 h29 h210 h214 h216 h218 hH h0 h2 hV hR hcone hrevuz hdet h23 hdiv hF1 hF2 hF3 hcell hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_1_6_wired_certCore_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_wired_certCore_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_wired_certCore_bm ν hcore hscale hsc hrp hind hEnvS hm hdeg h27 h28 h29 h210 h214 h216 h218 hH h0 h2 hV hR hcone hrevuz hdet h23 hdiv hF1 hF2 hF3 hcell hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_1_4_derived_certCore_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_derived_certCore_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_derived_certCore_bm ν hcore hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_1_6_derived_certCore_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_derived_certCore_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_derived_certCore_bm ν hcore hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_5_1_canon_noCell_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_5_1_canon_noCell_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hG : FrozenGreenDiscPole)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (h27 : VolumeGrowthStmt)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
   :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_canon_noCell_bm ν hC hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hU hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK hE hE1 hE2 hscale h27 h22 h24c hcanon h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC

end

section
open MeasureTheory
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Theorem14.lean
/-- Wrapper of `closed_1_4_wired`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_wired_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont)
    
    (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility)
    
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_wired ν hC hscale hsc hrp hind hEnvS hm hdeg h27 h28 h29 h210 h214 h216 h218 hH h0 h2 hV hR hcone hrevuz hdet h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/Theorem14.lean
/-- Wrapper of `closed_1_6_wired`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_wired_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont)
    
    (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility)
    
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_wired ν hC hscale hsc hrp hind hEnvS hm hdeg h27 h28 h29 h210 h214 h216 h218 hH h0 h2 hV hR hcone hrevuz hdet h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

end

section
open MeasureTheory
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Theorem14d.lean
/-- Wrapper of `closed_1_4_derived`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_derived_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont)
    
    (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility)
    
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_derived ν hC hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/Theorem14d.lean
/-- Wrapper of `closed_1_6_derived`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_derived_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont)
    
    (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility)
    
    (hGBall : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hpole : FrozenGreenDiscPole)
    (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_derived ν hC hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hGBall hpc hsmp hpole hnj hcan hcl hcan6

end

section
open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/S5qd.lean
/-- Wrapper of `closed_5_1_canon_noCell_derived`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_5_1_canon_noCell_derived_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hT : RandomWalkToLBMStmt 𝒮 → CellSizeEstimateStmt 𝒮 → MepsScalingInput 𝒮 →
      BrownianOutwardExcursionAtExitStep → FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    
    (hscale : QuantumConeScalingInput)
    
    (h27 : VolumeGrowthStmt) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_canon_noCell_derived ν hC hT hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hU hexc hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK hE hE1 hE2 hscale h27 h22 h24c hcanon h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC

-- from MatedCRT/FirstPass/S5qd.lean
/-- Wrapper of `closed_5_1_canon_noCell_derived_closed`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_5_1_canon_noCell_derived_closed_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    
    (hscale : QuantumConeScalingInput)
    
    (h27 : VolumeGrowthStmt) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_canon_noCell_derived_closed ν hC hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hU hexc hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK hE hE1 hE2 hscale h27 h22 h24c hcanon h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC

end

end MatedCRT.FirstPassClosure

namespace MatedCRT.HBRewire

section
open MatedCRT.FirstPassClosure
open MeasureTheory
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/AuditCore.lean
/-- Wrapper of `closed_1_4_derived_hb_certCore`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_derived_hb_certCore_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hcore : CertifiedReferenceModelCore ν 𝒮) (hBM : BrownianOutwardExcursionAtExitStep) (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮) (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (h23 : ConeHarmonicBallsStmt) (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel) (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple) (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : FrozenGreenFunctionCrudeBound 𝒮) (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType) (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales) (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls) (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) (hpc : FrozenPunctureConnected) (hsmp : FPStrongMinimumPrinciple) (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_derived_hb_certCore ν hcore hBM hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hpc hsmp hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/AuditCore.lean
/-- Wrapper of `closed_1_6_derived_hb_certCore`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_derived_hb_certCore_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hcore : CertifiedReferenceModelCore ν 𝒮) (hBM : BrownianOutwardExcursionAtExitStep) (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮) (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (h23 : ConeHarmonicBallsStmt) (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel) (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple) (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : FrozenGreenFunctionCrudeBound 𝒮) (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType) (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales) (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls) (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) (hpc : FrozenPunctureConnected) (hsmp : FPStrongMinimumPrinciple) (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_derived_hb_certCore ν hcore hBM hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hpc hsmp hnj hcan hcl hcan6

end

section
open MatedCRT.FirstPassClosure
open MeasureTheory
open MeasureTheory Filter Topology Set Metric
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_1_4_derived_hb_certCore_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_derived_hb_certCore_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_derived_hb_certCore_bm ν hcore hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hpc hsmp hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_1_6_derived_hb_certCore_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_derived_hb_certCore_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_derived_hb_certCore_bm ν hcore hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hpc hsmp hnj hcan hcl hcan6

end

section
open MatedCRT.FirstPassClosure
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/HBRewire.lean
/-- Wrapper of `closed_1_4_derived_hb`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_derived_hb_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
    : ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_derived_hb ν hC hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hpc hsmp hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/HBRewire.lean
/-- Wrapper of `closed_1_6_derived_hb`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_derived_hb_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality)
    (hpair : FPPairingLawIG4)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
    : ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_derived_hb ν hC hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF1 hF2 hF3 hcell hexc hμae hSB (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hLoc hpair hstd hmin hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hpc hsmp hnj hcan hcl hcan6

end

end MatedCRT.HBRewire

namespace MatedCRT.Phase2

section
open MatedCRT.FirstPassClosure
open MeasureTheory
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/AuditCore.lean
/-- Wrapper of `closed_1_4_derived_p2_certCore`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_derived_p2_certCore_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hcore : CertifiedReferenceModelCore ν 𝒮) (hBM : BrownianOutwardExcursionAtExitStep) (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮) (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (h23 : ConeHarmonicBallsStmt) (hdiv : FrozenConeRadialDivergenceCorrected) (hF3 : FrozenDiskGreenNonnegCont) (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw) (hstd : FrozenConeLogLocalCodeLawStd) (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : FrozenGreenFunctionCrudeBound 𝒮) (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType) (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales) (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls) (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_derived_p2_certCore ν hcore hBM hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF3 hcell hexc (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/AuditCore.lean
/-- Wrapper of `closed_1_6_derived_p2_certCore`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_derived_p2_certCore_lemma31 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hcore : CertifiedReferenceModelCore ν 𝒮) (hBM : BrownianOutwardExcursionAtExitStep) (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮) (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (h23 : ConeHarmonicBallsStmt) (hdiv : FrozenConeRadialDivergenceCorrected) (hF3 : FrozenDiskGreenNonnegCont) (hcell : FrozenAdjacentCellsMeetAe 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw) (hstd : FrozenConeLogLocalCodeLawStd) (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) (h22 : LQGMeasurePropertiesStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : FrozenGreenFunctionCrudeBound 𝒮) (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType) (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales) (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls) (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) (hnj : StrictGapFixedTimeUnionStep 𝒮) (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_derived_p2_certCore ν hcore hBM hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF3 hcell hexc (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hnj hcan hcl hcan6

end

section
open MatedCRT.FirstPassClosure
open MeasureTheory
open MeasureTheory Filter Topology Set Metric
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_1_4_derived_p2_certCore_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_4_derived_p2_certCore_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_derived_p2_certCore_bm ν hcore hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF3 hcell (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hnj hcan hcl hcan6

-- from MatedCRT/FirstPass/Closure/Rewire53.lean
/-- Wrapper of `closed_1_6_derived_p2_certCore_bm`: the frozen least-supersolution input `FrozenLeastSupersolutionMemCone 𝒮` is supplied by the transfer step `ConeLeastSupersolutionTransfer 𝒮` applied to HB22 Lemma 3.1 (`HarmonicBallsLemma31Printed`). -/
theorem closed_1_6_derived_p2_certCore_bm_lemma31
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮)
    (hdeg : DegreeBoundInput 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h51 : BG20Prop51 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction)
    (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergenceCorrected)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hLST : MatedCRT.ConeLeastSupersolutionTransfer 𝒮) (hHB31 : MatedCRT.HarmonicBallsLemma31Printed)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero)
    (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet)
    (hSC : FrozenClusterStrongCompatibility)
    (hnj : StrictGapFixedTimeUnionStep 𝒮)
    (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep)
    (hcan6 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
   :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_derived_p2_certCore_bm ν hcore hscale hsc hrp hind hEnvS hm hdeg hBG h28 h29 h210 h214 h216 h51 hH h0 h2 hV hR hcone hrevuz h23 hdiv hF3 hcell (MatedCRT.frozenLeastSupersolutionMemCone_of_lemma31 hLST hHB31) hmodel hFL hstd hGBC hconf hK hE hE1 hE2 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hnj hcan hcl hcan6

end

end MatedCRT.Phase2
