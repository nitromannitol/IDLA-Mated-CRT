import MatedCRT.Assembly.Reference
import MatedCRT.FirstPass.Derived.Counted
import MatedCRT.FirstPass.Derived.CountedMinimal

/-!
# The numbered results at the canonical model from the three canonical premises

The counted forms of docs/campaign/COUNTED.md take the certified reference model `CertifiedReferenceModel ν 𝒮`, and
some of them the quantum cone scaling, the canonical form of Berestycki-Gwynne, Lemma 5.6, the first-hit property of
the curve or the projections of the certified model. At the canonical model `ProbeMi.canonicalSLEModel ν` the
certified model follows from `CanonicalHypotheses ν` (`certifiedReferenceModel_canonical`,
`MatedCRT/Assembly/Reference.lean`), and the other inputs hold for every model (`quantumConeScalingInput_derived`,
`frozenBG20GreenCrudeCanonical_holds`, `fpFirstHitVisits_holds`). So the results below hold at the canonical model from
the three premises `CanonicalHypotheses ν` only. This includes Lemma 3.6, whose one-sided boundary continuity
`FrozenOneSidedBoundaryContinuityFlooredUniform` follows from the reference environments
(`ReferenceInputs.oneSidedBoundaryContinuity`).

The results of Sections 2 and 6 on the quantum cone and the whole-plane field do not depend on the model; they hold
with no hypothesis: Lemma 2.3, the Draft Lemmas 2.4 and 2.5 (with the uniqueness of the time `T`) and the measurability
of the family of Lemma 2.4 (`MatedCRT/Assembly/Reference.lean`), Lemma 2.6, and Lemmas 6.4 and 6.5.
-/

set_option autoImplicit false

open MeasureTheory

namespace MatedCRT

/-- **Lemma 2.6** (scale invariance of the cone harmonic balls), with no hypothesis. -/
theorem coneScaleInvarianceStmt_holds : ConeScaleInvarianceStmt :=
  closed_2_6_lp_derivedInputs FirstPass.Derived.quantumConeScalingInput_derived

/-- **Lemma 6.5** (hitting of annuli), with no hypothesis. -/
theorem annulusHit_holds : AnnulusHitStmt :=
  annulusHit_of_volumeTail FirstPass.Derived.wholePlaneLQGExistenceStep_holds
    AnnulusHitField.coneWholePlaneWeylComparison FirstPass.Derived.wholePlaneLQGCoordinateChangeStep_holds
    FirstPass.Derived.wholePlaneUpperVolumeTailStep_holds

/-- **Lemma 6.4** (prevalence of good annuli), with no hypothesis. -/
theorem goodAnnulusPrevalence_holds : GoodAnnulusPrevalenceStmt :=
  goodAnnulusPrevalence_of_annulusHit annulusHit_holds ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds
    Field.ConeCircle.circleAverageModConstStep

/-- **Lemma 2.19** (explicit bound for the expected exit time) at the canonical model. -/
theorem expectedExitTimeExplicitBound_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    ExpectedExitTimeExplicitBoundStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_2_19_ownBinders_derivedInputs _ ν (certifiedReferenceModel_canonical ν H)

/-- **Lemma 3.1** (corrected, samplewise form) at the canonical model. -/
theorem discretePotentialTightnessPointwise_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    S3c.DiscretePotentialTightnessPointwiseStmt (ProbeMi.canonicalSLEModel ν) :=
  have hC := certifiedReferenceModel_canonical ν H
  S3c.firstPass_3_1_faithful_derivedInputs hC.mepsScaling hC.exitTimeUpperBound
    hC.frozenDiscreteHolderContinuityCorrected

/-- **Lemma 3.3** (uniform convergence of the Green kernel) at the canonical model. -/
theorem uniformConvergenceGreenKernel_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    UniformConvergenceGreenKernelStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_3_3_ownBinders_derivedInputs _ ν (certifiedReferenceModel_canonical ν H)

/-- **Lemma 3.4** (convergence of integrals of the Green function) at the canonical model. -/
theorem integralConvergenceGreenFunction_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    IntegralConvergenceGreenFunctionStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_3_4_ownBinders_derivedInputs _ ν (certifiedReferenceModel_canonical ν H)

/-- **Lemma 3.5** (corrected discrete Dirichlet problem) at the canonical model. -/
theorem discreteDirichletProblemCorrected_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    DiscreteDirichletProblemCorrectedStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_3_5_lp_derivedInputs _ ν (certifiedReferenceModel_canonical ν H)

/-- **Lemma 3.5** (Draft form, boundary datum `φ(η(b))`) at the canonical model, from the corrected form. -/
theorem discreteDirichletProblem_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    DiscreteDirichletProblemStmt (ProbeMi.canonicalSLEModel ν) :=
  FirstPass35Bridge.discreteDirichletProblem_of_corrected (certifiedReferenceModel_canonical ν H).cellSizeEstimate
    closed_2_13_cellRewire (discreteDirichletProblemCorrected_canonical ν H)

/-- **The one-sided boundary continuity of Lemma 3.6** (`FrozenOneSidedBoundaryContinuityFlooredUniform`) at the
canonical model. -/
theorem oneSidedBoundaryContinuity_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    FirstPass36.FrozenOneSidedBoundaryContinuityFlooredUniform (ProbeMi.canonicalSLEModel ν) :=
  (referenceInputs_canonical ν H).oneSidedBoundaryContinuity

/-- **Lemma 3.6** (corrected harmonic convergence and its same-walk annealed form) at the canonical model. -/
theorem correctedHarmonicConvergence_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    CorrectedHarmonicConvergenceStmt (ProbeMi.canonicalSLEModel ν) ∧
      FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt (ProbeMi.canonicalSLEModel ν) :=
  (referenceInputs_canonical ν H).correctedHarmonicConvergence

/-- **Lemma 3.7** (convergence of the normalized exit time) at the canonical model. -/
theorem convergenceNormalizedExitTime_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    ConvergenceNormalizedExitTimeStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_3_7_lp_derivedInputs _ ν (certifiedReferenceModel_canonical ν H)

/-- **Theorem 4.1** (convergence of the divisible sandpile odometers) at the canonical model. -/
theorem convergenceDivisible_canonical
    (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    ConvergenceDivisibleStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_4_1_lp_derivedInputs ν (certifiedReferenceModel_canonical ν H)

/-- **Proposition 4.2** (lower bound for the divisible sandpile) at the canonical model. -/
theorem divSandpileLowerBound_canonical
    (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    DivSandpileLowerBoundStmt (ProbeMi.canonicalSLEModel ν) :=
  have hC := certifiedReferenceModel_canonical ν H
  FirstPassClosure.closed_4_2_lp_minimalInputs hC.mepsScaling hC.degreeMeasureConvergence
    (integralConvergenceGreenFunction_canonical ν H) hC.greenKernelUpperBound hC.cellSizeEstimate
    (discreteDirichletProblemCorrected_canonical ν H) hC.exitTimeUpperBound
    hC.frozenDiscreteHolderContinuityCorrected FirstPass.Derived.quantumConeScalingInput_derived

/-- **Lemma 4.6** (subsequential convergence, prepared form) at the canonical model. -/
theorem subsequentialConvergencePrepared_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    SubsequentialConvergencePreparedStmt (ProbeMi.canonicalSLEModel ν) :=
  have hC := certifiedReferenceModel_canonical ν H
  firstPass_4_6_h35c_derivedInputs hC.mepsScaling hC.exitTimeUpperBound hC.frozenDiscreteHolderContinuityCorrected
    hC.cellSizeEstimate (discreteDirichletProblemCorrected_canonical ν H)
    (convergenceNormalizedExitTime_canonical ν H)

/-- **Lemma 4.7** (equiboundedness of the odometers) at the canonical model. -/
theorem equibounded_canonical
    (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) : EquiboundedStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_4_7_ownBinders_derivedInputs _ ν (certifiedReferenceModel_canonical ν H)

/-- **Lemma 4.8** (properties of subsequential limits, corrected) at the canonical model. -/
theorem subsequentialPropertiesCorrected_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    SubsequentialPropertiesCorrectedStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_4_8_lp_derivedInputs _ ν (certifiedReferenceModel_canonical ν H)

/-- **Proposition 5.1** (lower bound for IDLA) at the canonical model. -/
theorem idlaLowerBound_canonical
    (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) : IDLALowerBoundStmt (ProbeMi.canonicalSLEModel ν) :=
  FirstPassClosure.closed_5_1_lp_noSup_derivedInputs ν (certifiedReferenceModel_canonical ν H)
    FirstPass.Derived.quantumConeScalingInput_derived (frozenBG20GreenCrudeCanonical_holds _)

/-- **Proposition 5.2** (general lower bound for IDLA) at the canonical model. -/
theorem generalIDLALowerBound_canonical
    (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    GeneralIDLALowerBoundStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_5_2_ownBinders_derivedInputs _ ν (certifiedReferenceModel_canonical ν H)

/-- **Lemma 5.3** (mean value inequality) at the canonical model. -/
theorem meanValueInequality_canonical
    (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) : MeanValueInequalityStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_5_3_clean_derivedInputs ν (certifiedReferenceModel_canonical ν H)
    FirstPass.Derived.quantumConeScalingInput_derived (fpFirstHitVisits_holds _)

/-- **Proposition 6.1** (upper bound for IDLA) at the canonical model. -/
theorem idlaUpperBound_canonical
    (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) : IDLAUpperBoundStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_6_1_lp_noSup_derivedInputs ν (certifiedReferenceModel_canonical ν H)
    FirstPass.Derived.quantumConeScalingInput_derived (frozenBG20GreenCrudeCanonical_holds _)

/-- **Lemma 6.7** (constant-order lower bound, faithful form) at the canonical model. -/
theorem faithfulConstantOrderLowerBound_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    FaithfulConstantOrderLowerBoundStmt (ProbeMi.canonicalSLEModel ν) :=
  LIClosed68Y.firstPass_6_7_minimalInputs (certifiedReferenceModel_canonical ν H)

/-- **Lemma 6.8** (constant-order lower bound for the divisible sandpile, faithful form) at the canonical model. -/
theorem faithfulConstantOrderLowerBoundDiv_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    FaithfulConstantOrderLowerBoundDivStmt (ProbeMi.canonicalSLEModel ν) :=
  LIClosed68Y.firstPass_6_8_minimalInputs (certifiedReferenceModel_canonical ν H)

/-- **Lemma 6.9** (chance of being absorbed, faithful form) at the canonical model. -/
theorem faithfulChanceOfBeingAbsorbed_canonical (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    FaithfulChanceOfBeingAbsorbedStmt (ProbeMi.canonicalSLEModel ν) :=
  LIClosed68Y.firstPass_6_9_minimalInputs (certifiedReferenceModel_canonical ν H)

/-- **Lemma 6.10** (iterative bound) at the canonical model. -/
theorem iterativeBound_canonical
    (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) : IterativeBoundStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_6_10_lp_derivedInputs _ ν (certifiedReferenceModel_canonical ν H)

/-- **Proposition 7.1** (upper bound for the divisible sandpile) at the canonical model. -/
theorem divSandpileUpperBound_canonical
    (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    DivSandpileUpperBoundStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_7_1_lp_derivedInputs _ ν (certifiedReferenceModel_canonical ν H)
    FirstPass.Derived.quantumConeScalingInput_derived

/-- **Theorem 8.1** (convergence of IDLA constrained to a domain) at the canonical model. -/
theorem idlaConstrainedConvergence_canonical
    (ν : ℝ → Measure SLEPathCode) (H : CanonicalHypotheses ν) :
    IDLAConstrainedConvergenceStmt (ProbeMi.canonicalSLEModel ν) :=
  closed_8_1_lp_noSup_derivedInputs ν (certifiedReferenceModel_canonical ν H)
    FirstPass.Derived.quantumConeScalingInput_derived (frozenBG20GreenCrudeCanonical_holds _)

end MatedCRT
