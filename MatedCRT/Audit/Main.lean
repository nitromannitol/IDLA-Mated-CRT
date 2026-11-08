import MatedCRT.Assembly.Main
import MatedCRT.Audit.CorrectedForms
import MatedCRT.Audit.Refutations

/-!
# Audit: the conditional Theorems 1.4 and 1.6

* `#print axioms` of `convergenceOfIDLA_conditional` and `convergenceOfDivSandpile_conditional`.
* For every numbered result on the main line, an `example` restating it from `MainHypotheses` and a check
  `assert_uses T R`: the reduction `R` occurs in the proof of the theorem `T`, transitively through the theorems
  `MainHypotheses.*` of MatedCRT/Assembly/Main.lean. A reduction dropped from the composition, or a numbered result
  routed around, makes this file fail. `assert_uses_deep` follows every constant under `MatedCRT` instead.
* `assert_no_refuted_field`: no field of `MainHypotheses` is a statement refuted in Lean, i.e. the head of the
  conclusion `¬ C …` of a theorem of a module under `MatedCRT.Audit` (at present MatedCRT/Audit/CorrectedForms.lean:
  the Draft Lemmas 4.4 and 4.5, E-c1-1; MatedCRT/Audit/Refutations.lean: the Draft Lemma 3.1, E-c1-4).
-/

open Lean Elab Command

namespace MatedCRT.Audit.Main

/-- The body of a theorem or definition. -/
def valueOf? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | _ => none

/-- Whether the proof of `root` uses the constant `target`, following the constants under the prefix `pfx`. -/
def usesTrans (env : Environment) (root pfx target : Name) (fuel : Nat := 10000) : Bool := Id.run do
  let mut todo : Array Name := #[root]
  let mut seen : NameSet := {}
  let mut fuel := fuel
  while 0 < todo.size && 0 < fuel do
    fuel := fuel - 1
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      if let some v := valueOf? ci then
        for c in v.getUsedConstants do
          if c == target then return true
          if pfx.isPrefixOf c then todo := todo.push c
  return false

/-- `assert_uses T R`: fail unless the proof of `T` uses `R`, directly or through `MatedCRT.MainHypotheses.*`. -/
elab "assert_uses " t:ident r:ident : command => do
  let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let rn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo r
  unless usesTrans (← getEnv) tn `MatedCRT.MainHypotheses rn do
    throwError "{tn} does not use {rn}"

/-- `assert_uses_deep T R`: fail unless the proof of `T` uses `R`, through any constant under `MatedCRT`. -/
elab "assert_uses_deep " t:ident r:ident : command => do
  let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let rn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo r
  unless usesTrans (← getEnv) tn `MatedCRT rn 200000 do
    throwError "{tn} does not use {rn}"

/-- `assert_not_uses T R`: fail if the proof of `T` uses `R` (a control that `assert_uses` is not vacuous). -/
elab "assert_not_uses " t:ident r:ident : command => do
  let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let rn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo r
  if usesTrans (← getEnv) tn `MatedCRT.MainHypotheses rn then
    throwError "{tn} uses {rn}"

/-- The statements refuted in Lean: the heads `C` of the conclusions `¬ C …` of the theorems of the modules under
`MatedCRT.Audit`. -/
def refutedStatements (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless ci matches .thmInfo _ do continue
    let some idx := env.getModuleIdxFor? n | continue
    let some mn := env.header.moduleNames[idx.toNat]? | continue
    unless (`MatedCRT.Audit).isPrefixOf mn do continue
    let body := ci.type.getForallBody
    unless body.isAppOfArity ``Not 1 do continue
    let some c := body.appArg!.getAppFn.constName? | continue
    unless out.contains c do out := out.push c
  return out

/-- `assert_no_refuted_field`: fail if the type of a field of `MainHypotheses` is headed by a statement refuted in
Lean under `MatedCRT.Audit` (or if the Draft Lemma 4.4, refuted in MatedCRT/Audit/CorrectedForms.lean, or the Draft
Lemma 3.1, refuted in MatedCRT/Audit/Refutations.lean, is not found among the refuted statements: a guard against a
vacuous check). Logs the refuted statements and the field count. -/
elab "assert_no_refuted_field" : command => do
  let env ← getEnv
  let refuted := refutedStatements env
  unless refuted.contains ``MatedCRT.DiscreteLaplacianBoundStmt do
    throwError "the refutation of the Draft Lemma 4.4 is not found under MatedCRT.Audit: {refuted}"
  unless refuted.contains ``MatedCRT.DiscretePotentialTightnessStmt do
    throwError "the refutation of the Draft Lemma 3.1 is not found under MatedCRT.Audit: {refuted}"
  let fields := getStructureFields env ``MatedCRT.MainHypotheses
  let mut bad : Array Name := #[]
  for f in fields do
    let some ci := env.find? (``MatedCRT.MainHypotheses ++ f) | throwError "no projection {f}"
    let some c := ci.type.getForallBody.getAppFn.constName? | continue
    if refuted.contains c then bad := bad.push f
  unless bad.isEmpty do
    throwError "fields of MainHypotheses whose statement is refuted in Lean: {bad}"
  logInfo m!"MainHypotheses has {fields.size} fields; none is refuted in Lean. Refuted under MatedCRT.Audit: {refuted}"

end MatedCRT.Audit.Main

#print axioms MatedCRT.convergenceOfIDLA_conditional
#print axioms MatedCRT.convergenceOfDivSandpile_conditional

assert_no_refuted_field

namespace MatedCRT.Audit.Main

open MatedCRT

variable (𝒮 : SpaceFillingSLEModel)

/-! ## Theorems 1.4, 1.6 and Proposition 8.1 -/

/-- **Theorem 1.4**. -/
example (H : MainHypotheses 𝒮) : ConvergenceOfIDLAStmt 𝒮 := convergenceOfIDLA_conditional 𝒮 H
assert_uses convergenceOfIDLA_conditional convergenceOfIDLA_of_coneSteps

/-- **Theorem 1.6**. -/
example (H : MainHypotheses 𝒮) : ConvergenceOfDivSandpileStmt 𝒮 := convergenceOfDivSandpile_conditional 𝒮 H
assert_uses convergenceOfDivSandpile_conditional convergenceOfDivSandpile_of_coneSteps

/-- **Proposition 8.1**. -/
example (H : MainHypotheses 𝒮) : IDLAConstrainedConvergenceStmt 𝒮 := H.iDLAConstrainedConvergence
assert_uses convergenceOfIDLA_conditional iDLAConstrainedConvergence_of_steps
assert_uses convergenceOfDivSandpile_conditional iDLAConstrainedConvergence_of_steps

/-! ## Section 2 -/

/-- **Theorem 2.3**. -/
example (H : MainHypotheses 𝒮) : ConeHarmonicBallsStmt := H.coneHarmonicBalls
assert_uses convergenceOfIDLA_conditional coneHarmonicBalls_of_steps
assert_uses convergenceOfIDLA_conditional coneFamilyAEMeasurableStep_of_inputs

/-- **Lemma 2.4**. -/
example (H : MainHypotheses 𝒮) : ConeHarmonicBallsUpToFixedTimeStmt := H.coneHarmonicBallsUpToFixedTime
assert_uses convergenceOfIDLA_conditional coneHarmonicBallsUpToFixedTime_final

/-- **Lemma 2.5**. -/
example (H : MainHypotheses 𝒮) : ConeScaleInvarianceUpToFixedTimeStmt := H.coneScaleInvarianceUpToFixedTime
assert_uses convergenceOfIDLA_conditional coneScaleInvarianceUpToFixedTime_of_scaleRadiusPos
assert_uses convergenceOfIDLA_conditional coneScaleRadiusPosStep_of_input

/-- **Lemma 2.13**, proved. -/
example : MaximumPrincipleStmt 𝒮 := MainHypotheses.maximumPrinciple 𝒮
assert_uses convergenceOfIDLA_conditional maximumPrinciple_of_steps

/-- **Lemma 2.17**. -/
example (H : MainHypotheses 𝒮) : BoundedExitTimeRVStmt := H.boundedExitTimeRV
assert_uses convergenceOfIDLA_conditional boundedExitTimeRV_of_steps

/-- **Lemma 2.19**. -/
example (H : MainHypotheses 𝒮) : ExpectedExitTimeExplicitBoundStmt 𝒮 := H.expectedExitTimeExplicitBound
assert_uses convergenceOfIDLA_conditional expectedExitTimeExplicitBound_of_steps

/-! ## Section 3 -/

/-- **Lemma 3.1**, corrected form (the Draft form is refuted in Lean, `assert_no_refuted_field`). -/
example (H : MainHypotheses 𝒮) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  H.discretePotentialTightnessCorrected
assert_uses convergenceOfIDLA_conditional discretePotentialTightnessCorrected_of_inputs

/-- **Lemma 3.3**. -/
example (H : MainHypotheses 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 := H.uniformConvergenceGreenKernel
assert_uses convergenceOfIDLA_conditional uniformConvergenceGreenKernel_final
assert_uses_deep convergenceOfIDLA_conditional greenKernelInteriorStep
assert_uses_deep convergenceOfIDLA_conditional greenKernelBoundaryStep

/-- **Lemma 3.5**. -/
example (H : MainHypotheses 𝒮) : DiscreteDirichletProblemStmt 𝒮 := H.discreteDirichletProblem
assert_uses convergenceOfIDLA_conditional discreteDirichletProblem_of_steps
assert_uses convergenceOfIDLA_conditional dirichletLimitStep_of_volumeGrowth

/-- **Lemma 3.6**. -/
example (H : MainHypotheses 𝒮) : ConvergenceHarmonicFunctionsStmt 𝒮 := H.convergenceHarmonicFunctions
assert_uses convergenceOfIDLA_conditional convergenceHarmonicFunctions_of_inputs
assert_uses_deep convergenceOfIDLA_conditional harmonicExitCellStep_of_inputs

/-- **Lemma 3.7**. -/
example (H : MainHypotheses 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 := H.convergenceNormalizedExitTime
assert_uses convergenceOfIDLA_conditional convergenceNormalizedExitTime_of_statements

/-! ## Section 4 -/

/-- **Theorem 4.1**. -/
example (H : MainHypotheses 𝒮) : ConvergenceDivisibleStmt 𝒮 := H.convergenceDivisible
assert_uses convergenceOfIDLA_conditional convergenceDivisible_of_steps
assert_uses convergenceOfIDLA_conditional obstacleLimitUniqueness
assert_uses convergenceOfIDLA_conditional convergenceDivisibleEventMeasurableStep_of_coneFamilyAEMeasurable

/-- **Proposition 4.2**. -/
example (H : MainHypotheses 𝒮) : DivSandpileLowerBoundStmt 𝒮 := H.divSandpileLowerBound
assert_uses convergenceOfIDLA_conditional divSandpileLowerBound_prop42
assert_uses_deep convergenceOfIDLA_conditional divSandpileOdometerComparison_of_cellsMeet

/-- **Lemma 4.3**, proved. -/
example : DiscreteBasicPropertiesStmt 𝒮 := discreteBasicProperties 𝒮
assert_uses convergenceOfIDLA_conditional discreteBasicProperties

/-- **Lemma 4.4**, corrected form (E-c1-1), proved; the Draft 4.4 is refuted (`assert_no_refuted_field`). -/
example : DiscreteLaplacianBoundCorrectedStmt 𝒮 := discreteLaplacianBoundCorrected 𝒮
assert_uses convergenceOfIDLA_conditional discreteLaplacianBoundCorrected

/-- **Lemma 4.6**. -/
example (H : MainHypotheses 𝒮) : SubsequentialConvergenceStmt 𝒮 := H.subsequentialConvergence
assert_uses convergenceOfIDLA_conditional subsequentialConvergence_of_corrected

/-- **Lemma 4.7**. -/
example (H : MainHypotheses 𝒮) : EquiboundedStmt 𝒮 := H.equibounded
assert_uses convergenceOfIDLA_conditional equibounded_of_steps

/-- **Lemma 4.8**. -/
example (H : MainHypotheses 𝒮) : SubsequentialPropertiesStmt 𝒮 := H.subsequentialProperties
assert_uses convergenceOfIDLA_conditional subsequentialProperties_of_inputs
assert_uses_deep convergenceOfIDLA_conditional odometerDistributionalLimitCorrectedStep_of_greenKernel

/-! ## Section 5 -/

/-- **Proposition 5.1**. -/
example (H : MainHypotheses 𝒮) : IDLALowerBoundStmt 𝒮 := H.iDLALowerBound
assert_uses convergenceOfIDLA_conditional iDLALowerBound_final_of_strictGap
assert_uses_deep convergenceOfIDLA_conditional discreteClusterInnerBound_prop42
assert_uses_deep convergenceOfIDLA_conditional iDLALowerBound_of_volumeGrowth_cellSize
assert_uses_deep convergenceOfIDLA_conditional LQGMeasureField.lqgMeasureFieldMeasurableStep
assert_uses convergenceOfIDLA_conditional stoppedMeanValueInequality_of_steps
assert_uses convergenceOfIDLA_conditional stoppedLLowerBound_of_inputs

/-- **Lemma 5.3** (used by 5.1 inside `iDLALowerBound_final_of_strictGap`). -/
example (H : MainHypotheses 𝒮) : MeanValueInequalityStmt 𝒮 := H.meanValueInequality
assert_uses MainHypotheses.meanValueInequality meanValueInequality_of_surplus
assert_uses MainHypotheses.meanValueInequality meanValueSurplusStep_of_lower

/-- **Lemma 5.4** (used by 5.1 inside `iDLALowerBound_final_of_strictGap`). -/
example (H : MainHypotheses 𝒮) : LLowerBoundStmt 𝒮 := H.lLowerBound
assert_uses MainHypotheses.lLowerBound lLowerBound_of_adjacentCellsMeet

/-! ## Section 6 -/

/-- **Proposition 6.1**. -/
example (H : MainHypotheses 𝒮) : IDLAUpperBoundStmt 𝒮 := H.iDLAUpperBound
assert_uses convergenceOfIDLA_conditional IDLAUpperBound.iDLAUpperBound_of_steps
assert_uses convergenceOfIDLA_conditional boundaryLayerMeasurableStep_of_coneFamilyAEMeasurable

/-- **Lemma 6.4**. -/
example (H : MainHypotheses 𝒮) : GoodAnnulusPrevalenceStmt := H.goodAnnulusPrevalence
assert_uses convergenceOfIDLA_conditional goodAnnulusPrevalence_of_annulusHit
assert_uses convergenceOfIDLA_conditional Field.ConeCircle.circleAverageModConstStep

/-- **Lemma 6.5**. -/
example (H : MainHypotheses 𝒮) : AnnulusHitStmt := H.annulusHit
assert_uses convergenceOfIDLA_conditional annulusHit_of_volumeTail

/-- **Lemma 6.6**, proved (used inside `goodAnnulusPrevalence_of_annulusHit`). -/
example : AnnulusIterateStmt := annulusIterate
assert_uses_deep convergenceOfIDLA_conditional annulusIterate

/-- **Lemma 6.7**, E-A10 (b) form. -/
example (H : MainHypotheses 𝒮) : ConstantOrderLowerBoundLogStmt 𝒮 := H.constantOrderLowerBoundLog
assert_uses convergenceOfIDLA_conditional constantOrderLowerBoundLog

/-- **Lemma 6.8**, E-A10 (b) form. -/
example (H : MainHypotheses 𝒮) : ConstantOrderLowerBoundDivLogStmt 𝒮 := H.constantOrderLowerBoundDivLog
assert_uses convergenceOfIDLA_conditional constantOrderLowerBoundDiv_of_inputs

/-- **Lemma 6.9**, E-A10 (b) form. -/
example (H : MainHypotheses 𝒮) : ChanceOfBeingAbsorbedLogLossStmt 𝒮 := H.chanceOfBeingAbsorbedLogLoss
assert_uses convergenceOfIDLA_conditional chanceOfBeingAbsorbedLogLoss_of_steps

/-- **Lemma 6.10**. -/
example (H : MainHypotheses 𝒮) : IterativeBoundStmt 𝒮 := H.iterativeBound
assert_uses convergenceOfIDLA_conditional iterativeBound

/-! ## Section 7 -/

/-- **Proposition 7.1**. -/
example (H : MainHypotheses 𝒮) : DivSandpileUpperBoundStmt 𝒮 := H.divSandpileUpperBound
assert_uses convergenceOfIDLA_conditional divSandpileUpperBound_of_meshScaling

/-- **Lemma 7.2**, corrected form (E-c3-2). -/
example (H : MainHypotheses 𝒮) : MassBoundOdometerAboveScaleStmt 𝒮 := H.massBoundOdometerAboveScale
assert_uses convergenceOfIDLA_conditional massBoundOdometerAboveScale_of_corrected

/-- **Lemma 7.3**, proved. -/
example : OdometerBoundMassStmt 𝒮 := MainHypotheses.odometerBoundMass 𝒮
assert_uses convergenceOfIDLA_conditional odometerBoundMass_of_corrected

/-- **Lemma 7.4**. -/
example (H : MainHypotheses 𝒮) : CrudeUpperBoundStmt 𝒮 := H.crudeUpperBound
assert_uses convergenceOfIDLA_conditional crudeUpperBound_of_corrected

/-! ## Proved inputs -/

assert_uses convergenceOfIDLA_conditional adjacentCellsMeetAeStep
assert_uses convergenceOfIDLA_conditional Absorption.absorptionChernoffStep

/-! ## Controls: committed reductions that the composition routes around (Draft or false-step routes) -/

assert_not_uses convergenceOfIDLA_conditional subsequentialConvergence_of_steps
assert_not_uses convergenceOfIDLA_conditional subsequentialProperties_of_steps
assert_not_uses convergenceOfIDLA_conditional divSandpileUpperBound_of_carved_inputs
assert_not_uses convergenceOfIDLA_conditional odometerBoundMass_of_draft
assert_not_uses convergenceOfIDLA_conditional crudeUpperBound_of_draft
assert_not_uses convergenceOfIDLA_conditional constantOrderLowerBoundDiv_of_steps
assert_not_uses convergenceOfIDLA_conditional iterativeBound_of_inputs
assert_not_uses convergenceOfIDLA_conditional chanceOfBeingAbsorbedLogLoss_of_div
assert_not_uses convergenceOfIDLA_conditional convergenceNormalizedExitTime_of_interior_discrete_boundary
assert_not_uses convergenceOfIDLA_conditional subsequentialProperties_of_corrected

end MatedCRT.Audit.Main
