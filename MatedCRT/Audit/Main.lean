import MatedCRT.Assembly.Main

/-!
# Audit: the conditional Theorems 1.4 and 1.6

* `#print axioms` of `convergenceOfIDLA_conditional` and `convergenceOfDivSandpile_conditional`.
* For every numbered result on the main line, an `example` restating it from `MainHypotheses` and a check
  `assert_uses T R`: the reduction `R` occurs in the proof of the theorem `T`, transitively through the theorems
  `MainHypotheses.*` of MatedCRT/Assembly/Main.lean. A reduction dropped from the composition, or a numbered result
  routed around, makes this file fail.
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
def usesTrans (env : Environment) (root pfx target : Name) : Bool := Id.run do
  let mut todo : Array Name := #[root]
  let mut seen : NameSet := {}
  let mut fuel := 10000
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

/-- `assert_not_uses T R`: fail if the proof of `T` uses `R` (a control that `assert_uses` is not vacuous). -/
elab "assert_not_uses " t:ident r:ident : command => do
  let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let rn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo r
  if usesTrans (← getEnv) tn `MatedCRT.MainHypotheses rn then
    throwError "{tn} uses {rn}"

end MatedCRT.Audit.Main

#print axioms MatedCRT.convergenceOfIDLA_conditional
#print axioms MatedCRT.convergenceOfDivSandpile_conditional
namespace MatedCRT.Audit.Main

open MatedCRT

variable (𝒮 : SpaceFillingSLEModel)

/-! ## Theorems 1.4, 1.6 and Proposition 8.1 -/

/-- **Theorem 1.4**. -/
example (H : MainHypotheses 𝒮) : ConvergenceOfIDLAStmt 𝒮 := convergenceOfIDLA_conditional 𝒮 H
assert_uses convergenceOfIDLA_conditional convergenceOfIDLA_of_steps

/-- **Theorem 1.6**. -/
example (H : MainHypotheses 𝒮) : ConvergenceOfDivSandpileStmt 𝒮 := convergenceOfDivSandpile_conditional 𝒮 H
assert_uses convergenceOfDivSandpile_conditional convergenceOfDivSandpile_of_steps

/-- **Proposition 8.1**. -/
example (H : MainHypotheses 𝒮) : IDLAConstrainedConvergenceStmt 𝒮 := H.iDLAConstrainedConvergence
assert_uses convergenceOfIDLA_conditional iDLAConstrainedConvergence_of_steps
assert_uses convergenceOfDivSandpile_conditional iDLAConstrainedConvergence_of_steps

/-! ## Section 2 -/

/-- **Theorem 2.3**. -/
example (H : MainHypotheses 𝒮) : ConeHarmonicBallsStmt := H.coneHarmonicBalls
assert_uses convergenceOfIDLA_conditional coneHarmonicBalls_of_steps

/-- **Lemma 2.13**. -/
example : MaximumPrincipleStmt 𝒮 := MainHypotheses.maximumPrinciple 𝒮
assert_uses convergenceOfIDLA_conditional maximumPrinciple_of_steps

/-- **Lemma 2.17**. -/
example (H : MainHypotheses 𝒮) : BoundedExitTimeRVStmt := H.boundedExitTimeRV
assert_uses convergenceOfIDLA_conditional boundedExitTimeRV_of_steps

/-- **Lemma 2.19**. -/
example (H : MainHypotheses 𝒮) : ExpectedExitTimeExplicitBoundStmt 𝒮 := H.expectedExitTimeExplicitBound
assert_uses convergenceOfIDLA_conditional expectedExitTimeExplicitBound_of_steps

/-! ## Section 3 -/

/-- **Lemma 3.1**, corrected form (the Draft form is group (d) of `MainHypotheses`). -/
example (H : MainHypotheses 𝒮) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  H.discretePotentialTightnessCorrected
assert_uses convergenceOfIDLA_conditional discretePotentialTightness_of_steps

/-- **Lemma 3.3**. -/
example (H : MainHypotheses 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 := H.uniformConvergenceGreenKernel
assert_uses convergenceOfIDLA_conditional uniformConvergenceGreenKernel_of_steps

/-- **Lemma 3.5**. -/
example (H : MainHypotheses 𝒮) : DiscreteDirichletProblemStmt 𝒮 := H.discreteDirichletProblem
assert_uses convergenceOfIDLA_conditional discreteDirichletProblem_of_steps

/-- **Lemma 3.6**. -/
example (H : MainHypotheses 𝒮) : ConvergenceHarmonicFunctionsStmt 𝒮 := H.convergenceHarmonicFunctions
assert_uses convergenceOfIDLA_conditional convergenceHarmonicFunctions_of_steps

/-- **Lemma 3.7**. -/
example (H : MainHypotheses 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 := H.convergenceNormalizedExitTime
assert_uses convergenceOfIDLA_conditional convergenceNormalizedExitTime_of_interior_discrete_boundary

/-! ## Section 4 -/

/-- **Theorem 4.1**. -/
example (H : MainHypotheses 𝒮) : ConvergenceDivisibleStmt 𝒮 := H.convergenceDivisible
assert_uses convergenceOfIDLA_conditional convergenceDivisible_of_steps
assert_uses convergenceOfIDLA_conditional obstacleLimitUniqueness

/-- **Proposition 4.2**. -/
example (H : MainHypotheses 𝒮) : DivSandpileLowerBoundStmt 𝒮 := H.divSandpileLowerBound
assert_uses convergenceOfIDLA_conditional divSandpileLowerBound_of_steps
assert_uses convergenceOfIDLA_conditional divSandpileOdometerComparison_of_cellsMeet

/-- **Lemma 4.3**. -/
example (H : MainHypotheses 𝒮) : DiscreteBasicPropertiesStmt 𝒮 := H.discreteBasicProperties
assert_uses convergenceOfIDLA_conditional discreteBasicProperties_of_inputs

/-- **Lemma 4.4**, corrected form (E-c1-1; the Draft form is group (d) of `MainHypotheses`). -/
example (H : MainHypotheses 𝒮) : DiscreteLaplacianBoundCorrectedStmt 𝒮 := H.discreteLaplacianBoundCorrected
assert_uses convergenceOfIDLA_conditional discreteLaplacianBoundCorrected_of_inputs

/-- **Lemma 4.6**. -/
example (H : MainHypotheses 𝒮) : SubsequentialConvergenceStmt 𝒮 := H.subsequentialConvergence
assert_uses convergenceOfIDLA_conditional subsequentialConvergence_of_steps

/-- **Lemma 4.7**. -/
example (H : MainHypotheses 𝒮) : EquiboundedStmt 𝒮 := H.equibounded
assert_uses convergenceOfIDLA_conditional equibounded_of_steps

/-- **Lemma 4.8**. -/
example (H : MainHypotheses 𝒮) : SubsequentialPropertiesStmt 𝒮 := H.subsequentialProperties
assert_uses convergenceOfIDLA_conditional subsequentialProperties_of_steps

/-! ## Section 5 -/

/-- **Proposition 5.1**. -/
example (H : MainHypotheses 𝒮) : IDLALowerBoundStmt 𝒮 := H.iDLALowerBound
assert_uses convergenceOfIDLA_conditional iDLALowerBound_of_volumeGrowth_cellSize
assert_uses convergenceOfIDLA_conditional discreteClusterInnerBound_of_steps

/-- **Lemma 5.3**. -/
example (H : MainHypotheses 𝒮) : MeanValueInequalityStmt 𝒮 := H.meanValueInequality
assert_uses convergenceOfIDLA_conditional meanValueInequality_of_surplus

/-- **Lemma 5.4**. -/
example (H : MainHypotheses 𝒮) : LLowerBoundStmt 𝒮 := H.lLowerBound
assert_uses convergenceOfIDLA_conditional lLowerBound_of_adjacentCellsMeet

/-! ## Section 6 -/

/-- **Proposition 6.1**. -/
example (H : MainHypotheses 𝒮) : IDLAUpperBoundStmt 𝒮 := H.iDLAUpperBound
assert_uses convergenceOfIDLA_conditional IDLAUpperBound.iDLAUpperBound_of_steps

/-- **Lemma 6.4**. -/
example (H : MainHypotheses 𝒮) : GoodAnnulusPrevalenceStmt := H.goodAnnulusPrevalence
assert_uses convergenceOfIDLA_conditional goodAnnulusPrevalence_of_steps
assert_uses convergenceOfIDLA_conditional annulusIterateConeTransfer

/-- **Lemma 6.5**. -/
example (H : MainHypotheses 𝒮) : AnnulusHitStmt := H.annulusHit
assert_uses convergenceOfIDLA_conditional annulusHit_of_steps

/-- **Lemma 6.6**, proved. -/
example : AnnulusIterateStmt := annulusIterate
assert_uses convergenceOfIDLA_conditional annulusIterate

/-- **Lemma 6.7**, E-A10 (b) form. -/
example (H : MainHypotheses 𝒮) : ConstantOrderLowerBoundLogStmt 𝒮 := H.constantOrderLowerBoundLog
assert_uses convergenceOfIDLA_conditional constantOrderLowerBoundLog

/-- **Lemma 6.8**, E-A10 (b) form (the Draft form is group (d) of `MainHypotheses`). -/
example (H : MainHypotheses 𝒮) : ConstantOrderLowerBoundDivLogStmt 𝒮 := H.constantOrderLowerBoundDivLog
assert_uses convergenceOfIDLA_conditional constantOrderLowerBoundDiv_of_steps

/-- **Lemma 6.9**, E-A10 (b) form. -/
example (H : MainHypotheses 𝒮) : ChanceOfBeingAbsorbedLogLossStmt 𝒮 := H.chanceOfBeingAbsorbedLogLoss
assert_uses convergenceOfIDLA_conditional chanceOfBeingAbsorbedLogLoss_of_steps

/-- **Lemma 6.10**. -/
example (H : MainHypotheses 𝒮) : IterativeBoundStmt 𝒮 := H.iterativeBound
assert_uses convergenceOfIDLA_conditional iterativeBound

/-! ## Section 7 -/

/-- **Proposition 7.1**. -/
example (H : MainHypotheses 𝒮) : DivSandpileUpperBoundStmt 𝒮 := H.divSandpileUpperBound
assert_uses convergenceOfIDLA_conditional divSandpileUpperBound_of_carved_inputs

/-- **Lemma 7.3**. -/
example (H : MainHypotheses 𝒮) : OdometerBoundMassStmt 𝒮 := H.odometerBoundMass
assert_uses convergenceOfIDLA_conditional odometerBoundMass_of_draft

/-- **Lemma 7.4**. -/
example (H : MainHypotheses 𝒮) : CrudeUpperBoundStmt 𝒮 := H.crudeUpperBound
assert_uses convergenceOfIDLA_conditional crudeUpperBound_of_draft

/-! ## Proved inputs -/

assert_uses convergenceOfIDLA_conditional adjacentCellsMeetAeStep
assert_uses convergenceOfIDLA_conditional greenKernelLaplacianStep
assert_uses convergenceOfIDLA_conditional normExitTimeLaplacianStep
assert_uses convergenceOfIDLA_conditional Absorption.absorptionChernoffStep

/-! ## Controls: committed reductions that the composition routes around -/

assert_not_uses convergenceOfIDLA_conditional iterativeBound_of_inputs
assert_not_uses convergenceOfIDLA_conditional chanceOfBeingAbsorbedLogLoss_of_div
assert_not_uses convergenceOfIDLA_conditional discreteBasicProperties_of_steps

end MatedCRT.Audit.Main
