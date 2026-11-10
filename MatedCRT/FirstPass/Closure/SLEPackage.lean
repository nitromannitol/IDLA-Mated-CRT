import MatedCRT.FirstPass.SLERef
import MatedCRT.FirstPass.Frozen.SLERef

/-!
# Closure: per-model inputs from the certified SLE reference package (task fp-Closure-counted-results, worker z1)

Operator decision (lead li, 04:53 UTC; chat 160 audit of 1.4/1.6): the closed theorems for a model `𝒮` are stated
with a certified reference law `ν`: `hνC : SLEReferenceInput ν` (the five cited numbered results, `SLECitedInputs`)
and `hνF : SLEFrozenReferenceInput ν` (the corrected Lemma 3.2 and the fixed-time truncated quenched laws), together
with `hLaw : HasNormalizedSLELaw 𝒮 ν`. The helpers below discharge, for the same `ν`, the per-model inputs the package
supplies: `RandomWalkToLBMStmt` (2.11), `GreenKernelUpperBoundStmt` (2.14), `GreenKernelLowerBoundStmt` (2.16),
`ExitTimeUpperBoundStmt` (2.18), `FrozenDiscreteHolderContinuityCorrected` (corrected 3.2), and
`FrozenTruncatedQuenchedLawsFixedTime`. Not supplied by the package (kept as hypotheses, see the report): the SLE inputs
`SLEScaleInvarianceInput`, `SLEReparametrizationInput`, `SLEIndepMonoInput`, `ConeEnvironmentScalingUnderSLE`, and the
per-model cited inputs `MepsScalingInput`, `DegreeBoundInput`, `CellSizeEstimateStmt`, `CountingMeasureConvergenceStmt`,
`DegreeMeasureConvergenceStmt`, `GreenFunctionCrudeBoundStmt`, and the frozen `FrozenLBMGreenOccupationRescaled`,
`FrozenConeScalingLaw`, `FrozenConeEnvironmentScaling`.

Terminology: Duplantier–Sheffield (quantum cones and the mated-CRT environment), Garban–Rhodes–Vargas (LBM).
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 2.11 (random walk to LBM) for a model with normalized law `ν`, from the reference package. -/
theorem slePkg_randomWalkToLBM {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : RandomWalkToLBMStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).1

/-- Lemma 2.14 (Green kernel upper bound) for a model with normalized law `ν`, from the reference package. -/
theorem slePkg_greenKernelUpper {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : GreenKernelUpperBoundStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).2.1

/-- Lemma 2.16 (Green kernel lower bound) for a model with normalized law `ν`, from the reference package. -/
theorem slePkg_greenKernelLower {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : GreenKernelLowerBoundStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).2.2.1

/-- Lemma 2.18 (exit time upper bound) for a model with normalized law `ν`, from the reference package. -/
theorem slePkg_exitTimeUpper {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : ExitTimeUpperBoundStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).2.2.2.1

/-- The corrected Lemma 3.2 (`FrozenDiscreteHolderContinuityCorrected`) for a model with normalized law `ν`. -/
theorem slePkg_holder {ν : ℝ → Measure SLEPathCode} (hνF : SLEFrozenReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenDiscreteHolderContinuityCorrected 𝒮 :=
  frozenDiscreteHolder_of_frozenReferenceLaw hνF hLaw

/-- The fixed-time truncated quenched laws (`FrozenTruncatedQuenchedLawsFixedTime`) for a model with normalized law `ν`. -/
theorem slePkg_truncated {ν : ℝ → Measure SLEPathCode} (hνF : SLEFrozenReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenTruncatedQuenchedLawsFixedTime 𝒮 :=
  frozenTruncatedQuenched_of_frozenReferenceLaw hνF hLaw

end MatedCRT
