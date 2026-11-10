import MatedCRT.FirstPass.SLERef
import MatedCRT.FirstPass.Frozen.SLERef

/-!
# Closure: per-model inputs from the certified SLE reference package (task fp-Closure-counted-results and
fp-Closure-round2, worker z1)

Operator decision (lead li, 04:53 UTC; chat 160 audit of 1.4/1.6): the closed theorems for a model `𝒮` are stated
with a certified reference law `ν`: `hνE : SLEReferenceExtendedInput ν` (FirstPass/SLERef/Extended.lean; it contains
`SLEReferenceInput ν`, the five cited SLE/literature clauses, as its first component, and since the operator note of
05:37 UTC the per-model clauses of fp-SLERef-extend-package), `hνF : SLEFrozenReferenceInput ν` (the corrected Lemma 3.2
and the fixed-time truncated quenched laws), and `hLaw : HasNormalizedSLELaw 𝒮 ν`. The helpers below discharge, for the
same `ν`, the per-model inputs the package supplies: `RandomWalkToLBMStmt` (2.11), `GreenKernelUpperBoundStmt` (2.14),
`GreenKernelLowerBoundStmt` (2.16), `ExitTimeUpperBoundStmt` (2.18), `FrozenDiscreteHolderContinuityCorrected` (corrected
3.2), `FrozenTruncatedQuenchedLawsFixedTime`, and the ten extended-package inputs `SLEScaleInvarianceInput`,
`SLEReparametrizationInput`, `SLEIndepMonoInput`, `MepsScalingInput`, `DegreeBoundInput`, `CellSizeEstimateStmt`,
`CountingMeasureConvergenceStmt`, `DegreeMeasureConvergenceStmt`, `FrozenConeScalingLaw`, `FrozenLBMGreenOccupationRescaled`.
Of the eleven per-model inputs of chat 177, only `ConeEnvironmentScalingUnderSLE` is not supplied: under the closure clause
it is equivalent to the retired statement `ConeEnvironmentScalingStep` (`coneEnvironmentScalingUnderSLE_iff`).
The extended clauses are marked PENDING TRUTH CHECK in FirstPass/SLERef/Extended.lean.

Terminology: Miller–Sheffield (SLE closure properties, Imaginary Geometry IV), Duplantier–Sheffield (quantum cones and the
mated-CRT environment), Garban–Rhodes–Vargas (LBM).
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

/-! ### The extended package (`SLEReferenceExtendedInput`, fp-SLERef-extend-package): ten derivable per-model inputs -/

/-- SLE closure input `SLEScaleInvarianceInput 𝒮` (Miller–Sheffield, IG IV §1.2.3), from the extended package. -/
theorem slePkg_sleScaleInvariance {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : SLEScaleInvarianceInput 𝒮 :=
  scaleInvariance_of_extended hνE hLaw

/-- SLE closure input `SLEReparametrizationInput 𝒮` (Miller–Sheffield, IG IV §4.3), from the extended package. -/
theorem slePkg_sleReparametrization {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : SLEReparametrizationInput 𝒮 :=
  reparametrization_of_extended hνE hLaw

/-- SLE closure input `SLEIndepMonoInput 𝒮` (Miller–Sheffield, IG IV §4.3), from the extended package. -/
theorem slePkg_sleIndepMono {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : SLEIndepMonoInput 𝒮 :=
  indepMono_of_extended hνE hLaw

/-- `MepsScalingInput 𝒮` (BG20 eq. (1.8)), from the extended package. -/
theorem slePkg_mepsScaling {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : MepsScalingInput 𝒮 :=
  mepsScaling_of_extended hνE hLaw

/-- `DegreeBoundInput 𝒮` (GMS19 Lemma 2.6), from the extended package. -/
theorem slePkg_degreeBound {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : DegreeBoundInput 𝒮 :=
  degreeBound_of_extended hνE hLaw

/-- `CellSizeEstimateStmt 𝒮` (BG20 Lemma 2.4), from the extended package. -/
theorem slePkg_cellSize {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : CellSizeEstimateStmt 𝒮 :=
  cellSizeEstimate_of_extended hνE hLaw

/-- `CountingMeasureConvergenceStmt 𝒮` (BG20 Lemma A.4), from the extended package. -/
theorem slePkg_countingMeasure {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : CountingMeasureConvergenceStmt 𝒮 :=
  countingMeasureConvergence_of_extended hνE hLaw

/-- `DegreeMeasureConvergenceStmt 𝒮` (BG20 Corollary A.6), from the extended package. -/
theorem slePkg_degreeMeasure {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : DegreeMeasureConvergenceStmt 𝒮 :=
  degreeMeasureConvergence_of_extended hνE hLaw

/-- `FrozenConeScalingLaw 𝒮` (Duplantier–Sheffield, Prop. 4.13(i)), from the extended package. -/
theorem slePkg_frozenConeScaling {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenConeScalingLaw 𝒮 :=
  frozenConeScalingLaw_of_extended hνE hLaw

/-- `FrozenLBMGreenOccupationRescaled 𝒮` (Garban–Rhodes–Vargas with the coordinate change), from the extended package. -/
theorem slePkg_frozenLBM {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenLBMGreenOccupationRescaled 𝒮 :=
  frozenLBMGreenOccupation_of_extended hνE hLaw

end MatedCRT
