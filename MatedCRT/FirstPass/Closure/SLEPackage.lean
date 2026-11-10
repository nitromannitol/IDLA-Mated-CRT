import MatedCRT.FirstPass.SLERef
import MatedCRT.FirstPass.Frozen.SLERef

/-!
# Closure: per-model inputs from the certified SLE reference package (task fp-Closure-counted-results,
fp-Closure-round2 and fp-Closure-round3, worker z1)

Operator decision (lead li, 04:53 UTC; chat 160 audit of 1.4/1.6): the closed theorems for a model `𝒮` were stated with a
reference law `ν`: `hνC : SLEReferenceInput ν`, `hνE : SLEReferenceExtendedInput ν` (operator note 05:37 UTC), `hνF`, `hLaw`.
The helpers below project the per-model inputs of those packages.

SUPERSEDED (chat 186, operator 06:10 UTC): every `∀ 𝒮, HasNormalizedSLELaw 𝒮 ν → X 𝒮` clause of the reference packages is
FALSE as typed. The closed theorems of Closure/ now take one hypothesis `hC : CertifiedReferenceModel ν 𝒮`
(FirstPass/SLERef/Certified.lean) and use its projections (`hC.exitTimeUpperBound`, `hC.mepsScaling`, ...). Every `slePkg_*`
helper below is superseded (chat 186): kept, not deleted, and no longer called by Closure/.

Of the eleven per-model inputs of chat 177, only `ConeEnvironmentScalingUnderSLE` is not supplied by any package: under the
closure clause it is equivalent to the retired statement `ConeEnvironmentScalingStep` (`coneEnvironmentScalingUnderSLE_iff`).

Terminology: Miller–Sheffield (SLE closure properties, Imaginary Geometry IV), Duplantier–Sheffield (quantum cones and the
mated-CRT environment), Garban–Rhodes–Vargas (LBM).
-/

open MeasureTheory

namespace MatedCRT

/-- SUPERSEDED (chat 186). Lemma 2.11 (random walk to LBM) for a model with normalized law `ν`, from the reference package. -/
theorem slePkg_randomWalkToLBM {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : RandomWalkToLBMStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).1

/-- SUPERSEDED (chat 186). Lemma 2.14 (Green kernel upper bound) for a model with normalized law `ν`. -/
theorem slePkg_greenKernelUpper {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : GreenKernelUpperBoundStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).2.1

/-- SUPERSEDED (chat 186). Lemma 2.16 (Green kernel lower bound) for a model with normalized law `ν`. -/
theorem slePkg_greenKernelLower {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : GreenKernelLowerBoundStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).2.2.1

/-- SUPERSEDED (chat 186). Lemma 2.18 (exit time upper bound) for a model with normalized law `ν`. -/
theorem slePkg_exitTimeUpper {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : ExitTimeUpperBoundStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).2.2.2.1

/-- SUPERSEDED (chat 186). The corrected Lemma 3.2 (`FrozenDiscreteHolderContinuityCorrected`) for a model with normalized
law `ν`. -/
theorem slePkg_holder {ν : ℝ → Measure SLEPathCode} (hνF : SLEFrozenReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenDiscreteHolderContinuityCorrected 𝒮 :=
  frozenDiscreteHolder_of_frozenReferenceLaw hνF hLaw

/-- SUPERSEDED (chat 186). The fixed-time truncated quenched laws (`FrozenTruncatedQuenchedLawsFixedTime`) for a model with
normalized law `ν`. -/
theorem slePkg_truncated {ν : ℝ → Measure SLEPathCode} (hνF : SLEFrozenReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenTruncatedQuenchedLawsFixedTime 𝒮 :=
  frozenTruncatedQuenched_of_frozenReferenceLaw hνF hLaw

/-! ### The extended package (`SLEReferenceExtendedInput`, fp-SLERef-extend-package): ten derivable per-model inputs -/

/-- SUPERSEDED (chat 186). SLE closure input `SLEScaleInvarianceInput 𝒮` (Miller–Sheffield, IG IV §1.2.3). -/
theorem slePkg_sleScaleInvariance {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : SLEScaleInvarianceInput 𝒮 :=
  scaleInvariance_of_extended hνE hLaw

/-- SUPERSEDED (chat 186). SLE closure input `SLEReparametrizationInput 𝒮` (Miller–Sheffield, IG IV §4.3). -/
theorem slePkg_sleReparametrization {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : SLEReparametrizationInput 𝒮 :=
  reparametrization_of_extended hνE hLaw

/-- SUPERSEDED (chat 186). SLE closure input `SLEIndepMonoInput 𝒮` (Miller–Sheffield, IG IV §4.3). -/
theorem slePkg_sleIndepMono {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : SLEIndepMonoInput 𝒮 :=
  indepMono_of_extended hνE hLaw

/-- SUPERSEDED (chat 186). `MepsScalingInput 𝒮` (BG20 eq. (1.8)). -/
theorem slePkg_mepsScaling {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : MepsScalingInput 𝒮 :=
  mepsScaling_of_extended hνE hLaw

/-- SUPERSEDED (chat 186). `DegreeBoundInput 𝒮` (GMS19 Lemma 2.6). -/
theorem slePkg_degreeBound {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : DegreeBoundInput 𝒮 :=
  degreeBound_of_extended hνE hLaw

/-- SUPERSEDED (chat 186). `CellSizeEstimateStmt 𝒮` (BG20 Lemma 2.4). -/
theorem slePkg_cellSize {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : CellSizeEstimateStmt 𝒮 :=
  cellSizeEstimate_of_extended hνE hLaw

/-- SUPERSEDED (chat 186). `CountingMeasureConvergenceStmt 𝒮` (BG20 Lemma A.4). -/
theorem slePkg_countingMeasure {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : CountingMeasureConvergenceStmt 𝒮 :=
  countingMeasureConvergence_of_extended hνE hLaw

/-- SUPERSEDED (chat 186). `DegreeMeasureConvergenceStmt 𝒮` (BG20 Corollary A.6). -/
theorem slePkg_degreeMeasure {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : DegreeMeasureConvergenceStmt 𝒮 :=
  degreeMeasureConvergence_of_extended hνE hLaw

/-- SUPERSEDED (chat 186). `FrozenConeScalingLaw 𝒮` (Duplantier–Sheffield, Prop. 4.13(i)). -/
theorem slePkg_frozenConeScaling {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenConeScalingLaw 𝒮 :=
  frozenConeScalingLaw_of_extended hνE hLaw

/-- SUPERSEDED (chat 186). `FrozenLBMGreenOccupationRescaled 𝒮` (Garban–Rhodes–Vargas with the coordinate change). -/
theorem slePkg_frozenLBM {ν : ℝ → Measure SLEPathCode} (hνE : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenLBMGreenOccupationRescaled 𝒮 :=
  frozenLBMGreenOccupation_of_extended hνE hLaw

end MatedCRT
