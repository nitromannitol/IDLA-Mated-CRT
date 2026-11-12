import MatedCRT.FirstPass.SLERef
import MatedCRT.FirstPass.Frozen.SLERef

/-!
# Closure: per-model inputs from the certified SLE reference package

The closed theorems for a model `𝒮` were stated with a
reference law `ν`: `hνC : SLEReferenceInput ν`, `hνF`, `hLaw`.
The helpers below project the per-model inputs of those packages.

SUPERSEDED: the closed theorems of Closure/ now take one hypothesis `hC : CertifiedReferenceModel ν 𝒮`
(FirstPass/SLERef/Certified.lean) and use its projections (`hC.exitTimeUpperBound`, `hC.mepsScaling`, ...). Every `slePkg_*`
helper below is superseded and no longer called by Closure/.

Of the eleven per-model inputs, only `ConeEnvironmentScalingUnderSLE` is not supplied by any package: under the
closure clause it is equivalent to the retired statement `ConeEnvironmentScalingStep` (`coneEnvironmentScalingUnderSLE_iff`).

Terminology: Miller–Sheffield (SLE closure properties, Imaginary Geometry IV), Duplantier–Sheffield (quantum cones and the
mated-CRT environment), Garban–Rhodes–Vargas (LBM).
-/

open MeasureTheory

namespace MatedCRT

/-- SUPERSEDED. Lemma 2.11 (random walk to LBM) for a model with normalized law `ν`, from the reference package. -/
theorem slePkg_randomWalkToLBM {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : RandomWalkToLBMStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).1

/-- SUPERSEDED. Lemma 2.14 (Green kernel upper bound) for a model with normalized law `ν`. -/
theorem slePkg_greenKernelUpper {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : GreenKernelUpperBoundStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).2.1

/-- SUPERSEDED. Lemma 2.16 (Green kernel lower bound) for a model with normalized law `ν`. -/
theorem slePkg_greenKernelLower {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : GreenKernelLowerBoundStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).2.2.1

/-- SUPERSEDED. Lemma 2.18 (exit time upper bound) for a model with normalized law `ν`. -/
theorem slePkg_exitTimeUpper {ν : ℝ → Measure SLEPathCode} (hνC : SLEReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : ExitTimeUpperBoundStmt 𝒮 :=
  (slecited_of_referenceLaw hνC hLaw).2.2.2.1

/-- SUPERSEDED. The corrected Lemma 3.2 (`FrozenDiscreteHolderContinuityCorrected`) for a model with normalized
law `ν`. -/
theorem slePkg_holder {ν : ℝ → Measure SLEPathCode} (hνF : SLEFrozenReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenDiscreteHolderContinuityCorrected 𝒮 :=
  frozenDiscreteHolder_of_frozenReferenceLaw hνF hLaw

/-- SUPERSEDED. The fixed-time truncated quenched laws (`FrozenTruncatedQuenchedLawsFixedTime`) for a model with
normalized law `ν`. -/
theorem slePkg_truncated {ν : ℝ → Measure SLEPathCode} (hνF : SLEFrozenReferenceInput ν)
    {𝒮 : SpaceFillingSLEModel} (hLaw : HasNormalizedSLELaw 𝒮 ν) : FrozenTruncatedQuenchedLawsFixedTime 𝒮 :=
  frozenTruncatedQuenched_of_frozenReferenceLaw hνF hLaw

end MatedCRT
