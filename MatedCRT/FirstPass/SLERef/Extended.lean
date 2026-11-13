import MatedCRT.FirstPass.SLERef.Reference
import MatedCRT.External.SLE
import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.Frozen.S1d
import MatedCRT.FirstPass.Frozen.S3S4b
import MatedCRT.FirstPass.Frozen.S4S6c
import MatedCRT.Steps.Sec1.Convergence

/-!
# Extended SLE reference package

`SLEReferenceExtendedCorrectedInput ν` extends the certified reference package `SLEReferenceInput ν` by seven clauses:

* uniform literature clauses `MepsScalingClause`, `DegreeBoundClause`, `CellSizeEstimateClause`,
  `CountingMeasureConvergenceClause`, `DegreeMeasureConvergenceClause`;
* environment clauses `FrozenConeScalingClause` and `FrozenLBMGreenOccupationClause`, which concern the cone field and
  the LQG/LBM environment, not the SLE marginal.

Every clause has the form `∀ 𝒮, HasNormalizedSLELaw 𝒮 ν → X 𝒮`, as the existing clauses of `SLEReferenceInput`.
`SLEReferenceInput` itself is not changed, since `SLEReferenceExistsInput` (frozen) is stated through it. The three SLE
closure properties of the predicate `IsSLE` (Miller–Sheffield, *Imaginary Geometry IV*, §§1.2.3, 4.3) form the per-model
hypothesis `SLEModelClosureInput 𝒮`, taken explicitly. Truth-checked: the seven clauses are TRUE, since `IsValid` already
imposes the cone, GMC measure, clock and mating-of-trees coupling. `CertifiedReferenceModel`
(`MatedCRT/FirstPass/SLERef/Certified.lean`) is the per-model alternative.

`ConeEnvironmentScalingUnderSLE 𝒮` is not derived here: under the closure hypothesis it is equivalent to
`ConeEnvironmentScalingStep 𝒮`, the predicate on the model `FrozenConeEnvironmentScaling` (`Frozen/S3S4.lean`). See `coneEnvironmentScalingUnderSLE_iff`.
-/

namespace MatedCRT

open MeasureTheory

/-- One certified closure clause for a model `𝒮`: the three SLE closure properties of the predicate `IsSLE`, namely
scale invariance (`SLEScaleInvarianceInput`), closure under increasing reparametrization (`SLEReparametrizationInput`),
and monotonicity of independence (`SLEIndepMonoInput`). Source: Miller–Sheffield, *Imaginary Geometry IV*, §§1.2.3 and
4.3, as cited in `MatedCRT/External/SLE.lean` (lines 37, 46, 56). Truth-checked: model-dependent; it holds for the genuine SLE predicate. It is an explicit per-model hypothesis. -/
def SLEModelClosureInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  SLEScaleInvarianceInput 𝒮 ∧ SLEReparametrizationInput 𝒮 ∧ SLEIndepMonoInput 𝒮

/-- Uniform clause: every model with normalized law `ν` satisfies `MepsScalingInput` (the scaling `C⁻¹ε⁻¹ ≤ m_ε ≤ Cε⁻¹`).
Source: Berestycki–Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, arXiv:2003.10320, eq. (1.8),
as cited in `MatedCRT/External/SLE.lean` (line 63). Truth-checked: TRUE, since `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling. Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def MepsScalingClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → MepsScalingInput 𝒮

/-- Uniform clause: every model with normalized law `ν` satisfies `DegreeBoundInput`. Source: Gwynne–Miller–Sun (GMS19),
Lemma 2.6, as cited in `MatedCRT/External/SLE.lean` (line 70). Truth-checked: TRUE, since `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling. Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def DegreeBoundClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → DegreeBoundInput 𝒮

/-- Uniform clause: every model with normalized law `ν` satisfies `CellSizeEstimateStmt` (the cell-size estimate).
Source: Berestycki–Gwynne, arXiv:2003.10320, Lemma 2.4 (printed Lemma 2.8, `MatedCRT/Draft/Section2.lean:131`).
Truth-checked: TRUE, since `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling. Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def CellSizeEstimateClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → CellSizeEstimateStmt 𝒮

/-- Uniform clause: every model with normalized law `ν` satisfies `CountingMeasureConvergenceStmt`. Source:
Berestycki–Gwynne, arXiv:2003.10320, Lemma A.4 (printed Lemma 2.9, `MatedCRT/Draft/Section2.lean:143`). Truth-checked: TRUE, since `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling. Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def CountingMeasureConvergenceClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → CountingMeasureConvergenceStmt 𝒮

/-- Uniform clause: every model with normalized law `ν` satisfies `DegreeMeasureConvergenceStmt`. Source:
Berestycki–Gwynne, arXiv:2003.10320, Corollary A.6 (printed Lemma 2.10, `MatedCRT/Draft/Section2.lean:157`).
Truth-checked: TRUE, since `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling. Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def DegreeMeasureConvergenceClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → DegreeMeasureConvergenceStmt 𝒮

/-- Environment clause (not an SLE-marginal clause): every model with normalized law `ν` satisfies `FrozenConeScalingLaw`,
the law-level cone scaling of the quantum cone environment. Source: Duplantier–Miller–Sheffield, *Mating of trees*,
arXiv:1409.7055v4, Proposition 4.13(i), with Duplantier–Sheffield, arXiv:0808.1560v2, Proposition 2.1 (locators as in
`MatedCRT/FirstPass/Frozen/S4S6c.lean`). Truth-checked: TRUE, since `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling. Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def FrozenConeScalingClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → FrozenConeScalingLaw 𝒮

/-- Environment clause (LQG/LBM side, not an SLE-marginal clause): every model with normalized law `ν` satisfies
`FrozenLBMGreenOccupationRescaled`. Source: Garban–Rhodes–Vargas, *Liouville Brownian motion*, arXiv:1301.2876, the PCAF
construction and occupation identity, with the deterministic rescaling and LQG coordinate change of the Lean normalization
`2/S.m₀`. It is NOT literally GRV Theorem 2.7(1). Truth-checked: TRUE, since `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling. Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def FrozenLBMGreenOccupationClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → FrozenLBMGreenOccupationRescaled 𝒮

/-- Reduction, not a derivation: under the closure clause, `ConeEnvironmentScalingUnderSLE 𝒮` (three SLE premises, then
`ConeEnvironmentScalingStep 𝒮`) is equivalent to `ConeEnvironmentScalingStep 𝒮`. The conclusion is not supplied by the
package. `ConeEnvironmentScalingStep` is the predicate `FrozenConeEnvironmentScaling` of
`MatedCRT/FirstPass/Frozen/S3S4.lean`. -/
theorem coneEnvironmentScalingUnderSLE_iff {𝒮 : SpaceFillingSLEModel} (hcl : SLEModelClosureInput 𝒮) :
    ConeEnvironmentScalingUnderSLE 𝒮 ↔ ConeEnvironmentScalingStep 𝒮 :=
  ⟨fun h => h hcl.1 hcl.2.1 hcl.2.2, fun h _ _ _ => h⟩

/-! ### Extended package

The package `SLEReferenceExtendedCorrectedInput` is `SLEReferenceInput ν` and the seven analytic clauses. Closure of the raw predicate `IsSLE` is the per-model hypothesis `hClosure : SLEModelClosureInput 𝒮`,
taken explicitly by the consumers that rescale `IsSLE`, or supplied by `CertifiedReferenceModel ν 𝒮`. -/

/-- The corrected extended reference package for one law family `ν`: `SLEReferenceInput ν` and the
seven analytic clauses `MepsScalingClause`, `DegreeBoundClause`, `CellSizeEstimateClause`,
`CountingMeasureConvergenceClause`, `DegreeMeasureConvergenceClause`, `FrozenConeScalingClause`,
`FrozenLBMGreenOccupationClause`. No closure clause. Truth-checked: UNSURE, model-dependent: realizability depends on the chosen `ν` and the reference-environment witness. Not verified as TRUE as a whole: `SLEReferenceInput` carries the
unrestricted-`D` exit-time clause and `CountingMeasureConvergenceClause` is not source-exact; both are
report-only. -/
def SLEReferenceExtendedCorrectedInput (ν : ℝ → Measure SLEPathCode) : Prop :=
  SLEReferenceInput ν ∧ MepsScalingClause ν ∧ DegreeBoundClause ν ∧ CellSizeEstimateClause ν ∧
    CountingMeasureConvergenceClause ν ∧ DegreeMeasureConvergenceClause ν ∧
    FrozenConeScalingClause ν ∧ FrozenLBMGreenOccupationClause ν

/-- Projection: the reference package `SLEReferenceInput ν` of the corrected package. -/
theorem sleReference_of_corrected {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedCorrectedInput ν) :
    SLEReferenceInput ν :=
  hν.1

/-- Projection: `MepsScalingInput 𝒮` for every model with normalized law `ν` (corrected package). -/
theorem mepsScaling_of_corrected {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedCorrectedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : MepsScalingInput 𝒮 :=
  hν.2.1 𝒮 h

/-- Projection: `DegreeBoundInput 𝒮` for every model with normalized law `ν` (corrected package). -/
theorem degreeBound_of_corrected {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedCorrectedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : DegreeBoundInput 𝒮 :=
  hν.2.2.1 𝒮 h

/-- Projection: `CellSizeEstimateStmt 𝒮` for every model with normalized law `ν` (corrected package). -/
theorem cellSizeEstimate_of_corrected {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedCorrectedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : CellSizeEstimateStmt 𝒮 :=
  hν.2.2.2.1 𝒮 h

/-- Projection: `CountingMeasureConvergenceStmt 𝒮` for every model with normalized law `ν` (corrected package). -/
theorem countingMeasureConvergence_of_corrected {ν : ℝ → Measure SLEPathCode}
    (hν : SLEReferenceExtendedCorrectedInput ν) {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) :
    CountingMeasureConvergenceStmt 𝒮 :=
  hν.2.2.2.2.1 𝒮 h

/-- Projection: `DegreeMeasureConvergenceStmt 𝒮` for every model with normalized law `ν` (corrected package). -/
theorem degreeMeasureConvergence_of_corrected {ν : ℝ → Measure SLEPathCode}
    (hν : SLEReferenceExtendedCorrectedInput ν) {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) :
    DegreeMeasureConvergenceStmt 𝒮 :=
  hν.2.2.2.2.2.1 𝒮 h

/-- Projection: `FrozenConeScalingLaw 𝒮` for every model with normalized law `ν` (corrected package). -/
theorem frozenConeScalingLaw_of_corrected {ν : ℝ → Measure SLEPathCode}
    (hν : SLEReferenceExtendedCorrectedInput ν) {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) :
    FrozenConeScalingLaw 𝒮 :=
  hν.2.2.2.2.2.2.1 𝒮 h

/-- Projection: `FrozenLBMGreenOccupationRescaled 𝒮` for every model with normalized law `ν` (corrected package). -/
theorem frozenLBMGreenOccupation_of_corrected {ν : ℝ → Measure SLEPathCode}
    (hν : SLEReferenceExtendedCorrectedInput ν) {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) :
    FrozenLBMGreenOccupationRescaled 𝒮 :=
  hν.2.2.2.2.2.2.2 𝒮 h

/-- Closure consumers, explicit form (at the call sites that rescale `IsSLE`):
the per-model closure hypothesis `hClosure : SLEModelClosureInput 𝒮` is taken directly. -/
theorem scaleInvariance_of_closure {𝒮 : SpaceFillingSLEModel} (hClosure : SLEModelClosureInput 𝒮) :
    SLEScaleInvarianceInput 𝒮 :=
  hClosure.1

/-- Closure consumers, explicit form: reparametrization closure from `hClosure : SLEModelClosureInput 𝒮`. -/
theorem reparametrization_of_closure {𝒮 : SpaceFillingSLEModel} (hClosure : SLEModelClosureInput 𝒮) :
    SLEReparametrizationInput 𝒮 :=
  hClosure.2.1

/-- Closure consumers, explicit form: monotonicity of independence from `hClosure : SLEModelClosureInput 𝒮`. -/
theorem indepMono_of_closure {𝒮 : SpaceFillingSLEModel} (hClosure : SLEModelClosureInput 𝒮) :
    SLEIndepMonoInput 𝒮 :=
  hClosure.2.2

end MatedCRT

#print axioms MatedCRT.coneEnvironmentScalingUnderSLE_iff
