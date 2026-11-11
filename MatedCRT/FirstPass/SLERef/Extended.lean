import MatedCRT.FirstPass.SLERef.Reference
import MatedCRT.External.SLE
import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.Frozen.S1d
import MatedCRT.FirstPass.Frozen.S3S4b
import MatedCRT.FirstPass.Frozen.S4S6c
import MatedCRT.Steps.Sec1.Convergence

/-!
# Extended SLE reference package

`SLEReferenceExtendedInput ν` extends the certified reference package `SLEReferenceInput ν` by eight clauses:

* `SLEModelClosureClause` (RETIRED, FALSE): the uniform closure clause for `SLEModelClosureInput 𝒮`, the conjunction of the three SLE
  closure inputs `SLEScaleInvarianceInput`, `SLEReparametrizationInput`, `SLEIndepMonoInput` (Miller–Sheffield,
  *Imaginary Geometry IV*, §§1.2.3, 4.3);
* uniform literature clauses `MepsScalingClause`, `DegreeBoundClause`, `CellSizeEstimateClause`,
  `CountingMeasureConvergenceClause`, `DegreeMeasureConvergenceClause`;
* environment clauses `FrozenConeScalingClause` and `FrozenLBMGreenOccupationClause`, which concern the cone field and
  the LQG/LBM environment, not the SLE marginal.

Every clause has the form `∀ 𝒮, HasNormalizedSLELaw 𝒮 ν → X 𝒮`, as the existing clauses of `SLEReferenceInput`.
`SLEReferenceInput` itself is not changed, since `SLEReferenceExistsInput` (frozen) is stated through it.

REPAIR. `SLEModelClosureClause` is FALSE (`HasNormalizedSLELaw` does not give closure of the raw predicate `IsSLE`), so `SLEReferenceExtendedExistsInput` is FALSE as typed and is RETIRED. The corrected package `SLEReferenceExtendedCorrectedInput` drops the closure clause; closure is the per-model hypothesis `SLEModelClosureInput 𝒮`, taken explicitly. The seven analytic clauses are kept. Truth-checked: the seven analytic clauses are TRUE; an earlier FALSE verdict is withdrawn, since `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling. The clauses are kept unchanged; `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`) is the per-model alternative.

`ConeEnvironmentScalingUnderSLE 𝒮` is NOT derived here: under the closure clause it is equivalent to
`ConeEnvironmentScalingStep 𝒮`, which is FALSE (`FrozenConeEnvironmentScaling`, `Frozen/S3S4.lean`). See `coneEnvironmentScalingUnderSLE_iff`.
-/

namespace MatedCRT

open MeasureTheory

/-- One certified closure clause for a model `𝒮`: the three SLE closure properties of the predicate `IsSLE`, namely
scale invariance (`SLEScaleInvarianceInput`), closure under increasing reparametrization (`SLEReparametrizationInput`),
and monotonicity of independence (`SLEIndepMonoInput`). Source: Miller–Sheffield, *Imaginary Geometry IV*, §§1.2.3 and
4.3, as cited in `MatedCRT/External/SLE.lean` (lines 37, 46, 56). Truth-checked: UNSURE, model-dependent: true for the genuine SLE predicate, false for the constant-curve predicate of `SLEModelClosureClause`. It is a legitimate explicit per-model hypothesis. -/
def SLEModelClosureInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  SLEScaleInvarianceInput 𝒮 ∧ SLEReparametrizationInput 𝒮 ∧ SLEIndepMonoInput 𝒮

/-- RETIRED (FALSE, vacuous helper, not used by counted closures). Uniform closure clause of the reference
package: every model with normalized law `ν` satisfies `SLEModelClosureInput`. Source: Miller–Sheffield, *Imaginary Geometry
IV*, §§1.2.3, 4.3. Counterexample (constant-curve predicate): let `𝒮.IsSLE … η` mean that `η` is constantly `1`. No accepted
curve has an `IsLebesgueRepresentative`, since such a representative would force `η 0 = 0`; hence `HasNormalizedSLELaw 𝒮 ν`
holds vacuously for every `ν`. On a one-point probability space, scaling the accepted constant curve by `2` gives a rejected
curve, so closure fails. Replaced in the corrected package by the per-model hypothesis `SLEModelClosureInput 𝒮`. Kept
unchanged, never deleted. -/
def SLEModelClosureClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → SLEModelClosureInput 𝒮

/-- Uniform clause: every model with normalized law `ν` satisfies `MepsScalingInput` (the scaling `C⁻¹ε⁻¹ ≤ m_ε ≤ Cε⁻¹`).
Source: Berestycki–Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, arXiv:2003.10320, eq. (1.8),
as cited in `MatedCRT/External/SLE.lean` (line 63). Truth-checked: TRUE (an earlier FALSE verdict is withdrawn: `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling). Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def MepsScalingClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → MepsScalingInput 𝒮

/-- Uniform clause: every model with normalized law `ν` satisfies `DegreeBoundInput`. Source: Gwynne–Miller–Sun (GMS19),
Lemma 2.6, as cited in `MatedCRT/External/SLE.lean` (line 70). Truth-checked: TRUE (an earlier FALSE verdict is withdrawn: `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling). Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def DegreeBoundClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → DegreeBoundInput 𝒮

/-- Uniform clause: every model with normalized law `ν` satisfies `CellSizeEstimateStmt` (the cell-size estimate).
Source: Berestycki–Gwynne, arXiv:2003.10320, Lemma 2.4 (printed Lemma 2.8, `MatedCRT/Draft/Section2.lean:131`).
Truth-checked: TRUE (an earlier FALSE verdict is withdrawn: `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling). Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def CellSizeEstimateClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → CellSizeEstimateStmt 𝒮

/-- Uniform clause: every model with normalized law `ν` satisfies `CountingMeasureConvergenceStmt`. Source:
Berestycki–Gwynne, arXiv:2003.10320, Lemma A.4 (printed Lemma 2.9, `MatedCRT/Draft/Section2.lean:143`). Truth-checked: TRUE (an earlier FALSE verdict is withdrawn: `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling). Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def CountingMeasureConvergenceClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → CountingMeasureConvergenceStmt 𝒮

/-- Uniform clause: every model with normalized law `ν` satisfies `DegreeMeasureConvergenceStmt`. Source:
Berestycki–Gwynne, arXiv:2003.10320, Corollary A.6 (printed Lemma 2.10, `MatedCRT/Draft/Section2.lean:157`).
Truth-checked: TRUE (an earlier FALSE verdict is withdrawn: `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling). Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def DegreeMeasureConvergenceClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → DegreeMeasureConvergenceStmt 𝒮

/-- Environment clause (not an SLE-marginal clause): every model with normalized law `ν` satisfies `FrozenConeScalingLaw`,
the law-level cone scaling of the quantum cone environment. Source: Duplantier–Miller–Sheffield, *Mating of trees*,
arXiv:1409.7055v4, Proposition 4.13(i), with Duplantier–Sheffield, arXiv:0808.1560v2, Proposition 2.1 (locators as in
`MatedCRT/FirstPass/Frozen/S4S6c.lean`). Truth-checked: TRUE (an earlier FALSE verdict is withdrawn: `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling). Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def FrozenConeScalingClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → FrozenConeScalingLaw 𝒮

/-- Environment clause (LQG/LBM side, not an SLE-marginal clause): every model with normalized law `ν` satisfies
`FrozenLBMGreenOccupationRescaled`. Source: Garban–Rhodes–Vargas, *Liouville Brownian motion*, arXiv:1301.2876, the PCAF
construction and occupation identity, with the deterministic rescaling and LQG coordinate change of the Lean normalization
`2/S.m₀`. It is NOT literally GRV Theorem 2.7(1). Truth-checked: TRUE (an earlier FALSE verdict is withdrawn: `IsValid` already imposes the cone, GMC measure, clock and mating-of-trees coupling). Kept in `SLEReferenceExtendedCorrectedInput`; the per-model alternative is `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def FrozenLBMGreenOccupationClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → FrozenLBMGreenOccupationRescaled 𝒮

/-- The extended certified reference package for one law family `ν`: the existing `SLEReferenceInput ν` and the eight
clauses above. Every clause uses the same `ν` as `HasNormalizedSLELaw`.
RETIRED (FALSE, vacuous helper, not used by counted closures): unsatisfiable, because it contains the false `SLEModelClosureClause`, so its projections are vacuous. Kept unchanged (its consumers keep their hypotheses). Use `SLEReferenceExtendedCorrectedInput`. -/
def SLEReferenceExtendedInput (ν : ℝ → Measure SLEPathCode) : Prop :=
  SLEReferenceInput ν ∧ SLEModelClosureClause ν ∧ MepsScalingClause ν ∧ DegreeBoundClause ν ∧
    CellSizeEstimateClause ν ∧ CountingMeasureConvergenceClause ν ∧ DegreeMeasureConvergenceClause ν ∧
    FrozenConeScalingClause ν ∧ FrozenLBMGreenOccupationClause ν

/-- RETIRED (FALSE, vacuous helper, not used by counted closures): its closure clause makes it false for every `ν`. Never deleted; the corrected package is `SLEReferenceExtendedCorrectedInput`. FIRST-PASS FROZEN. Some law family `ν` carries the extended
reference package. Analogue of `SLEReferenceExistsInput` (`MatedCRT/FirstPass/Frozen/SLERef.lean`) for the new clauses. SUPERSEDED: it inherits the eight clauses above, hence the false closure clause; superseded by `CertifiedReferenceModel` (`MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def SLEReferenceExtendedExistsInput : Prop :=
  ∃ ν : ℝ → Measure SLEPathCode, SLEReferenceExtendedInput ν

/-- Projection: the closure clause `SLEModelClosureInput 𝒮` for every model with normalized law `ν`. -/
theorem sleModelClosure_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : SLEModelClosureInput 𝒮 :=
  hν.2.1 𝒮 h

/-- Derived from the closure clause: scale invariance of `IsSLE`, input `SLEScaleInvarianceInput 𝒮`. -/
theorem scaleInvariance_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : SLEScaleInvarianceInput 𝒮 :=
  (sleModelClosure_of_extended hν h).1

/-- Derived from the closure clause: reparametrization closure, input `SLEReparametrizationInput 𝒮`. -/
theorem reparametrization_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : SLEReparametrizationInput 𝒮 :=
  (sleModelClosure_of_extended hν h).2.1

/-- Derived from the closure clause: monotonicity of independence, input `SLEIndepMonoInput 𝒮`. -/
theorem indepMono_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : SLEIndepMonoInput 𝒮 :=
  (sleModelClosure_of_extended hν h).2.2

/-- Projection: `MepsScalingInput 𝒮` for every model with normalized law `ν`. -/
theorem mepsScaling_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : MepsScalingInput 𝒮 :=
  hν.2.2.1 𝒮 h

/-- Projection: `DegreeBoundInput 𝒮` for every model with normalized law `ν`. -/
theorem degreeBound_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : DegreeBoundInput 𝒮 :=
  hν.2.2.2.1 𝒮 h

/-- Projection: `CellSizeEstimateStmt 𝒮` for every model with normalized law `ν`. -/
theorem cellSizeEstimate_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : CellSizeEstimateStmt 𝒮 :=
  hν.2.2.2.2.1 𝒮 h

/-- Projection: `CountingMeasureConvergenceStmt 𝒮` for every model with normalized law `ν`. -/
theorem countingMeasureConvergence_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : CountingMeasureConvergenceStmt 𝒮 :=
  hν.2.2.2.2.2.1 𝒮 h

/-- Projection: `DegreeMeasureConvergenceStmt 𝒮` for every model with normalized law `ν`. -/
theorem degreeMeasureConvergence_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : DegreeMeasureConvergenceStmt 𝒮 :=
  hν.2.2.2.2.2.2.1 𝒮 h

/-- Projection: `FrozenConeScalingLaw 𝒮` for every model with normalized law `ν`. -/
theorem frozenConeScalingLaw_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : FrozenConeScalingLaw 𝒮 :=
  hν.2.2.2.2.2.2.2.1 𝒮 h

/-- Projection: `FrozenLBMGreenOccupationRescaled 𝒮` for every model with normalized law `ν`. -/
theorem frozenLBMGreenOccupation_of_extended {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceExtendedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : FrozenLBMGreenOccupationRescaled 𝒮 :=
  hν.2.2.2.2.2.2.2.2 𝒮 h

/-- Reduction, not a derivation: under the closure clause, `ConeEnvironmentScalingUnderSLE 𝒮` (three SLE premises, then
`ConeEnvironmentScalingStep 𝒮`) is equivalent to `ConeEnvironmentScalingStep 𝒮`. The conclusion is not supplied by the
package. `ConeEnvironmentScalingStep` is the statement retired as FALSE in `MatedCRT/FirstPass/Frozen/S3S4.lean`
(`FrozenConeEnvironmentScaling`). -/
theorem coneEnvironmentScalingUnderSLE_iff {𝒮 : SpaceFillingSLEModel} (hcl : SLEModelClosureInput 𝒮) :
    ConeEnvironmentScalingUnderSLE 𝒮 ↔ ConeEnvironmentScalingStep 𝒮 :=
  ⟨fun h => h hcl.1 hcl.2.1 hcl.2.2, fun h _ _ _ => h⟩

/-! ### Corrected extended package

`SLEReferenceExtendedInput` is left unchanged: its closure clause is false, so it is unsatisfiable, and changing its body
would silently change the hypotheses of the counted statements that take it. The corrected package is
`SLEReferenceExtendedCorrectedInput`: `SLEReferenceInput ν` and the seven analytic clauses, without
`SLEModelClosureClause`. Closure of the raw predicate `IsSLE` is the per-model hypothesis `hClosure : SLEModelClosureInput 𝒮`,
taken explicitly by the consumers that rescale `IsSLE`, or supplied by `CertifiedReferenceModel ν 𝒮`. -/

/-- The corrected extended reference package for one law family `ν` (new name, see above): `SLEReferenceInput ν` and the
seven analytic clauses `MepsScalingClause`, `DegreeBoundClause`, `CellSizeEstimateClause`,
`CountingMeasureConvergenceClause`, `DegreeMeasureConvergenceClause`, `FrozenConeScalingClause`,
`FrozenLBMGreenOccupationClause`. No closure clause. Truth-checked: UNSURE, model-dependent: removing the closure clause repairs the contradiction, and realizability depends on the chosen `ν` and the reference-environment witness. Not verified as TRUE as a whole: `SLEReferenceInput` carries the
unrestricted-`D` exit-time clause and `CountingMeasureConvergenceClause` is not source-exact; both are
report-only in this round. -/
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

/-- Closure consumers, explicit form (replaces `scaleInvariance_of_extended` etc. at the call sites that rescale `IsSLE`):
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

#print axioms MatedCRT.sleModelClosure_of_extended
#print axioms MatedCRT.scaleInvariance_of_extended
#print axioms MatedCRT.reparametrization_of_extended
#print axioms MatedCRT.indepMono_of_extended
#print axioms MatedCRT.mepsScaling_of_extended
#print axioms MatedCRT.degreeBound_of_extended
#print axioms MatedCRT.cellSizeEstimate_of_extended
#print axioms MatedCRT.countingMeasureConvergence_of_extended
#print axioms MatedCRT.degreeMeasureConvergence_of_extended
#print axioms MatedCRT.frozenConeScalingLaw_of_extended
#print axioms MatedCRT.frozenLBMGreenOccupation_of_extended
#print axioms MatedCRT.coneEnvironmentScalingUnderSLE_iff
