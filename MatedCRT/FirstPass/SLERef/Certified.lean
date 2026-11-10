import MatedCRT.FirstPass.SLERef.Extended
import MatedCRT.FirstPass.SLERef.Similarity
import MatedCRT.FirstPass.Frozen.S3c
import MatedCRT.FirstPass.Frozen.S3S4

/-!
# Certified reference model of whole-plane space-filling SLE (task fp-SLERef-certified-model, worker z10)

Chat 186 (`notes/fp-gaps/CHATGPT-idla-new-frozen-SLERef-BG20.md`, section "Minimal correction"): every clause of the form
`∀ 𝒮, HasNormalizedSLELaw 𝒮 ν → X 𝒮` is FALSE as typed when `X` depends on the raw predicate `IsSLE`, the field, the graph or
the clock of `𝒮`, because the normalized SLE code law does not constrain these. The repair is a predicate on the individual
model `𝒮`: `CertifiedReferenceModel ν 𝒮` is quantified per model, not over all models with normalized law `ν`.

Nothing here constructs an SLE, a field or a law. The conjuncts of `CertifiedReferenceModel` are the existing Props, and the
projections below select one conjunct each, for the closure consumer `MatedCRT/FirstPass/Closure/SLEPackage.lean`.

`ConeEnvironmentScalingUnderSLE 𝒮` (`MatedCRT/FirstPass/Frozen/S1d.lean:38`) is NOT a conjunct. Under the closure input
`SLEModelClosureInput 𝒮` it is equivalent to the retired `ConeEnvironmentScalingStep 𝒮`
(`coneEnvironmentScalingUnderSLE_iff`, `MatedCRT/FirstPass/SLERef/Extended.lean`); that reduction is left to the operator.
-/

namespace MatedCRT

open MeasureTheory

/-- The certified reference model for the law `ν` (FIRST-PASS, task fp-SLERef-certified-model). The model `𝒮` has normalized law
`ν` and satisfies, jointly, the following conjuncts, in this order:

1. `HasNormalizedSLELaw 𝒮 ν` (`MatedCRT/FirstPass/SLERef/Code.lean:53`);
2. `SLEModelClosureInput 𝒮`: `SLEScaleInvarianceInput`, `SLEReparametrizationInput`, `SLEIndepMonoInput`
   (`MatedCRT/External/SLE.lean:37,46,56`; Miller–Sheffield, *Imaginary Geometry IV*, §§1.2.3, 4.3);
3. `MepsScalingInput 𝒮` (`MatedCRT/External/SLE.lean:63`; Berestycki–Gwynne, arXiv:2003.10320, eq. (1.8));
4. `DegreeBoundInput 𝒮` (`MatedCRT/External/SLE.lean:70`; Gwynne–Miller–Sun, Lemma 2.6);
5. `CellSizeEstimateStmt 𝒮` (`MatedCRT/Draft/Section2.lean:131`; Berestycki–Gwynne Lemma 2.4);
6. `CountingMeasureConvergenceStmt 𝒮` (`MatedCRT/Draft/Section2.lean:143`; Berestycki–Gwynne Lemma A.4);
7. `DegreeMeasureConvergenceStmt 𝒮` (`MatedCRT/Draft/Section2.lean:157`; Berestycki–Gwynne Corollary A.6);
8. `FrozenConeScalingLaw 𝒮` (`MatedCRT/FirstPass/Frozen/S4S6c.lean:27`; Duplantier–Miller–Sheffield Prop. 4.13(i));
9. `FrozenLBMGreenOccupationRescaled 𝒮` (`MatedCRT/FirstPass/Frozen/S3S4b.lean:83`; Garban–Rhodes–Vargas, arXiv:1301.2876,
   with the Lean normalization `2/S.m₀`);
10. `HasReferenceEnvironments 𝒮` (`MatedCRT/FirstPass/SLERef/Reference.lean`): valid environments for every `γ ∈ (0, 2)`;
11. `RandomWalkToLBMStmt 𝒮` (Theorem 2.11, `MatedCRT/Draft/Section2.lean:169`);
12. `GreenKernelUpperBoundStmt 𝒮` (Lemma 2.14, `MatedCRT/Draft/Section2.lean:191`);
13. `GreenKernelLowerBoundStmt 𝒮` (Lemma 2.16, `MatedCRT/Draft/Section2.lean:212`);
14. `ExitTimeUpperBoundStmt 𝒮` (Lemma 2.18, `MatedCRT/Draft/Section2.lean:239`);
15. `FrozenDiscreteHolderContinuityCorrected 𝒮` (corrected Lemma 3.2, `MatedCRT/FirstPass/Frozen/S3S4.lean:22`, whose body is
    `DiscreteHolderContinuityCorrectedStep 𝒮`, `MatedCRT/Steps/Sec3/DiscretePotentialTightness.lean:71`);
16. `BG20Prop51 𝒮` (`MatedCRT/FirstPass/Frozen/S3c.lean:34`; Berestycki–Gwynne Proposition 5.1, eq. (5.1));
17. `FrozenTruncatedQuenchedLawsFixedTime 𝒮` (`MatedCRT/FirstPass/Frozen/S3S4b.lean:102`);
18. `FPSimilarityTransferCorrected 𝒮` (`MatedCRT/FirstPass/SLERef/Similarity.lean:33`).

Conjuncts 2 to 18 are the per-model content of the existing package `SLEReferenceWithSimilarityInput` and of
`SLEReferenceExtendedCorrectedInput` (closure removed, operator note 07:50 UTC; conjunct 2, `SLEModelClosureInput 𝒮`, supplies the closure per model), together with `HasReferenceEnvironments` of its reference witness. The closure conjunct
`ConeEnvironmentScalingUnderSLE 𝒮` is excluded (see the module docstring). -/
def CertifiedReferenceModel (ν : ℝ → Measure SLEPathCode) (𝒮 : SpaceFillingSLEModel) : Prop :=
  HasNormalizedSLELaw 𝒮 ν ∧
  SLEModelClosureInput 𝒮 ∧
  MepsScalingInput 𝒮 ∧
  DegreeBoundInput 𝒮 ∧
  CellSizeEstimateStmt 𝒮 ∧
  CountingMeasureConvergenceStmt 𝒮 ∧
  DegreeMeasureConvergenceStmt 𝒮 ∧
  FrozenConeScalingLaw 𝒮 ∧
  FrozenLBMGreenOccupationRescaled 𝒮 ∧
  HasReferenceEnvironments 𝒮 ∧
  RandomWalkToLBMStmt 𝒮 ∧
  GreenKernelUpperBoundStmt 𝒮 ∧
  GreenKernelLowerBoundStmt 𝒮 ∧
  ExitTimeUpperBoundStmt 𝒮 ∧
  FrozenDiscreteHolderContinuityCorrected 𝒮 ∧
  BG20Prop51 𝒮 ∧
  FrozenTruncatedQuenchedLawsFixedTime 𝒮 ∧
  FPSimilarityTransferCorrected 𝒮

/-- FIRST-PASS FROZEN (task fp-SLERef-certified-model). Some law `ν` and some space-filling SLE model `𝒮` carry the
certified reference model `CertifiedReferenceModel ν 𝒮`.

Truth check: TRUE per the operator's chat 186 ruling (`notes/fp-gaps/CHATGPT-idla-new-frozen-SLERef-BG20.md`): the canonical
mated-CRT SLE/LQG model realizes all component facts jointly. This file does not re-check that ruling.
Sources: the component sources listed in `CertifiedReferenceModel`. -/
def FrozenCertifiedReferenceModelExists : Prop :=
  ∃ (ν : ℝ → Measure SLEPathCode) (𝒮 : SpaceFillingSLEModel), CertifiedReferenceModel ν 𝒮

namespace CertifiedReferenceModel

variable {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}

/-- Projection, conjunct 1: the normalized SLE law of `𝒮` is `ν`. -/
theorem hasNormalizedSLELaw (h : CertifiedReferenceModel ν 𝒮) : HasNormalizedSLELaw 𝒮 ν := h.1

/-- Projection, conjunct 2: the closure input `SLEModelClosureInput 𝒮`. -/
theorem sleModelClosure (h : CertifiedReferenceModel ν 𝒮) : SLEModelClosureInput 𝒮 := h.2.1

/-- Projection, conjunct 3: `MepsScalingInput 𝒮`. -/
theorem mepsScaling (h : CertifiedReferenceModel ν 𝒮) : MepsScalingInput 𝒮 := h.2.2.1

/-- Projection, conjunct 4: `DegreeBoundInput 𝒮`. -/
theorem degreeBound (h : CertifiedReferenceModel ν 𝒮) : DegreeBoundInput 𝒮 := h.2.2.2.1

/-- Projection, conjunct 5: `CellSizeEstimateStmt 𝒮`. -/
theorem cellSizeEstimate (h : CertifiedReferenceModel ν 𝒮) : CellSizeEstimateStmt 𝒮 := h.2.2.2.2.1

/-- Projection, conjunct 6: `CountingMeasureConvergenceStmt 𝒮`. -/
theorem countingMeasureConvergence (h : CertifiedReferenceModel ν 𝒮) : CountingMeasureConvergenceStmt 𝒮 :=
  h.2.2.2.2.2.1

/-- Projection, conjunct 7: `DegreeMeasureConvergenceStmt 𝒮`. -/
theorem degreeMeasureConvergence (h : CertifiedReferenceModel ν 𝒮) : DegreeMeasureConvergenceStmt 𝒮 :=
  h.2.2.2.2.2.2.1

/-- Projection, conjunct 8: `FrozenConeScalingLaw 𝒮`. -/
theorem frozenConeScaling (h : CertifiedReferenceModel ν 𝒮) : FrozenConeScalingLaw 𝒮 :=
  h.2.2.2.2.2.2.2.1

/-- Projection, conjunct 9: `FrozenLBMGreenOccupationRescaled 𝒮`. -/
theorem frozenLBMGreenOccupation (h : CertifiedReferenceModel ν 𝒮) : FrozenLBMGreenOccupationRescaled 𝒮 :=
  h.2.2.2.2.2.2.2.2.1

/-- Projection, conjunct 10: `HasReferenceEnvironments 𝒮`. -/
theorem hasReferenceEnvironments (h : CertifiedReferenceModel ν 𝒮) : HasReferenceEnvironments 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.1

/-- Projection, conjunct 11: `RandomWalkToLBMStmt 𝒮` (Theorem 2.11). -/
theorem randomWalkToLBM (h : CertifiedReferenceModel ν 𝒮) : RandomWalkToLBMStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.1

/-- Projection, conjunct 12: `GreenKernelUpperBoundStmt 𝒮` (Lemma 2.14). -/
theorem greenKernelUpperBound (h : CertifiedReferenceModel ν 𝒮) : GreenKernelUpperBoundStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

/-- Projection, conjunct 13: `GreenKernelLowerBoundStmt 𝒮` (Lemma 2.16). -/
theorem greenKernelLowerBound (h : CertifiedReferenceModel ν 𝒮) : GreenKernelLowerBoundStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Projection, conjunct 14: `ExitTimeUpperBoundStmt 𝒮` (Lemma 2.18). -/
theorem exitTimeUpperBound (h : CertifiedReferenceModel ν 𝒮) : ExitTimeUpperBoundStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Projection, conjunct 15: `FrozenDiscreteHolderContinuityCorrected 𝒮` (corrected Lemma 3.2). -/
theorem frozenDiscreteHolderContinuityCorrected (h : CertifiedReferenceModel ν 𝒮) :
    FrozenDiscreteHolderContinuityCorrected 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Projection, conjunct 16: `BG20Prop51 𝒮`. -/
theorem bg20Prop51 (h : CertifiedReferenceModel ν 𝒮) : BG20Prop51 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Projection, conjunct 17: `FrozenTruncatedQuenchedLawsFixedTime 𝒮`. -/
theorem frozenTruncatedQuenchedLaws (h : CertifiedReferenceModel ν 𝒮) : FrozenTruncatedQuenchedLawsFixedTime 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Projection, conjunct 18: the corrected similarity transfer `FPSimilarityTransferCorrected 𝒮`. -/
theorem similarityTransferCorrected (h : CertifiedReferenceModel ν 𝒮) : FPSimilarityTransferCorrected 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The five cited numbered results `SLECitedInputs 𝒮` (Theorem 2.11, Lemmas 2.14, 2.16, 2.18 and corrected Lemma 3.2),
assembled from conjuncts 11, 12, 13, 14 and 15. -/
theorem sleCited (h : CertifiedReferenceModel ν 𝒮) : SLECitedInputs 𝒮 :=
  ⟨h.randomWalkToLBM, h.greenKernelUpperBound, h.greenKernelLowerBound, h.exitTimeUpperBound,
    h.frozenDiscreteHolderContinuityCorrected⟩

end CertifiedReferenceModel

end MatedCRT
