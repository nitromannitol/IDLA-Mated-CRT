import MatedCRT.FirstPass.SLERef.Code
import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3

/-!
# First pass: reference propositions for the space-filling SLE law (task fp-SLERef-reference-law, worker z10)

The five numbered results of the paper that are cited from the literature and whose statements quantify over valid
environments through the abstract predicate `SpaceFillingSLEModel.IsSLE`: Theorem 2.11 (`RandomWalkToLBMStmt`),
Lemma 2.14 (`GreenKernelUpperBoundStmt`), Lemma 2.16 (`GreenKernelLowerBoundStmt`), Lemma 2.18
(`ExitTimeUpperBoundStmt`) and Lemma 3.2 (`DiscreteHolderContinuityStmt`). Their Draft statements are unchanged and
are imported here; this module is not imported by the Draft modules, so there is no cycle.

`SLEReferenceInput ν` says that `ν` is a reference law: it is the normalized law of some model with valid reference
environments on `ℝ`, and every model with that normalized law satisfies the five cited statements. The corresponding
frozen proposition `SLEReferenceExistsInput` is in `MatedCRT/FirstPass/Frozen/SLERef.lean`.
-/

namespace MatedCRT

open MeasureTheory

/-- The five cited numbered results (2.11, 2.14, 2.16, 2.18, 3.2) for one space-filling SLE model `𝒮`. -/
def SLECitedInputs (𝒮 : SpaceFillingSLEModel) : Prop :=
  RandomWalkToLBMStmt 𝒮 ∧
  GreenKernelUpperBoundStmt 𝒮 ∧
  GreenKernelLowerBoundStmt 𝒮 ∧
  ExitTimeUpperBoundStmt 𝒮 ∧
  DiscreteHolderContinuityStmt 𝒮

/-- The model `𝒮` is realized by valid environments with parameter `γ` on the standard Borel space `ℝ`, for every
`γ ∈ (0, 2)`. The choice of `ℝ` is a sampling-space convention for the reference only. -/
def HasReferenceEnvironments (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ S : MatedCRTEnv ℝ, S.IsValid 𝒮 γ

/-- `ν` is a reference law for the five cited results: some model with the normalized law `ν` has valid reference
environments, and every model with the normalized law `ν` satisfies the five cited statements. -/
def SLEReferenceInput (ν : ℝ → Measure SLEPathCode) : Prop :=
  (∃ 𝒮ref : SpaceFillingSLEModel,
    HasNormalizedSLELaw 𝒮ref ν ∧ HasReferenceEnvironments 𝒮ref) ∧
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → SLECitedInputs 𝒮

end MatedCRT
