import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.FirstPass.SLERef.BG20

/-!
# First pass: corrected SLE reference clauses, items 2 and 4 (task fp-SLERef-items-2-4, worker z10)

Operator note 07:50 UTC, items 2 and 4 (`notes/fp-gaps/CHATGPT-idla-frozen-SLERef-BG20-PRO.md`). No printed statement
is edited (`Draft/`, `External/` are frozen); every corrected clause is a NEW `def`, and the printed forms are kept.

* Item 4, Lemma 2.18 (`ExitTimeUpperBoundStmt`, `MatedCRT/Draft/Section2.lean:239`). Its second clause quantifies over all
  `D ⊆ B_ρ`, which is false as cited. `ExitTimeUpperBoundBallStmt` keeps the first clause verbatim (the BG20 Proposition 5.1
  event, `BG20Prop51`) and restricts the second clause to the balls `ball x s ⊆ ball 0 ρ`, with `0 < s`
  (`notes/fp-gaps/CHATGPT-idla-exit-time-ball.md` §1, verdict TRUE). The note also offers a standalone form without the
  first clause; that form is not used here.
* Item 2, Lemma 2.9 (`CountingMeasureConvergenceStmt`, `MatedCRT/Draft/Section2.lean:143`). `CountingMeasureConvergenceCorrectedStmt`
  adds `MeasurableSet D` (the set integral `∫_D` is over a measurable set) and takes `w k ∈ cell ∩ D`. Source check: the corrected
  draft (`paper/idla_mated_crt-corrected.tex`, `lemma:mu_h-convergence`) reads `w^ε_a ∈ H^ε_a ∩ cl(D)`, so the printed `closure D`
  is the source text. The corrected clause is a weakening, and it follows from the printed clause without new mathematics
  (`countingMeasureConvergenceCorrected_of_printed`).

Packages. `SLEReferenceBallCorrectedInput ν` is `SLEReferenceExtendedCorrectedInput ν` with `SLECitedInputs` replaced by
`SLECitedInputsBall` and `CountingMeasureConvergenceClause` replaced by `CountingMeasureConvergenceCorrectedClause`. Its
universal form (`∀ 𝒮` with normalized law `ν`) inherits the open verdict of the 06:10 operator note on `SLEReferenceInput`.
`CertifiedReferenceModelBall ν 𝒮` is the per-model corrected version of `CertifiedReferenceModel ν 𝒮`: conjunct 6 is replaced by
`CountingMeasureConvergenceCorrectedStmt 𝒮` and conjunct 14 by `ExitTimeUpperBoundBallStmt 𝒮`; every other conjunct, including
`BG20Prop51 𝒮`, is unchanged.

Nothing here asserts that a family `ν` is realized by an SLE; that remains the frozen input. No existence proposition is added.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Item 4: the exit-time clause of Lemma 2.18 (Berestycki–Gwynne Proposition 5.1, Lemma A.1) for balls. The first clause is the
clause of `ExitTimeUpperBoundStmt 𝒮` (`MatedCRT/Draft/Section2.lean:239`), verbatim. The second clause is restricted to the
balls `ball x s ⊆ ball 0 ρ` with `0 < s`, with the same bound. Source: `notes/fp-gaps/CHATGPT-idla-exit-time-ball.md` §1
(verdict TRUE). It replaces `ExitTimeUpperBoundStmt 𝒮`, whose unrestricted second clause is FALSE as cited. -/
def ExitTimeUpperBoundBallStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, 0 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  HarmonicBalls.PolyHighProb S.P fun ε => {ω |
    (∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
      ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
        exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
          ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω) ^ N) ∧
    (∀ x : ℂ, ∀ s : ℝ, 0 < s → ball x s ⊆ ball 0 ρ →
      ∀ a ∈ cellVertices ε (S.η ω) (ball x s),
        ENNReal.ofReal (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball x s)) a) ≤
          expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball x s)) a ∧
        expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball x s)) a ≤
          ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) (ball x s)))}

/-- Item 2: the counting-measure clause of Lemma 2.9 (Berestycki–Gwynne Lemma A.4, `MatedCRT/Draft/Section2.lean:143`), with
`MeasurableSet D` and `w k ∈ cell ∩ D`. Weaker than `CountingMeasureConvergenceStmt 𝒮`, which it follows from
(`countingMeasureConvergenceCorrected_of_printed`). -/
def CountingMeasureConvergenceCorrectedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  HarmonicBalls.PolyHighProb S.P fun ε => {ω | ∀ (D : Set ℂ) (f : ℂ → ℝ) (w : ℤ → ℂ), MeasurableSet D → D ⊆ ball 0 ρ →
    (∀ x ∈ thickening (ε ^ α) D, 0 ≤ f x ∧ |f x| ≤ ε ^ (-β)) →
    (∀ x ∈ thickening (ε ^ α) D, ∀ y ∈ thickening (ε ^ α) D, |f x - f y| ≤ ε ^ (-β) * ‖x - y‖) →
    (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ D) →
    ε⁻¹ * ∫ x in D, f x ∂S.μ ω - ε ^ (-1 + α) ≤ ∑' k : cellVertices ε (S.η ω) D, f (w k) ∧
    ∑' k : cellVertices ε (S.η ω) D, f (w k) ≤ ε⁻¹ * ∫ x in thickening (ε ^ α) D, f x ∂S.μ ω + ε ^ (-1 + α)}

/-- The printed Lemma 2.9 (closure form) implies the corrected clause: restrict to measurable `D`, and use
`w k ∈ cell ∩ D ⊆ cell ∩ closure D`. -/
theorem countingMeasureConvergenceCorrected_of_printed {𝒮 : SpaceFillingSLEModel}
    (h : CountingMeasureConvergenceStmt 𝒮) : CountingMeasureConvergenceCorrectedStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨α, β, hα, hβ, hρ⟩ := h γ hγ0 hγ2
  refine ⟨α, β, hα, hβ, fun ρ hρ0 hρ1 Ω _ S hv => ?_⟩
  refine polyHighProb_of_subset_event (hρ ρ hρ0 hρ1 Ω S hv) ?_
  intro ε ω hω D f w _ hDb hf hL hw
  exact hω D f w hDb hf hL (fun k hk => ⟨(hw k hk).1, subset_closure (hw k hk).2⟩)

/-- The printed Lemma 2.18 implies the ball clause: the second clause of `ExitTimeUpperBoundStmt 𝒮` is used at `D = ball x s`. -/
theorem exitTimeUpperBoundBall_of_printed {𝒮 : SpaceFillingSLEModel} (h : ExitTimeUpperBoundStmt 𝒮) :
    ExitTimeUpperBoundBallStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨α, hα, hρ⟩ := h γ hγ0 hγ2
  refine ⟨α, hα, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨C, hC, hS⟩ := hρ ρ hρ0 hρ1
  refine ⟨C, hC, fun Ω _ S hv => ?_⟩
  exact polyHighProb_of_subset_event (hS Ω S hv)
    (fun ε ω hω => ⟨hω.1, fun x s _ hsub => hω.2 (ball x s) hsub⟩)

/-- The five cited numbered results with the item-4 correction: `SLECitedInputs 𝒮` with `ExitTimeUpperBoundBallStmt 𝒮` in
place of `ExitTimeUpperBoundStmt 𝒮`. -/
def SLECitedInputsBall (𝒮 : SpaceFillingSLEModel) : Prop :=
  RandomWalkToLBMStmt 𝒮 ∧
  GreenKernelUpperBoundStmt 𝒮 ∧
  GreenKernelLowerBoundStmt 𝒮 ∧
  ExitTimeUpperBoundBallStmt 𝒮 ∧
  DiscreteHolderContinuityCorrectedStep 𝒮

theorem sleCitedBall_of_printed {𝒮 : SpaceFillingSLEModel} (h : SLECitedInputs 𝒮) : SLECitedInputsBall 𝒮 := by
  obtain ⟨hRW, hGU, hGL, hEB, hDH⟩ := h
  exact ⟨hRW, hGU, hGL, exitTimeUpperBoundBall_of_printed hEB, hDH⟩

/-- Reference package with the item-4 correction: `SLEReferenceInput ν` with `SLECitedInputsBall` in the second conjunct. -/
def SLEReferenceBallInput (ν : ℝ → Measure SLEPathCode) : Prop :=
  (∃ 𝒮ref : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮ref ν ∧ HasReferenceEnvironments 𝒮ref) ∧
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → SLECitedInputsBall 𝒮

/-- Item 2 as a clause on the law family: every model with normalized law `ν` satisfies the corrected counting clause. -/
def CountingMeasureConvergenceCorrectedClause (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ 𝒮 : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮 ν → CountingMeasureConvergenceCorrectedStmt 𝒮

/-- Corrected package (new name), items 2 and 4 applied to `SLEReferenceExtendedCorrectedInput ν`: `SLEReferenceBallInput ν`
and the seven analytic clauses, with `CountingMeasureConvergenceCorrectedClause ν` in place of
`CountingMeasureConvergenceClause ν`. The closure clause is absent, as in `SLEReferenceExtendedCorrectedInput`. The
universal form `∀ 𝒮` is the open question of the 06:10 operator note (see the module docstring). -/
def SLEReferenceBallCorrectedInput (ν : ℝ → Measure SLEPathCode) : Prop :=
  SLEReferenceBallInput ν ∧ MepsScalingClause ν ∧ DegreeBoundClause ν ∧ CellSizeEstimateClause ν ∧
    CountingMeasureConvergenceCorrectedClause ν ∧ DegreeMeasureConvergenceClause ν ∧
    FrozenConeScalingClause ν ∧ FrozenLBMGreenOccupationClause ν

theorem sleReferenceBall_of_corrected {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceBallCorrectedInput ν) :
    SLEReferenceBallInput ν :=
  hν.1

theorem sleCitedBall_of_corrected {ν : ℝ → Measure SLEPathCode} (hν : SLEReferenceBallCorrectedInput ν)
    {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) : SLECitedInputsBall 𝒮 :=
  hν.1.2 𝒮 h

theorem countingMeasureConvergenceCorrected_of_corrected {ν : ℝ → Measure SLEPathCode}
    (hν : SLEReferenceBallCorrectedInput ν) {𝒮 : SpaceFillingSLEModel} (h : HasNormalizedSLELaw 𝒮 ν) :
    CountingMeasureConvergenceCorrectedStmt 𝒮 :=
  hν.2.2.2.2.1 𝒮 h

/-- Corrected certificate (new name), per model: `CertifiedReferenceModel ν 𝒮` with conjunct 6 replaced by
`CountingMeasureConvergenceCorrectedStmt 𝒮` and conjunct 14 by `ExitTimeUpperBoundBallStmt 𝒮`. All other conjuncts are as in
`CertifiedReferenceModel` (sources in its docstring, `MatedCRT/FirstPass/SLERef/Certified.lean`). -/
def CertifiedReferenceModelBall (ν : ℝ → Measure SLEPathCode) (𝒮 : SpaceFillingSLEModel) : Prop :=
  HasNormalizedSLELaw 𝒮 ν ∧
  SLEModelClosureInput 𝒮 ∧
  MepsScalingInput 𝒮 ∧
  DegreeBoundInput 𝒮 ∧
  CellSizeEstimateStmt 𝒮 ∧
  CountingMeasureConvergenceCorrectedStmt 𝒮 ∧
  DegreeMeasureConvergenceStmt 𝒮 ∧
  FrozenConeScalingLaw 𝒮 ∧
  FrozenLBMGreenOccupationRescaled 𝒮 ∧
  HasReferenceEnvironments 𝒮 ∧
  RandomWalkToLBMStmt 𝒮 ∧
  GreenKernelUpperBoundStmt 𝒮 ∧
  GreenKernelLowerBoundStmt 𝒮 ∧
  ExitTimeUpperBoundBallStmt 𝒮 ∧
  FrozenDiscreteHolderContinuityCorrected 𝒮 ∧
  BG20Prop51 𝒮 ∧
  FrozenTruncatedQuenchedLawsFixedTime 𝒮 ∧
  FPSimilarityTransferCorrected 𝒮

namespace CertifiedReferenceModelBall

variable {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}

/-- Conjunct 14: `ExitTimeUpperBoundBallStmt 𝒮`. -/
theorem exitTimeUpperBoundBall (h : CertifiedReferenceModelBall ν 𝒮) : ExitTimeUpperBoundBallStmt 𝒮 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hEB, _, _, _, _⟩ := h
  exact hEB

/-- Conjunct 6: `CountingMeasureConvergenceCorrectedStmt 𝒮`. -/
theorem countingMeasureConvergenceCorrected (h : CertifiedReferenceModelBall ν 𝒮) :
    CountingMeasureConvergenceCorrectedStmt 𝒮 := by
  obtain ⟨_, _, _, _, _, hC, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h
  exact hC

/-- The five cited numbered results with the item-4 correction, from conjuncts 11, 12, 13, 14 and 15. -/
theorem sleCitedBall (h : CertifiedReferenceModelBall ν 𝒮) : SLECitedInputsBall 𝒮 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hRW, hGU, hGL, hEB, hDH, _, _, _⟩ := h
  exact ⟨hRW, hGU, hGL, hEB, hDH⟩

/-- The printed certificate implies the corrected one: conjunct 6 by `countingMeasureConvergenceCorrected_of_printed`,
conjunct 14 by `exitTimeUpperBoundBall_of_printed`; the other conjuncts are copied. -/
theorem of_certified (h : CertifiedReferenceModel ν 𝒮) : CertifiedReferenceModelBall ν 𝒮 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, countingMeasureConvergenceCorrected_of_printed h6, h7, h8, h9, h10, h11, h12, h13,
    exitTimeUpperBoundBall_of_printed h14, h15, h16, h17, h18⟩

end CertifiedReferenceModelBall

end MatedCRT
