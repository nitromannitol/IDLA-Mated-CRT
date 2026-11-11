import MatedCRT.FirstPass.S2g.LawCoded
import MatedCRT.FirstPass.S4d.RescaledMeasurable

/-! # Lemma 2.6 in coded law from the raw law (FirstPass G9)

Closure gap G9: `firstPass_5_3_final` (FirstPass/S5c/FinalSurplus.lean:229) takes the coded form
`ConeScaleInvarianceCodedStmt` (FirstPass/S2g/LawCoded.lean:20) as `hLs`. The Draft statement `ConeScaleInvarianceStmt`
(Draft/Section2.lean, Lemma 2.6) equates the raw laws `P.map` of the pairs (circle average process, global family
process). The coded form asks for an `IdentDistrib` of the pairs (circle average process, global code). Besides the raw
equality, `IdentDistrib` needs the almost sure measurability of both raw pairs, which the Draft statement does not give.

Route:
* `map_code_eq`: the code map `(x, F) ↦ (x, processCode F)` is measurable (LawCode.lean), so a raw equality in law of
  measurable pairs gives an equality in law of the pairs of codes.
* `coneScaleInvarianceCoded_of_measurable`: `ConeScaleInvarianceStmt` and the a.e. measurability of the unscaled and of the
  rescaled pairs give the coded form.
* `coneScaleInvarianceCoded_of_stmt_stopped`: the a.e. measurability of the global family, unscaled and rescaled, is
  `coneGlobalFamilyAEMeasurable_of_stopped` and `coneRescaledGlobalFamilyAEMeasurable_of_stopped`
  (FirstPass/S4d/GlobalMeasurable.lean, RescaledMeasurable.lean). They use the step `ConeFamilyAEMeasurableStep`
  (Steps/Sec2/ConeHarmonicBalls.lean:31), which is neither frozen nor a Draft statement. -/

namespace MatedCRT.FirstPassG9

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

/-- The code map `(x, F) ↦ (x, processCode F)` pushes an equality in law of measurable pairs to an equality in law of the
pairs of countable codes (FirstPass/S2g/LawCode.lean). -/
theorem map_code_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {F G : Ω → X × (ℝ × ℂ → Prop)} (hF : AEMeasurable F P) (hG : AEMeasurable G P) (h : P.map F = P.map G) :
    P.map (fun ω => ((F ω).1, processCode (F ω).2)) = P.map (fun ω => ((G ω).1, processCode (G ω).2)) := by
  have hT : Measurable (fun p : X × (ℝ × ℂ → Prop) => (p.1, processCode p.2)) :=
    MatedCRT.measurable_prod_processCode
  have e1 : P.map (fun ω => ((F ω).1, processCode (F ω).2)) =
      (P.map F).map (fun p : X × (ℝ × ℂ → Prop) => (p.1, processCode p.2)) :=
    (AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hF).symm
  have e2 : P.map (fun ω => ((G ω).1, processCode (G ω).2)) =
      (P.map G).map (fun p : X × (ℝ × ℂ → Prop) => (p.1, processCode p.2)) :=
    (AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hG).symm
  rw [e1, e2, h]

/-- **Lemma 2.6, coded law, from the raw law and the measurability of the pairs (FirstPass G9).** Given the Draft statement
`ConeScaleInvarianceStmt` and, for every admissible family, the a.e. measurability of the unscaled pair (circle average
process, global family process) and of every rescaled pair, the coded form `ConeScaleInvarianceCodedStmt` holds. -/
theorem coneScaleInvarianceCoded_of_measurable (hStmt : ConeScaleInvarianceStmt)
    (hM : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) →
        AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P ∧
        ∀ b : ℝ, 0 < b → AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω)
          (coneScaleRadius γ (hcirc ω) b) b), globalFamilyProcess (rescaledFamily (Λ ω)
          (coneScaleRadius γ (hcirc ω) b) b))) P) :
    ConeScaleInvarianceCodedStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone Λ hΛ b hb
  obtain ⟨hF, hGb⟩ := hM γ hγ0 hγ2 Ω P hC hcirc μ hcone Λ hΛ
  have hmap := hStmt γ hγ0 hγ2 Ω P hC hcirc μ hcone Λ hΛ b hb
  have hT : Measurable (fun p : (Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop) => (p.1, processCode p.2)) :=
    MatedCRT.measurable_prod_processCode
  exact ⟨hT.comp_aemeasurable hF, hT.comp_aemeasurable (hGb b hb), map_code_eq hF (hGb b hb) hmap⟩

/-- **Lemma 2.6, coded law, conditional on the stopped measurability (FirstPass G9; NOT the closed G9).** From the Draft
statements `ConeScaleInvarianceStmt` (Lemma 2.6), `ConeHarmonicBallsUpToFixedTimeStmt` (Lemma 2.4) and
`ConeScaleInvarianceUpToFixedTimeStmt` (Lemma 2.5), the literature input `QuantumConeScalingInput` (which gives the radius
positivity), and the open step `ConeFamilyAEMeasurableStep`, the coded form holds. -/
theorem coneScaleInvarianceCoded_of_stmt_stopped (hStmt : ConeScaleInvarianceStmt)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hfam : ConeFamilyAEMeasurableStep) (hscale : QuantumConeScalingInput) :
    ConeScaleInvarianceCodedStmt := by
  refine coneScaleInvarianceCoded_of_measurable hStmt ?_
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone Λ hΛ
  have : IsProbabilityMeasure P := hcone.1
  refine ⟨coneGlobalFamilyAEMeasurable_of_stopped hγ0 hγ2 hcone h24 h25 hfam
    (coneScaleRadiusPosStep_of_input hscale) Λ hΛ, fun b hb => ?_⟩
  exact coneRescaledGlobalFamilyAEMeasurable_of_stopped hγ0 hγ2 hcone h24 h25 hfam
    (coneScaleRadiusPosStep_of_input hscale) Λ hΛ hb

end MatedCRT.FirstPassG9
