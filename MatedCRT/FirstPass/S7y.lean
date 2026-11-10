import MatedCRT.FirstPass.S7x
import MatedCRT.FirstPass.SLERef.BG20

/-!
# Counting-measure clause of Lemma 2.9 with `MeasurableSet D` (fp-S7y-h29-measurable)

Operator audit (`notes/fp-gaps/CHATGPT-idla-7-8-audit-PRO.md`, the `h29` row of the hypothesis table and "The two required
interface repairs", item 2 of the minimal correction list): `CountingMeasureConvergenceStmt 𝒮`
(MatedCRT/Draft/Section2.lean:143, BG20 Lemma A.4, FROZEN) quantifies over arbitrary `D ⊆ B_ρ`, while BG20 states the
result for Borel `D`. The repair adds `MeasurableSet D` before `D ⊆ ball 0 ρ` and keeps the choice-point condition
`w k ∈ cell ε η k ∩ closure D` unchanged.

`CountingMeasureConvergenceMeasurableStmt` below is that repaired form. It is weaker than
`CountingMeasureConvergenceStmt` (it quantifies over fewer `D`), so the Draft statement implies it.

No Draft statement is edited, and no Prop is frozen.
-/

namespace MatedCRT

open MeasureTheory Set Metric

/-- **Lemma 2.9, Borel form** (lemma:mu_h-convergence, line 680; BG20 Lemma A.4; operator audit item 2). Same as
`CountingMeasureConvergenceStmt` (MatedCRT/Draft/Section2.lean:143) with `MeasurableSet D` added before `D ⊆ B_ρ`. The
choice-point condition is `w k ∈ cell ε η k ∩ closure D`, as in the Draft. -/
def CountingMeasureConvergenceMeasurableStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  _root_.HarmonicBalls.PolyHighProb S.P fun ε => {ω | ∀ (D : Set ℂ) (f : ℂ → ℝ) (w : ℤ → ℂ),
    MeasurableSet D → D ⊆ ball 0 ρ →
    (∀ x ∈ thickening (ε ^ α) D, 0 ≤ f x ∧ |f x| ≤ ε ^ (-β)) →
    (∀ x ∈ thickening (ε ^ α) D, ∀ y ∈ thickening (ε ^ α) D, |f x - f y| ≤ ε ^ (-β) * ‖x - y‖) →
    (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ closure D) →
    ε⁻¹ * ∫ x in D, f x ∂S.μ ω - ε ^ (-1 + α) ≤ ∑' k : cellVertices ε (S.η ω) D, f (w k) ∧
    ∑' k : cellVertices ε (S.η ω) D, f (w k) ≤ ε⁻¹ * ∫ x in thickening (ε ^ α) D, f x ∂S.μ ω + ε ^ (-1 + α)}

/-- The Draft counting-measure statement implies its Borel form: restrict the universal quantifier over `D` to
measurable `D`; the rest of the event is unchanged. -/
theorem countingMeasureConvergenceMeasurable_of_stmt {𝒮 : SpaceFillingSLEModel}
    (h : CountingMeasureConvergenceStmt 𝒮) : CountingMeasureConvergenceMeasurableStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨α, β, hα, hβ, hρ⟩ := h γ hγ0 hγ2
  refine ⟨α, β, hα, hβ, fun ρ hρ0 hρ1 Ω _ S hv => ?_⟩
  refine polyHighProb_of_subset_event (hρ ρ hρ0 hρ1 Ω S hv) ?_
  intro ε ω hω D f w _ hDb hf hL hw
  exact hω D f w hDb hf hL hw

end MatedCRT
