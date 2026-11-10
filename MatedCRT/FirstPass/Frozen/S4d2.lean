import MatedCRT.FirstPass.S2g

/-!
# First-pass frozen input of the rescaled half-ball horizon uniqueness (fp-S4d-4-2-assembly-b, q4)

EXTERNAL fact about the `γ`-quantum cone (Duplantier-Miller-Sheffield; Sheffield-Wang) used by the step
`ConeRescaledHalfBallHorizonUniqueFPStep` (`FirstPass/S4d/ScaleBridge.lean`). The step is proved from this input in
`FirstPass/S4d/HorizonUnique.lean` (`coneRescaledHalfBallHorizonUnique_fp`), via `halfBallTime_eq_of_stopped_fp`. The input
says that, for each `b > 0`, the rescaled cone measure `rescaledMeasure (μ ω) (R_b(ω)) b` (with `R_b` the cone scale radius)
is the LQG measure of a cone field on the same probability space. It is not a verbatim numbered theorem of DMS.
-/

namespace MatedCRT

open MeasureTheory

/-- FIRST-PASS FROZEN. For every `γ`-quantum cone `(P, hC, hcirc, μ)` with `0 < γ < 2` and every `b > 0`, almost surely the
cone scale radius `R_b = coneScaleRadius γ (hcirc ω) b` is positive, and the rescaled measure `ω ↦ rescaledMeasure (μ ω) R_b b`
admits a cone-field representation `(hCb, hcircb)` on the same `(Ω, P)`: `IsConeField γ P hCb hcircb` with that measure.
Sources: Duplantier-Miller-Sheffield, "Liouville quantum gravity as a mating of trees" (arXiv:1409.7055v4), Definition 4.10
(p. 79) and Proposition 4.13(i) (p. 80), the circle average embedding adding `C/γ` with `C = -log b`, which preserves the cone
law after the dilation `R_b`; Sheffield-Wang (arXiv:1605.06171v2), Theorem 1.4 (p. 3), with constant Weyl scaling, for the
measure identity `μ_{h^b} = b⁻¹ (z ↦ z/R_b)_* μ_h` almost surely. The paper's Fact 2.2(III)-(IV) records the same facts
(`paper/idla_mated_crt-corrected.tex`). Not a verbatim numbered theorem of DMS: the representation on the same probability
space is the consequence of those facts. Truth check TRUE (chat 153; notes/fp-gaps/CHATGPT-q4-hRU.md section 3).
Used by: coneRescaledHalfBallHorizonUnique_fp (MatedCRT/FirstPass/S4d/HorizonUnique.lean). -/
def ConeRescaledMeasureIsConeFieldInput : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ),
    IsConeField γ P hC hcirc μ →
  ∀ b : ℝ, 0 < b →
    (∀ᵐ ω ∂P,
      0 < coneScaleRadius γ (hcirc ω) b) ∧
    ∃ (hCb : Ω → (ℂ → ℝ) → ℝ)
      (hcircb : Ω → ℝ → ℂ → ℝ),
      IsConeField γ P hCb hcircb
        (fun ω =>
          rescaledMeasure
            (μ ω)
            (coneScaleRadius γ (hcirc ω) b)
            b)

end MatedCRT
