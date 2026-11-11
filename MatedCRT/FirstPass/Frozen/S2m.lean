import HarmonicBalls.Defs.LQG

/-! # Frozen external input of the whole-plane LQG model

One `def` is an external input of the whole-plane LQG model step, used only as an explicit hypothesis of the existence-to-model theorem. Nothing here is proved. The statement concerns only the whole-plane GFF and its LQG measure: no cluster, odometer, harmonic ball or IDLA process occurs. The whole-plane GFF itself is not frozen: `MatedCRT.Field.wholePlaneGFF_exists` (`Proofs/Field/WholePlaneExistence.lean:46`) is proved (axioms propext, Classical.choice, Quot.sound). -/

namespace MatedCRT.FirstPass.S2m

open MeasureTheory HarmonicBalls

/-- Existence of the `γ`-LQG measure of the insertion-`γ` field on every probability space carrying a whole-plane GFF. For `0 < γ < 2`, a probability space `(Ω, P)` and a whole-plane GFF `(hC, hcirc)` (`IsWholePlaneGFF`), there is a random measure `μ` with `IsLQGMeasureOfField P γ γ hcirc μ`: almost surely `μ` is the vague limit, along the dyadic scales, of `ε^{γ²/2} e^{γ h_ε(z)} dz` for the field `h = h^ℂ − γ log|·|` (`α₀ = γ < Q_γ`, so the limit is locally finite). This is the universal form, restricted to probability spaces, of the Harmonic-Balls statement `LQGMeasureExistence` (`HarmonicBalls/Proposed/LQG.lean:66`), which is the existence part of the quantum-cone model.
Sources: Bou-Rabee and Gwynne, "Harmonic balls in Liouville quantum gravity", arXiv:2208.11795v3, Section 2.2, p. 9 (existence for this singular whole-plane field); Duplantier and Sheffield, "Liouville quantum gravity and KPZ", Invent. Math. 185 (2011), arXiv:0808.1560v2, Proposition 1.1, p. 5 (stated there for bounded domains); Berestycki and Powell, arXiv:2404.16642v2, Theorem 2.1, p. 62 (domain case).
Truth check: TRUE exactly as typed: HB arXiv:2208.11795v3, printed p. 9, equations (2.3), (2.4), (2.6) and Fact 2.1(I). The universal carrier (every probability space carrying a whole-plane GFF) follows by the measurable construction there; it is not a separately printed theorem. No change to the statement is needed. -/
def FrozenLQGMeasureExistenceInsertion : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ γ hcirc μ

end MatedCRT.FirstPass.S2m
