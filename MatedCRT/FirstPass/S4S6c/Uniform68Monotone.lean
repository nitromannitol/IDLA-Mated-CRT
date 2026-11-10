import MatedCRT.FirstPass.S6f.UniformEvents
import MatedCRT.FirstPass.S4S6c.Uniform68Local

/-!
# Monotonicity of the Lemma 6.8 events in the exponent `ω₀` (q2, task fp-S4S6c-envscaling-6-7-6-8)

The uniform event sets of q1 (`MatedCRT.FirstPass.S6f.UniformEvents`) are indexed by an exponent `ω₀`: the Green event
`greenLowEvent68 S ω₀ ρ CG ε` quantifies over vertices `a ∈ B_{ρ - ε^{ω₀}}` and scales `r ≥ ε^{ω₀}`. Decreasing `ω₀`
enlarges the scale range `[ε^{ω₀}, ...)` only from above and shrinks the vertex ball, so the event for the larger exponent
implies the event for the smaller one. This is what lets the target `UniformConstantOrderLowerBoundStmt` choose `ω₀` small
enough for the exit threshold relation `ε^α ≤ R/100` (the relation `(2 + 2ζ) ω₀ ≤ α`).

Terminology: Green kernel of the walk killed on leaving the window (Berestycki-Gwynne); Draft Lemma 2.16.
-/

open MeasureTheory Metric Set

namespace MatedCRT

/-- Decreasing the Green exponent weakens the Green event: `greenLowEvent68` at `ω₀` implies it at `ω₀' ≤ ω₀`
(for `0 < ε < 1`). -/
theorem greenLowEvent68_subset_of_le {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ω₀ ω₀' ρ CG ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (h : ω₀' ≤ ω₀) :
    greenLowEvent68 S ω₀ ρ CG ε ⊆ greenLowEvent68 S ω₀' ρ CG ε := by
  intro ω hω
  have hpow : ε ^ ω₀ ≤ ε ^ ω₀' := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le h
  unfold greenLowEvent68 at hω ⊢
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro a ha r hr hr' b hb
  have ha' : a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)) :=
    Uniform68Local.cellVertices_mono_local (Metric.ball_subset_ball (by linarith)) ha
  exact hω a ha' r (by linarith) hr' b hb

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.greenLowEvent68_subset_of_le
