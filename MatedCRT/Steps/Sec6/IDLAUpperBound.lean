import MatedCRT.Draft.Section5
import MatedCRT.Draft.Section6

/-!
# Proposition 6.1 (prop:IDLA-upper-bound, line 2252): carving of the proof (lines 2851-2921)

The printed proof. On `{t < T}`, release the `n = ⌊t ε⁻¹⌋` walkers stopped upon exiting `V^ε(Λ_t)`; let
`Θ_ε = A(∅; 0, …, 0 → V^ε(Λ_t))` and `P_ε` the stopped positions. Proposition 5.1 (stopped form) gives
`B⁻_{δ₁}(Λ_t) ⊆ Θ̄_ε`, so `|P_ε| ≤ n - |Θ_ε| ≤ ε⁻¹ μ_h(Λ_t \ B⁻_{δ₁}(Λ_t))`, which is `≤ 𝛅₀ ε⁻¹` once `δ₁` is small
(`μ_h(∂Λ_t) = 0`, eq:zero-measure-boundary). By the Abelian property (Lemma 6.3) the final aggregate has the law of
`A(Θ_ε; P_ε)`, and Lemma 6.10 with `Θ = Θ_ε` confines it to `B⁺_{C 𝛅₀^β}(Θ̄_ε) ⊆ B⁺_δ(Λ_t)`.

Carving (MatedCRT/Proofs/Sec6/IDLAUpperBound/OfSteps.lean, `iDLAUpperBound_of_steps`): from Lemma 6.10
(`IterativeBoundStmt`), Proposition 5.1 (`IDLALowerBoundStmt`, its stopped conjunct) and the step below. Lemma 6.3 is
used in its proved form (`AbelianIDLA.isAbelianIDLA`). Departures from the printed proof:
* **No random `s₀`.** The proof takes a random `σ(h)`-measurable `s₀` with `B_{s₀} ⋐ Λ_t` (line 2854), but Lemma 6.10
  is stated for deterministic `s₀`, and passing from the random to deterministic `s₀` would need the event
  `{B_{s₀} ⊆ Λ_t}` to be measurable. Instead Lemma 6.10 is applied to `Θ_ε ∪ V^ε(B_{δ/4})` with the deterministic
  `s₀ = δ/4`: IDLA is monotone in the initially occupied set path by path (`idlaAggregate_univ_mono`,
  MatedCRT/Proofs/IDLA/Monotone.lean), and `B⁺(B_{δ/4})` stays in `B⁺_δ(Λ_t)` since `0 ∈ Λ_t`.
* **The count of stopped walkers** uses that every cell has `μ_h`-mass `ε` (area parametrization), not Lemma 2.9:
  `μ_h(B⁻_{δ₁}(Λ_t)) ≤ μ_h(Θ̄_ε) ≤ ε |Θ_ε|` and `μ_h(Λ_t) = t`.
* **Measurability of the boundary layer** (`BoundaryLayerMeasurableStep`, a gap of the printed proof under the
  outer-probability convention of the Draft). The proof chooses `δ₁` depending on `ω` through
  `μ_h(Λ_t \ B⁻_{δ₁}(Λ_t)) → 0` (line 2875). With a deterministic `δ₁`, the event
  `{t < T, μ_h(Λ_t \ B⁻_{δ₁}(Λ_t)) ≥ 𝛅₀/2}` must have small probability; these events decrease to a null set as
  `δ₁ ↓ 0`, but continuity from above fails for outer measures, and `ω ↦ Λ_t` is not assumed measurable (the Draft
  quantifies over every family `Λ` which is almost surely the harmonic ball family). The step asks for null
  measurability of these events (as `ConvergenceDivisibleEventMeasurableStep` does for Theorem 4.1).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-- Step (measurability; gap of the printed proof, line 2875): for the harmonic ball family `Λ` (almost surely), the
events `{t < T, μ_h(Λ_t \ B⁻_{δ₁}(Λ_t)) ≥ s}` are null measurable. -/
def BoundaryLayerMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t δ₁ s : ℝ, 0 < t → 0 < δ₁ →
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧
      ENNReal.ofReal s ≤ S.μ ω (Λ ω t \ innerNbhd δ₁ (Λ ω t))} S.P

end MatedCRT
