import MatedCRT.Defs.WalkDisconnection
import MatedCRT.Defs.Setting

/-! # Annulus disconnection estimate for the mated-CRT map -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- Gwynne, Miller and Sheffield, *Harmonic functions on mated-CRT maps*,
arXiv:1807.07511v3, Lemma 3.11, equation (3.35), p. 31. For a
`γ`-quantum cone and its independent space-filling SLE, with `0 < γ < 2`
and `0 < ρ < 1`, the walk started at any cell meeting `B_r(z)` has a
uniformly positive quenched probability to disconnect the cells meeting
`∂B_{r/2}(z)` from those meeting `∂B_{2r}(z)` before hitting the latter.
The estimate holds simultaneously for `z ∈ B_ρ(0)` and
`ε^β ≤ r ≤ ρ` with `B_{2r}(z) ⊆ B_ρ(0)`, except with probability
`O(ε^α)`; `α, β` depend only on `γ`, and the positive lower bound on
`γ, ρ`. The probability of a possibly nonmeasurable exceptional set is
understood as outer measure. -/
def GMSAnnulusDisconnectionStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ p : ℝ, 0 < p ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < 1 →
    S.P {ω | ¬ ∀ z ∈ ball (0 : ℂ) ρ, ∀ r : ℝ,
      ε ^ β ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball 0 ρ →
      ∀ x ∈ cellVertices ε (S.η ω) (ball z r),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) x
          {w | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (r / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * r))) y w}} ≤
      ENNReal.ofReal (C * ε ^ α)

end MatedCRT

namespace MatedCRT

open MeasureTheory Set

/-- Gwynne, Miller and Sheffield, *Harmonic functions on mated-CRT maps*,
arXiv:1807.07511v3, Lemma 3.10, equation (3.34), p. 31 (itself attributed
to GMS18, Lemma 3.12). This is the restriction to locally finite multigraphs
whose vertex set is `ℤ`, matching the walk used in this repository. Assume
that the graph is connected and the walk from every vertex almost surely hits
`A` in finite time. For `x, y ∉ A`, the total variation distance of the two
first-hit laws is bounded by the probability that the walk from `x` fails to
disconnect `y` from `A` before hitting `A`. The pointwise set inequality is
equivalent to the total variation bound for probability laws on `ℤ`. -/
def GMSFirstHitComparisonStmt : Prop :=
  ∀ m : ℤ → ℤ → ℕ,
    (∀ a b, m a b = m b a) → (∀ a, m a a = 0) →
    (∀ a, {b | m a b ≠ 0}.Finite) →
    (adjGraph m).Connected →
    ∀ A : Set ℤ, (∀ a, ∀ᵐ w ∂srwLaw m a, vHitTime A w < ⊤) →
    ∀ x y : ℤ, x ∉ A → y ∉ A → ∀ B : Set ℤ,
      |(srwLaw m x {w | vExitPosition Aᶜ w ∈ B}).toReal -
        (srwLaw m y {w | vExitPosition Aᶜ w ∈ B}).toReal| ≤
      (srwLaw m x {w | ¬ walkDisconnectsBeforeHit m A y w}).toReal

end MatedCRT
