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
