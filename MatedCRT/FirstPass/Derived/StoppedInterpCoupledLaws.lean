import MatedCRT.FirstPass.Derived.StoppedInterpPrefixCoupling
import MatedCRT.FirstPass.Derived.SrwHitLawSeparation

/-!
# Laws of coupled stopped interpolations

Walks coupled through a common boundary hit have the same stopped
interpolation law.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal
open MatedCRT.ExitCouplingGlue
open MatedCRTHarmonic.Markov

namespace MatedCRT

/-- A coupling agreeing through its common first hit has identical stopped
interpolation laws on the complement of the hit set. -/
theorem stoppedInterp_law_eq_of_hitTime_coupling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P Q : Ω → (ℕ → ℤ)) (hP : Measurable P) (hQ : Measurable Q)
    (B : Set ℤ) (v : ℤ → ℂ) (m : ℝ≥0)
    (hcouple : ∀ᵐ ω ∂μ, hitTime B (P ω) = hitTime B (Q ω) ∧
      ∀ n : ℕ, (n : ℕ∞) ≤ hitTime B (P ω) → P ω n = Q ω n) :
    (μ.map P).map (stoppedInterp v m Bᶜ) =
      (μ.map Q).map (stoppedInterp v m Bᶜ) := by
  have hae : (fun ω => stoppedInterp v m Bᶜ (P ω)) =ᵐ[μ]
      (fun ω => stoppedInterp v m Bᶜ (Q ω)) := by
    filter_upwards [hcouple] with ω hω
    apply stoppedInterp_eq_of_exitTime_eq_of_prefix_eq
    · simpa only [hitTime_eq_vHitTime, vHitTime] using hω.1
    · intro n hn
      apply hω.2 n
      simpa only [hitTime_eq_vHitTime, vHitTime] using hn
  rw [Measure.map_map (measurable_stoppedInterp v m Bᶜ) hP,
    Measure.map_map (measurable_stoppedInterp v m Bᶜ) hQ]
  exact Measure.map_congr hae

end MatedCRT
