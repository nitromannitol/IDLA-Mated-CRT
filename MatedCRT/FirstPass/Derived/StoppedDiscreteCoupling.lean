import MatedCRT.FirstPass.Derived.StoppedDiscreteInterpolation
import MatedCRT.FirstPass.Derived.SrwHitLawSeparation

/-!
# Coupling stopped discrete trajectories

Paths agreeing through a common boundary hit have the same stopped trajectory.
-/

set_option autoImplicit false

open MeasureTheory
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open MatedCRTHarmonic.Markov

namespace MatedCRT

/-- Paths that agree through their common exit time have equal stopped paths. -/
theorem stoppedPath_eq_of_exitTime_eq_of_prefix_eq (A : Set ℤ) (x y : ℕ → ℤ)
    (ht : vExitTime A x = vExitTime A y)
    (hp : ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime A x → x n = y n) :
    stoppedPath A x = stoppedPath A y := by
  funext n
  unfold stoppedPath
  rw [← ht]
  apply hp
  exact le_trans (ENat.natCast_toNat_le_self _) (min_le_left _ _)

/-- A common-hit coupling identifies the laws of the stopped trajectories. -/
theorem stoppedPath_law_eq_of_hitTime_coupling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P Q : Ω → (ℕ → ℤ)) (hP : Measurable P) (hQ : Measurable Q)
    (B : Set ℤ)
    (hcouple : ∀ᵐ ω ∂μ, hitTime B (P ω) = hitTime B (Q ω) ∧
      ∀ n : ℕ, (n : ℕ∞) ≤ hitTime B (P ω) → P ω n = Q ω n) :
    (μ.map P).map (stoppedPath Bᶜ) = (μ.map Q).map (stoppedPath Bᶜ) := by
  have hae : (fun ω => stoppedPath Bᶜ (P ω)) =ᵐ[μ]
      (fun ω => stoppedPath Bᶜ (Q ω)) := by
    filter_upwards [hcouple] with ω hω
    apply stoppedPath_eq_of_exitTime_eq_of_prefix_eq
    · simpa only [hitTime_eq_vHitTime, vHitTime] using hω.1
    · intro n hn
      apply hω.2 n
      simpa only [hitTime_eq_vHitTime, vHitTime] using hn
  rw [Measure.map_map (measurable_stoppedPath Bᶜ) hP,
    Measure.map_map (measurable_stoppedPath Bᶜ) hQ]
  exact Measure.map_congr hae

end MatedCRT
