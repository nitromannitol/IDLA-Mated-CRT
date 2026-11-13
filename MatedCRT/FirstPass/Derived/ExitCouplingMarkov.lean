import MatedCRT.FirstPass.Derived.MepsUpperDeterministic
import MatedCRT.FirstPass.Derived.ExitCouplingEvents

/-!
# Markov's inequality for the rescaled exit time

The exit-time tail used in the coupling of the stopped walks (Berestycki–Gwynne (2020), Proposition 6.12,
Step 2, (6.42)): from a bound `Q` on the expected exit time `E_a[τ_A]`, the probability that the exit time,
divided by the speed `m`, exceeds `ρ` is at most `Q / (m ρ)`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingMarkov

open MeasureTheory Set
open scoped ENNReal NNReal

/-- **Markov's inequality for the rescaled exit time.** If `E_a[τ_A] ≤ Q`, then the walk from `a`
exits `A` after the rescaled time `ρ` (that is, after `m ρ` steps) with probability at most `Q / (m ρ)`. -/
theorem srwLaw_exitTimeScaled_gt_le (mult : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) {m ρ : ℝ≥0}
    (hm : 0 < m) (hρ : 0 < ρ) {Q : ℝ≥0∞} (hQ : expectedExitTime mult A a ≤ Q) :
    srwLaw mult a {X | ρ < ((vExitTime A X).toNat : ℝ≥0) / m} ≤ Q / ((m * ρ : ℝ≥0) : ℝ≥0∞) := by
  have hs0 : ((m * ρ : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [Ne, ENNReal.coe_eq_zero]
    exact (mul_pos hm hρ).ne'
  have hsub : {X : ℕ → ℤ | ρ < ((vExitTime A X).toNat : ℝ≥0) / m} ⊆
      {X | ((m * ρ : ℝ≥0) : ℝ≥0∞) < (vExitTime A X : ℝ≥0∞)} := by
    intro X hX
    by_cases hv : vExitTime A X = ⊤
    · have h0 : (vExitTime A X).toNat = 0 := by rw [hv]; rfl
      have : ρ < 0 := by
        have h := hX
        simp only [mem_ofPred_eq, h0, Nat.cast_zero, zero_div] at h
        exact h
      exact absurd this (not_lt.2 zero_le)
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hv
      have hTk : (vExitTime A X).toNat = k := by rw [← hk]; simp
      have h1 : ρ < (k : ℝ≥0) / m := by
        have h := hX
        simp only [mem_ofPred_eq, hTk] at h
        exact h
      have h2 : ρ * m < k := (lt_div_iff₀ hm).1 h1
      show ((m * ρ : ℝ≥0) : ℝ≥0∞) < (vExitTime A X : ℝ≥0∞)
      rw [← hk, ENat.toENNReal_coe, mul_comm]
      exact_mod_cast h2
  refine (measure_mono hsub).trans ((srwLaw_lt_vExitTime_le mult (subset_refl A) a hs0
    ENNReal.coe_ne_top).trans ?_)
  have : exitTimeMoment mult A a 1 = expectedExitTime mult A a := by
    simp [exitTimeMoment, expectedExitTime]
  rw [this]
  exact ENNReal.div_le_div_right hQ _

end ExitCouplingMarkov
end MatedCRT
