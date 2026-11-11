import Mathlib
import MatedCRT.FirstPass.S6e.C17Induction

/-!
# Lemma 6.8, the constant-order exit bound `s2 = 1/2` in the redesigned schedule (S9)

In the redesign the test radii `R_j` lie in the window `[d, d^a]` with `r^2 ≤ d < 2 r^2` (S2-S3), so
`r^2 ≤ R_j` for every test radius. The C17 chain `MatedCRT.Lemma68Induction.C17_le_half` is applied at the
exponent `p = 2`; its radius hypothesis `r ^ p / 2 < R_j` follows from `r ^ 2 ≤ R_j`. The conclusion is the
bound `1/2` for the probability of the event `H N` (no exit through the annulus after `N` tests), with a
constant that does not depend on the start vertex. The cutoff `Lemma68Cutoff.r0` depends on the start-vertex
parameter `s₀` only through the factor `(s₀ / 80) ^ (2 / p)`; the constant `s2 = 1/2` does not depend on `s₀`.
The quantifier order of S10 (choose `s2` before `s₀`, then `δ(h, s₀)`) is assembled in a later file.
-/

open MeasureTheory Set

namespace MatedCRT

namespace Lemma68Redesign

/-- The window bound `r ^ 2 ≤ R` of S2-S3 gives the bound `r ^ p / 2 < R` used by the C17 chain at `p = 2`. -/
theorem rpow_two_div_two_lt_of_sq_le {r R : ℝ} (hr : 0 < r) (h : r ^ 2 ≤ R) :
    r ^ (2 : ℝ) / 2 < R := by
  rw [Real.rpow_two]
  have hpos : 0 < r ^ 2 := by positivity
  linarith

/-- (S9, `s2 = 1/2`) In the redesigned schedule, with every test radius in the window `r ^ 2 ≤ R_j ≤ 1`,
the C17 chain bounds the probability that the first `N ≥ r ^ (-ζ) / 200` tests all fail by `1/2`, once
`r ≤ Lemma68Cutoff.r0 ρ s₀ 2 …` (the cutoff of (D3) at `p = 2`). Here `ζ ∈ (0, 1/2)` and `qStar ∈ (0, 9]`
are the constants of the per-test estimate `qStar / (1 + log (1 / R_j))^2` (S5); the statement is the
conclusion of `Lemma68Induction.C17_le_half` at `p = 2`. -/
theorem S9_one_test_le_half {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ → MeasurableSpace Ω) (hmono : Monotone m)
    (hm : ∀ j, m j ≤ mΩ) {G : ℕ → Set Ω} (hG : ∀ j, MeasurableSet (G j))
    (hGad : ∀ j, MeasurableSet[m (j + 1)] (G j)) {qStar ρ s₀ b lam cv c0 ζ r : ℝ}
    (hq : 0 < qStar) (hq9 : qStar ≤ 9) (hρ : 0 < ρ) (hs₀ : 0 < s₀) (hcv : 0 < cv)
    (hc0 : 0 < c0) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hrr0 : r ≤ Lemma68Cutoff.r0 ρ s₀ 2 b lam cv c0 (qStar / 9) ζ) (R : ℕ → Ω → ℝ)
    (hR : ∀ j, ∀ᵐ ω ∂μ, 0 < R j ω ∧ R j ω ≤ 1 ∧ r ^ 2 ≤ R j ω)
    (H : ℕ → Set Ω) (hH0 : H 0 = Set.univ) (hHs : ∀ j, H (j + 1) = H j ∩ (G j)ᶜ)
    (hstep : ∀ j, ∀ᵐ ω ∂μ, ω ∈ H j → qStar / (1 + Real.log (1 / R j ω)) ^ 2 ≤
      (μ[(G j).indicator (fun _ => (1 : ℝ)) | m j]) ω) {N : ℕ}
    (hN : r ^ (-ζ) / 200 ≤ (N : ℝ)) :
    μ.real (H N) ≤ 1 / 2 := by
  have hR' : ∀ j, ∀ᵐ ω ∂μ, 0 < R j ω ∧ R j ω ≤ 1 ∧ r ^ (2 : ℝ) / 2 < R j ω := fun j =>
    (hR j).mono fun ω h => ⟨h.1, h.2.1, rpow_two_div_two_lt_of_sq_le hr0 h.2.2⟩
  exact Lemma68Induction.C17_le_half μ m hmono hm hG hGad hq hq9 (by norm_num) hρ hs₀ hcv hc0 hζ hζ'
    hr0 hr1 hrr0 R hR' H hH0 hHs hstep hN

end Lemma68Redesign

end MatedCRT
