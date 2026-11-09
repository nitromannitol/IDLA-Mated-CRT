import MatedCRT.FirstPass.S4S6c.AmplifiedBound
import MatedCRT.FirstPass.S4S6c.SuccessiveTests

/-!
# LEMMA68 eqs (30)-(31): amplification from successive local tests (q2, task fp-S4S6c)

LEMMA68.md (lines 510-530, "Combining (29)-(32) proves (3)"): `N` successive local tests, each with conditional passing
probability at least `q(r) = c/(1+|log r|)²` from every state of the set `Y` (eq (30)), give probability at most `(1-q(r))^N`
that all tests are passed (eq (31), `srwLaw_successive_tests_le_pow`). With `N ≥ κ r^{-ζ}` (eq (32)) and the eventual
estimate `eventually_amplified_le_half`, this is at most `1/2` for all sufficiently small `r`.

The stopping and state conditions are the abstract ones of `srwLaw_successive_tests_le_pow`; the concrete tests of LEMMA68
(eqs (27)-(29)) remain to be instantiated (see the report). The per-test bound is taken for every radius, so that the
eventual statement is uniform in `N`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MatedCRT

/-- **Amplification from successive tests** (LEMMA68 eqs (30)-(32)): with the per-test bound `1 - c/(1+|log r|)²` (eq (30)),
for all small `r` and all `N ≥ κ r^{-ζ}`, the probability that the first `N` successive tests are all passed is at most `1/2`. -/
theorem srwLaw_successive_tests_le_half {c κ ζ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (hζ : 0 < ζ)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (τ : ℕ → (ℕ → ℤ) → ℕ∞)
    (G : ℕ → ℤ → Set (ℕ → ℤ)) (hG : ∀ N y, MeasurableSet (G N y))
    {Y : Set ℤ}
    (hcr : ∀ r : ℝ, ∀ N : ℕ, ∀ y ∈ Y, srwLaw m y (G N y) ≤ ENNReal.ofReal (1 - c / (1 + |Real.log r|) ^ 2))
    (S : ℕ → Set (ℕ → ℤ)) (hS0 : S 0 = univ)
    (hSsucc : ∀ N, S (N + 1) = S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ G N (x k)})
    (hstop : ∀ N k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      S N ∩ {x | τ N x = k} = {x | pathHist k x ∈ F})
    (hSY : ∀ N, ∀ x ∈ S N, ∀ k : ℕ, τ N x = k → x k ∈ Y) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ N : ℕ, κ * r ^ (-ζ) ≤ N → srwLaw m a (S N) ≤ ENNReal.ofReal (1 / 2) := by
  filter_upwards [eventually_amplified_le_half hc hκ hζ, eventually_div_one_add_abs_log_sq_le_one hc] with r hamp hq1 N hN
  have hq0 : 0 ≤ 1 - c / (1 + |Real.log r|) ^ 2 := by linarith
  calc srwLaw m a (S N) ≤ (ENNReal.ofReal (1 - c / (1 + |Real.log r|) ^ 2)) ^ N :=
        srwLaw_successive_tests_le_pow m a τ G hG (hcr r) S hS0 hSsucc hstop hSY N
    _ = ENNReal.ofReal ((1 - c / (1 + |Real.log r|) ^ 2) ^ N) := (ENNReal.ofReal_pow hq0 N).symm
    _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal (hamp N hN)

#print axioms MatedCRT.srwLaw_successive_tests_le_half

end MatedCRT
