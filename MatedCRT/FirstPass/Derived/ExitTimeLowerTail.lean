import LatticeProb.Prob.PaleyZygmundLp
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.ExitTime

/-!
# Lower tail of the exit time from its first and `N`-th moments (BG20 Lemma 6.6, quenched)

Lemma 6.6 of Berestycki-Gwynne (arXiv 2003.10320, p. 39) bounds below the probability that the
random walk on the mated-CRT map takes at least half its expected time to exit a ball. Its proof
(the `L^q` variant of the Paley-Zygmund inequality, after (6.15)) is deterministic once the
environment is fixed: for Hölder conjugate exponents `q = p/(p-1)`, `p` and an integer `N ≥ q`,
Jensen's inequality `E[τ^q]^{1/q} ≤ E[τ^N]^{1/N}` (6.14) and Hölder's inequality give
  `((E^a τ_A - t) / (E^a τ_A^N)^{1/N})^p ≤ P^a(t < τ_A)`
(`rpow_div_exitTimeMoment_le_srwLaw`). With a lower bound `L ≤ E^a τ_A` (Proposition 4.1, (6.15))
and an upper bound `E^a τ_A^N ≤ U^N` (Proposition 5.1, (6.13)) at the level `t = L/2`:
  `(L / 2 / U)^p ≤ P^a(L/2 < τ_A)`
(`rpow_half_div_le_srwLaw`). In (6.12), `L = ε⁻¹ μ_h(B_{cr}(η(x)))` and
`U = (N!)^{1/N} C ε⁻¹ sup_z ∫ (log(1/|z-w|) + 1) dμ_h(w)`, so the factors `ε⁻¹` cancel and
`a = (2 (N!)^{1/N} C)^{-p}`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT.ExitTimeLowerTail

/-- **Paley-Zygmund inequality for the exit time** (BG20 Lemma 6.6, proof, quenched). For a
multigraph `m` on `ℤ`, a set `A`, a start `a`, Hölder conjugate exponents `p, q` and an integer
`N ≥ q`: `((E^a τ_A - t) / (E^a τ_A^N)^{1/N})^p ≤ P^a(t < τ_A)`. -/
theorem rpow_div_exitTimeMoment_le_srwLaw (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) {p q : ℝ}
    (hpq : p.HolderConjugate q) {N : ℕ} (hqN : q ≤ N) (t : ℝ≥0∞) :
    ((expectedExitTime m A a - t) / exitTimeMoment m A a N ^ (1 / (N : ℝ))) ^ p ≤
      srwLaw m a {x | t < (vExitTime A x : ℝ≥0∞)} :=
  LatticeProb.rpow_div_le_measure_lt_of_le_natCast (μ := srwLaw m a)
    (Tightness.measurable_vExitTime_coe A) hpq.symm hqN t

/-- **BG20 Lemma 6.6, quenched form.** If `L ≤ E^a τ_A` with `L < ∞` and `E^a τ_A^N ≤ U^N`, then
for Hölder conjugate exponents `p, q` and an integer `N ≥ q`:
`(L / 2 / U)^p ≤ P^a(L/2 < τ_A)`. -/
theorem rpow_half_div_le_srwLaw (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) {p q : ℝ}
    (hpq : p.HolderConjugate q) {N : ℕ} (hqN : q ≤ N) {L U : ℝ≥0∞} (hL : L ≠ ⊤)
    (hLE : L ≤ expectedExitTime m A a) (hU : exitTimeMoment m A a N ≤ U ^ N) :
    (L / 2 / U) ^ p ≤ srwLaw m a {x | L / 2 < (vExitTime A x : ℝ≥0∞)} :=
  LatticeProb.rpow_half_div_le_measure_lt (μ := srwLaw m a) (Tightness.measurable_vExitTime_coe A)
    hpq.symm hqN hL hLE hU

end MatedCRT.ExitTimeLowerTail
