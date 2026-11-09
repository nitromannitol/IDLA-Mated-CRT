import MatedCRT.Proofs.WalkPotential.MarkovFixedTime

/-!
# Bridge from the fixed-time Markov property to the test product (q2, task fp-S4S6c; LEMMA68 eqs (23)-(27))

`srwLaw_markov` (Proofs/WalkPotential/MarkovFixedTime.lean) is the Markov property of simple random walk at a fixed time
`n`: `P^a(history up to n ∈ F, future ∈ E) = ∫_{history ∈ F} P^{x_n}(E) dP^a`.
`srwLaw_test_bound` turns it into the set-form conditional bound that `TestProduct.lean` takes as hypothesis: if the
conditional probability of the future event `E` is at most `c` from every state `y ∈ Y` reached by the events `S`, then
`P^a(S ∩ {future ∈ E}) ≤ c P^a(S)` for every `S` determined by the history up to `n` with `x_n ∈ Y` on `S`.
It is the one-test step of the product bound at a fixed time. The tests of LEMMA68 start at random times (stopping times
`T_j`), which needs the hitting-time form (`IDLA/StrongMarkov.lean`, `lintegral_hitTime_eq`, for fixed sets only); that
generalization is the open step N3a of the round report.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

open WalkPotential

/-- **Set-form conditional bound at a fixed time.** If `P^y(E) ≤ c` for every state `y ∈ Y`, and `S` is a measurable event
determined by the history up to time `n` with `x_n ∈ Y` on `S`, then `P^a(S ∩ {x_{n+·} ∈ E}) ≤ c P^a(S)`. -/
theorem srwLaw_test_bound (m : ℤ → ℤ → ℕ) (a : ℤ) (n : ℕ) {E : Set (ℕ → ℤ)} (hE : MeasurableSet E)
    {Y : Set ℤ} {c : ℝ≥0∞} (hc : ∀ y ∈ Y, srwLaw m y E ≤ c)
    {S : Set (ℕ → ℤ)} (hSmeas : MeasurableSet S) (hS : ∃ F : Set (Fin (n + 1) → ℤ), S = {x | pathHist n x ∈ F})
    (hSY : ∀ x ∈ S, x n ∈ Y) :
    srwLaw m a (S ∩ {x | pathShift n x ∈ E}) ≤ c * srwLaw m a S := by
  obtain ⟨F, rfl⟩ := hS
  have key := srwLaw_markov m a n F hE
  calc srwLaw m a ({x | pathHist n x ∈ F} ∩ {x | pathShift n x ∈ E})
      = srwLaw m a {x | pathHist n x ∈ F ∧ pathShift n x ∈ E} := rfl
    _ = ∫⁻ x in {x | pathHist n x ∈ F}, srwLaw m (x n) E ∂srwLaw m a := key
    _ ≤ ∫⁻ x in {x | pathHist n x ∈ F}, c ∂srwLaw m a :=
        setLIntegral_mono' hSmeas fun x hx => hc (x n) (hSY x hx)
    _ = c * srwLaw m a {x | pathHist n x ∈ F} := setLIntegral_const _ _

end MatedCRT
