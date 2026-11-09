import MatedCRT.FirstPass.S4S6c.StrongMarkovState

/-!
# One-test bound at a random time (q2, task fp-S4S6c; LEMMA68 N3a, set form)

The random-time version of `TestBridge.lean`. If, from every state `y ∈ Y`, the test event `G y` has probability at most `c`,
and `S` is an event on which the state at the random time `τ` lies in `Y`, then the probability that `S` occurs, `τ < ∞`
and the test passes after `τ`, is at most `c` times the probability of `S ∩ {τ < ∞}`. This is the hypothesis shape that the
product bound `TestProduct.lean` needs for the successive tests of LEMMA68 (eqs (23)-(27)), with the filtration `F_τ`
replaced by the events `S` of the stopping property.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT

open WalkPotential

/-- **One-test bound at a random time.** -/
theorem srwLaw_test_bound_random_time (m : ℤ → ℤ → ℕ) (a : ℤ) (τ : (ℕ → ℤ) → ℕ∞)
    (G : ℤ → Set (ℕ → ℤ)) (hG : ∀ y, MeasurableSet (G y)) {S : Set (ℕ → ℤ)}
    (hS : ∀ k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      S ∩ {x | τ x = k} = {x | pathHist k x ∈ F})
    {Y : Set ℤ} {c : ℝ≥0∞} (hc : ∀ y ∈ Y, srwLaw m y (G y) ≤ c)
    (hSY : ∀ x ∈ S, ∀ k : ℕ, τ x = k → x k ∈ Y) :
    srwLaw m a (S ∩ {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G (x k)}) ≤
      c * srwLaw m a (S ∩ {x | ∃ k : ℕ, τ x = k}) := by
  -- measurability of the pieces `S ∩ {τ = k}`
  have hmeasS : ∀ k : ℕ, MeasurableSet (S ∩ {x | τ x = k}) := by
    intro k
    obtain ⟨F, hF, hSF⟩ := hS k
    rw [hSF]
    exact measurable_pathHist k hF
  -- the pieces are pairwise disjoint
  have hdisjS : Pairwise (Disjoint on fun k : ℕ => S ∩ {x | τ x = k}) := by
    intro k k' hkk'
    refine Set.disjoint_left.2 fun x hx hx' => hkk' ?_
    have h1 : τ x = k := hx.2
    have h2 : τ x = k' := hx'.2
    have h3 : (k : ℕ∞) = (k' : ℕ∞) := h1.symm.trans h2
    exact_mod_cast h3
  -- the event `S ∩ {τ < ∞}` is the union of the pieces
  have hU : S ∩ {x | ∃ k : ℕ, τ x = k} = ⋃ k : ℕ, S ∩ {x | τ x = k} := by
    ext x
    simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hxS, k, hk⟩
      exact ⟨k, hxS, hk⟩
    · rintro ⟨k, hxS, hk⟩
      exact ⟨hxS, k, hk⟩
  rw [srwLaw_strong_markov_state m a τ G hG hS]
  have hsum : ∑' k : ℕ, ∫⁻ x in (S ∩ {x | τ x = k}), srwLaw m (x k) (G (x k)) ∂srwLaw m a ≤
      ∑' k : ℕ, c * srwLaw m a (S ∩ {x | τ x = k}) := by
    refine ENNReal.tsum_le_tsum fun k => ?_
    calc ∫⁻ x in (S ∩ {x | τ x = k}), srwLaw m (x k) (G (x k)) ∂srwLaw m a
        ≤ ∫⁻ x in (S ∩ {x | τ x = k}), c ∂srwLaw m a :=
          setLIntegral_mono' (hmeasS k) fun x hx => hc (x k) (hSY x hx.1 k hx.2)
      _ = c * srwLaw m a (S ∩ {x | τ x = k}) := by
          rw [setLIntegral_const, mul_comm]
  have hfinal : ∑' k : ℕ, c * srwLaw m a (S ∩ {x | τ x = k}) =
      c * srwLaw m a (S ∩ {x | ∃ k : ℕ, τ x = k}) := by
    rw [ENNReal.tsum_mul_left, hU, measure_iUnion hdisjS hmeasS]
  exact hsum.trans hfinal.le

end MatedCRT
