import MatedCRT.FirstPass.S4S6c.StateMarkov

/-!
# Strong Markov property at a random time with a state-dependent future event

Let `τ` be a random time (values in `ℕ∞`) for the simple random walk, with the stopping property in the form that each
event `S ∩ {τ = k}` is determined by the history up to time `k` (this is what `S ∈ F_τ` means for the events used by the
tests). Then the probability that `S` occurs and the state-dependent future event `G(x_τ)` occurs
after the finite random time `τ` is the sum over `k` of the fixed-time integrals:
`P^a(S ∩ {τ < ∞, shift_τ ∈ G(x_τ)}) = ∑_k ∫_{S ∩ {τ = k}} P^{x_k}(G(x_k)) dP^a`.
The proof decomposes `S ∩ {τ < ∞}` over the disjoint events `{τ = k}` and applies `srwLaw_markov_state` at each fixed time `k`.
This is the one-step strong Markov property needed to iterate the tests at their random start times (N3a).
-/

open MeasureTheory Set
open scoped ENNReal
open Function

namespace MatedCRT

open WalkPotential

/-- The future event at a fixed time, with state-dependent set, is measurable. -/
theorem measurableSet_future_at_state (k : ℕ) {G : ℤ → Set (ℕ → ℤ)} (hG : ∀ y, MeasurableSet (G y)) :
    MeasurableSet {x : ℕ → ℤ | pathShift k x ∈ G (x k)} := by
  have h : {x : ℕ → ℤ | pathShift k x ∈ G (x k)} =
      ⋃ y : ℤ, {x : ℕ → ℤ | x k = y} ∩ {x | pathShift k x ∈ G y} := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      exact ⟨x k, rfl, hx⟩
    · rintro ⟨y, hy, hx⟩
      have hxy : x k = y := hy
      rw [hxy]
      exact hx
  rw [h]
  refine MeasurableSet.iUnion fun y => ?_
  have hstate : MeasurableSet {x : ℕ → ℤ | x k = y} := by
    have h1 : MeasurableSet ((fun x : ℕ → ℤ => x k) ⁻¹' {y}) :=
      (measurable_pi_apply k) (measurableSet_singleton y)
    exact h1
  exact hstate.inter (walk_measurable_pathShift k (hG y))

/-- **Strong Markov property at a random time with a state-dependent future event**. -/
theorem srwLaw_strong_markov_state (m : ℤ → ℤ → ℕ) (a : ℤ) (τ : (ℕ → ℤ) → ℕ∞)
    (G : ℤ → Set (ℕ → ℤ)) (hG : ∀ y, MeasurableSet (G y)) {S : Set (ℕ → ℤ)}
    (hS : ∀ k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      S ∩ {x | τ x = k} = {x | pathHist k x ∈ F}) :
    srwLaw m a (S ∩ {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G (x k)}) =
      ∑' k : ℕ, ∫⁻ x in (S ∩ {x | τ x = k}), srwLaw m (x k) (G (x k)) ∂srwLaw m a := by
  -- decompose over the value of the random time
  have hL : S ∩ {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G (x k)} =
      ⋃ k : ℕ, (S ∩ {x | τ x = k}) ∩ {x | pathShift k x ∈ G (x k)} := by
    ext x
    simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hxS, k, hk, hfut⟩
      exact ⟨k, ⟨hxS, hk⟩, hfut⟩
    · rintro ⟨k, ⟨hxS, hk⟩, hfut⟩
      exact ⟨hxS, k, hk, hfut⟩
  have hdisj : Pairwise (Disjoint on fun k : ℕ =>
      (S ∩ {x | τ x = k}) ∩ {x | pathShift k x ∈ G (x k)}) := by
    intro k k' hkk'
    refine Set.disjoint_left.2 fun x hx hx' => hkk' ?_
    have h1 : τ x = k := hx.1.2
    have h2 : τ x = k' := hx'.1.2
    have h3 : (k : ℕ∞) = (k' : ℕ∞) := h1.symm.trans h2
    exact_mod_cast h3
  have hmeas : ∀ k : ℕ, MeasurableSet ((S ∩ {x | τ x = k}) ∩ {x | pathShift k x ∈ G (x k)}) := by
    intro k
    obtain ⟨F, hF, hSF⟩ := hS k
    have hpre : MeasurableSet (S ∩ {x | τ x = k}) := by
      rw [hSF]
      exact measurable_pathHist k hF
    exact hpre.inter (measurableSet_future_at_state k hG)
  rw [hL, measure_iUnion hdisj hmeas]
  refine tsum_congr fun k => ?_
  obtain ⟨F, hF, hSF⟩ := hS k
  have hset : (S ∩ {x | τ x = k}) ∩ {x | pathShift k x ∈ G (x k)} =
      {x | pathHist k x ∈ F ∧ pathShift k x ∈ G (x k)} := by
    rw [hSF]
    rfl
  rw [hset, srwLaw_markov_state m a k G hG hF, hSF]

end MatedCRT
