import MatedCRT.Proofs.WalkPotential.MarkovFixedTime

/-!
# State-dependent Markov property at a fixed time

The tests are events about the future of the walk whose law depends on the current state `x_n`: from the state
`y`, the test event is `G y`. `srwLaw_markov_state` extends `srwLaw_markov` (fixed future set) to state-dependent future
sets: `P^a(history ∈ F, future ∈ G(x_n)) = ∫_{history ∈ F} P^{x_n}(G(x_n)) dP^a`. The proof decomposes by the state
`y = x_n` (a countable disjoint union over `y ∈ ℤ`) and applies `srwLaw_markov` to each fibre. It is the input that the
random-time (stopping-time) version of the test product needs; that version is an open step.
-/

open MeasureTheory Set
open scoped ENNReal
open Function

namespace MatedCRT

open WalkPotential

/-- The history fibre `{f ∈ F : f (last) = y}`: histories in `F` whose last state is `y`. -/
def stateFiber {n : ℕ} (F : Set (Fin (n + 1) → ℤ)) (y : ℤ) : Set (Fin (n + 1) → ℤ) :=
  {f | f ∈ F ∧ f (Fin.last n) = y}

/-- **State-dependent Markov property at a fixed time.** -/
theorem srwLaw_markov_state (m : ℤ → ℤ → ℕ) (a : ℤ) (n : ℕ) (G : ℤ → Set (ℕ → ℤ))
    (hG : ∀ y, MeasurableSet (G y)) {F : Set (Fin (n + 1) → ℤ)} (hF : MeasurableSet F) :
    srwLaw m a {x | pathHist n x ∈ F ∧ pathShift n x ∈ G (x n)} =
      ∫⁻ x in {x | pathHist n x ∈ F}, srwLaw m (x n) (G (x n)) ∂srwLaw m a := by
  -- measurability of the fibres of the history
  have hlast : ∀ y : ℤ, MeasurableSet {f : Fin (n + 1) → ℤ | f (Fin.last n) = y} := fun y => by
    have h : MeasurableSet ((fun f : Fin (n + 1) → ℤ => f (Fin.last n)) ⁻¹' {y}) :=
      (measurable_pi_apply (Fin.last n)) (measurableSet_singleton y)
    exact h
  have hfib : ∀ y : ℤ, MeasurableSet (stateFiber F y) := fun y => hF.inter (hlast y)
  -- disjointness of the fibres of the history
  have hdisjF : Pairwise (Disjoint on fun y : ℤ => {x : ℕ → ℤ | pathHist n x ∈ stateFiber F y}) := by
    intro y y' hyy'
    refine Set.disjoint_left.2 fun x hx hx' => hyy' ?_
    have h1 : x n = y := hx.2
    have h2 : x n = y' := hx'.2
    exact h1.symm.trans h2
  -- the history event decomposes over the state at time `n`
  have hR : {x : ℕ → ℤ | pathHist n x ∈ F} = ⋃ y : ℤ, {x | pathHist n x ∈ stateFiber F y} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      exact ⟨x n, h, rfl⟩
    · rintro ⟨y, h, _⟩
      exact h
  -- the joint event decomposes over the state at time `n`
  have hL : {x : ℕ → ℤ | pathHist n x ∈ F ∧ pathShift n x ∈ G (x n)} =
      ⋃ y : ℤ, {x | pathHist n x ∈ stateFiber F y ∧ pathShift n x ∈ G y} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨x n, ⟨h1, rfl⟩, h2⟩
    · rintro ⟨y, ⟨h1, hy⟩, h2⟩
      have hxy : x n = y := hy
      exact ⟨h1, by rw [hxy]; exact h2⟩
  -- disjointness and measurability of the joint pieces
  have hdisjL : Pairwise (Disjoint on fun y : ℤ =>
      {x : ℕ → ℤ | pathHist n x ∈ stateFiber F y ∧ pathShift n x ∈ G y}) := by
    intro y y' hyy'
    refine Set.disjoint_left.2 fun x hx hx' => hyy' ?_
    have h1 : x n = y := hx.1.2
    have h2 : x n = y' := hx'.1.2
    exact h1.symm.trans h2
  have hmeasL : ∀ y : ℤ, MeasurableSet
      {x : ℕ → ℤ | pathHist n x ∈ stateFiber F y ∧ pathShift n x ∈ G y} := fun y =>
    (measurable_pathHist n (hfib y)).inter (walk_measurable_pathShift n (hG y))
  have hmeasFib : ∀ y : ℤ, MeasurableSet {x : ℕ → ℤ | pathHist n x ∈ stateFiber F y} :=
    fun y => measurable_pathHist n (hfib y)
  -- the joint probability is the sum over the states, each term by `srwLaw_markov`
  rw [hL, measure_iUnion hdisjL hmeasL]
  have hpiece : ∀ y : ℤ, srwLaw m a {x | pathHist n x ∈ stateFiber F y ∧ pathShift n x ∈ G y} =
      ∫⁻ x in {x | pathHist n x ∈ stateFiber F y}, srwLaw m (x n) (G y) ∂srwLaw m a :=
    fun y => srwLaw_markov m a n (stateFiber F y) (hG y)
  simp only [hpiece]
  -- the right-hand side decomposes the same way
  rw [hR, lintegral_iUnion hmeasFib hdisjF]
  refine tsum_congr fun y => ?_
  refine setLIntegral_congr_fun (hmeasFib y) fun x hx => ?_
  have hxy : x n = y := hx.2
  rw [hxy]

end MatedCRT
