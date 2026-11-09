import MatedCRT.FirstPass.S4S6c.RandomTimeTestBound
import MatedCRT.FirstPass.S4S6c.WindowStop68
import MatedCRT.FirstPass.S4S6c.GreenTest68

/-!
# From the sup form to the uniform form of the printed Lemma 6.7 (q2, task fp-S4S6c; LEMMA68.md "Proof of Lemma 6.7")

LEMMA68 (2) bounds the walker that starts on the layer `V(∂(K+B_{r/2}))`: it stays in `A` until it leaves `U = V \ Θ`
with probability at most `1/2`. The uniform target starts anywhere in `cl Θ` and asks for a visit of `W \ (S ∪ Θ)` before
the exit of `W`. The reduction (LEMMA68.md, "Proof of Lemma 6.7"): the walker from `cl Θ` first hits the layer `L` at a
time `T` before leaving `W` (geometric crossing, the input `hcross` below), and the strong Markov property at `T` applied
to LEMMA68 (2) (the input `hLayer`, with `A = S \ Θ`) bounds the probability that the walk stays in `S ∪ Θ` before leaving
`W`. This file proves the abstract reduction; the geometric crossing and the layer bound are its inputs.

Here `layerHit L` is the first visit time of a path to `L` (`∞` if never), and the strong Markov step is
`MatedCRT.srwLaw_test_bound_random_time` (`RandomTimeTestBound.lean:19`) with `S = univ`.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT
namespace UniformLayer68

open MatedCRT.SuccessiveExitStop MatedCRT.WindowStop68

open Classical in
/-- The first visit time `inf {n ≥ 0 : x n ∈ L}` of a path to the set `L` of cell vertices (`∞` if never). For the
layer `L = V(∂(K+B_{r/2}))` it is the first-passage time `T` of LEMMA68 "Proof of Lemma 6.7". -/
noncomputable def layerHit (L : Set ℤ) (x : ℕ → ℤ) : ℕ∞ :=
  if h : ∃ n, x n ∈ L then (Nat.find h : ℕ∞) else ⊤

/-- The first visit time is `k` exactly when the path is in `L` at time `k` and not before. -/
theorem layerHit_eq_coe_iff {L : Set ℤ} {x : ℕ → ℤ} {k : ℕ} :
    layerHit L x = (k : ℕ∞) ↔ x k ∈ L ∧ ∀ j < k, x j ∉ L := by
  classical
  unfold layerHit
  split_ifs with h
  · rw [ENat.natCast_inj, Nat.find_eq_iff]
  · constructor
    · intro hT
      exact absurd hT.symm (ENat.natCast_ne_top k)
    · rintro ⟨hk, _⟩
      exact absurd ⟨k, hk⟩ h

/-- The set of stopped paths of the first visit to `L` at time `k`, in the finite-dimensional coordinates of `pathHist`. -/
theorem measurableSet_layerHit_stop (L : Set ℤ) (k : ℕ) :
    MeasurableSet {f : Fin (k + 1) → ℤ | f (Fin.last k) ∈ L ∧ ∀ j : Fin (k + 1), (j : ℕ) < k → f j ∉ L} := by
  have h1 : MeasurableSet {f : Fin (k + 1) → ℤ | f (Fin.last k) ∈ L} :=
    measurable_pi_apply (Fin.last k) (Set.to_countable L).measurableSet
  have hj : ∀ j : Fin (k + 1), MeasurableSet {f : Fin (k + 1) → ℤ | (j : ℕ) < k → f j ∉ L} := by
    intro j
    by_cases hjk : (j : ℕ) < k
    · have hset : {f : Fin (k + 1) → ℤ | (j : ℕ) < k → f j ∉ L} = (fun f : Fin (k + 1) → ℤ => f j) ⁻¹' Lᶜ := by
        ext f
        simp [hjk]
      rw [hset]
      exact measurable_pi_apply j (Set.to_countable L).measurableSet.compl
    · have hset : {f : Fin (k + 1) → ℤ | (j : ℕ) < k → f j ∉ L} = univ := by
        ext f
        simp [hjk]
      rw [hset]
      exact MeasurableSet.univ
  have heq : {f : Fin (k + 1) → ℤ | f (Fin.last k) ∈ L ∧ ∀ j : Fin (k + 1), (j : ℕ) < k → f j ∉ L} =
      {f : Fin (k + 1) → ℤ | f (Fin.last k) ∈ L} ∩
        ⋂ j : Fin (k + 1), {f : Fin (k + 1) → ℤ | (j : ℕ) < k → f j ∉ L} := by
    ext f
    simp
  rw [heq]
  exact h1.inter (MeasurableSet.iInter hj)

/-- The first visit time to `L` is `k` iff the stopped path (`pathHist k`) visits `L` at `k` and not before. -/
theorem layerHit_stop_iff (L : Set ℤ) (k : ℕ) (x : ℕ → ℤ) :
    layerHit L x = (k : ℕ∞) ↔
      pathHist k x (Fin.last k) ∈ L ∧ ∀ j : Fin (k + 1), (j : ℕ) < k → pathHist k x j ∉ L := by
  rw [layerHit_eq_coe_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => h2 j hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => h2 ⟨j, by omega⟩ hj⟩

/-- Determinacy of the first visit time: `univ ∩ {layerHit L = k}` is the preimage of the stopped-path set under
`pathHist k` (the hypothesis `hS` of `srwLaw_test_bound_random_time`). -/
theorem layerHit_stop_eq (L : Set ℤ) (k : ℕ) :
    (univ : Set (ℕ → ℤ)) ∩ {x | layerHit L x = (k : ℕ∞)} =
      {x | pathHist k x ∈ {f : Fin (k + 1) → ℤ | f (Fin.last k) ∈ L ∧ ∀ j : Fin (k + 1), (j : ℕ) < k → f j ∉ L}} := by
  ext x
  simp only [univ_inter, mem_ofPred_eq]
  exact layerHit_stop_iff L k x

/-- **The visit bound before the exit of `W`** (LEMMA68.md, "Proof of Lemma 6.7", the strong Markov step). If
(i) the walk from `a` lies in `Good` with probability one, (ii) on `Good` the walk hits the layer `L` before it leaves
`W`, and (iii) the walk from every layer point stays in `S \ Θ` until it leaves `W \ Θ` with probability at most `c`
(LEMMA68 (2) with `A = S \ Θ`, `U = W \ Θ`), then the walk from `a` stays in `S ∪ Θ` before it leaves `W` with
probability at most `c`. -/
theorem srwLaw_stay_le_of_layer (m : ℤ → ℤ → ℕ) (a : ℤ) (W Θ S L : Set ℤ) (Good : Set (ℕ → ℤ)) {c : ℝ≥0∞}
    (hGood : srwLaw m a Goodᶜ = 0)
    (hcross : ∀ x ∈ Good, ∃ k : ℕ, layerHit L x = (k : ℕ∞) ∧ (k : ℕ∞) < vExitTime W x)
    (hLayer : ∀ y ∈ L, srwLaw m y {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime (W \ Θ) x → x n ∈ S \ Θ} ≤ c) :
    srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime W x → x n ∈ S ∪ Θ} ≤ c := by
  -- the test region of the strong Markov step: stay in `S \ Θ` until the exit of `W \ Θ`
  set G : ℤ → Set (ℕ → ℤ) := fun y => stayInRegion (fun _ => W \ Θ) (S \ Θ) y with hGdef
  have hG : ∀ y, MeasurableSet (G y) := fun y => measurableSet_stayInRegion (fun _ => W \ Θ) (S \ Θ) y
  have hS : ∀ k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      (univ : Set (ℕ → ℤ)) ∩ {x | layerHit L x = (k : ℕ∞)} = {x | pathHist k x ∈ F} :=
    fun k => ⟨_, measurableSet_layerHit_stop L k, layerHit_stop_eq L k⟩
  have hSY : ∀ x ∈ (univ : Set (ℕ → ℤ)), ∀ k : ℕ, layerHit L x = (k : ℕ∞) → x k ∈ L :=
    fun x _ k hk => (layerHit_eq_coe_iff.1 hk).1
  have hmain := MatedCRT.srwLaw_test_bound_random_time m a (layerHit L) G hG (S := univ) hS (Y := L) (c := c)
    (fun y hy => hLayer y hy) hSY
  have hone : srwLaw m a ((univ : Set (ℕ → ℤ)) ∩ {x | ∃ k : ℕ, layerHit L x = (k : ℕ∞)}) ≤ 1 :=
    prob_le_one
  have hsub : {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime W x → x n ∈ S ∪ Θ} ⊆
      Goodᶜ ∪ ((univ : Set (ℕ → ℤ)) ∩ {x | ∃ k : ℕ, layerHit L x = (k : ℕ∞) ∧ pathShift k x ∈ G (x k)}) := by
    intro x hx
    by_cases hxG : x ∈ Good
    · obtain ⟨k, hk, hkexit⟩ := hcross x hxG
      refine Or.inr ⟨mem_univ x, k, hk, ?_⟩
      show ∀ n : ℕ, (n : ℕ∞) < vExitTime (W \ Θ) (pathShift k x) → pathShift k x n ∈ S \ Θ
      intro n hn
      -- every time up to `k + n` lies in `W`
      have hall : ∀ m ≤ k + n, x m ∈ W := by
        intro m hm
        by_cases hmk : m ≤ k
        · exact mem_of_lt_vExitTime (lt_of_le_of_lt (by exact_mod_cast hmk) hkexit)
        · have hle : ((m - k : ℕ) : ℕ∞) < vExitTime W (pathShift k x) := by
            have hmn : ((m - k : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast (by omega : m - k ≤ n)
            exact lt_of_le_of_lt hmn (lt_of_lt_of_le hn (GreenTest68.vExitTime_le_of_subset Set.sdiff_subset (pathShift k x)))
          have hmem := mem_of_lt_vExitTime hle
          have hpe : pathShift k x (m - k) = x m := by
            show x (k + (m - k)) = x m
            congr 1
            omega
          rw [hpe] at hmem
          exact hmem
      have hexit : ((k + n : ℕ) : ℕ∞) < vExitTime W x := lt_vExitTime_of_forall hall
      have hin : x (k + n) ∈ S ∪ Θ := hx (k + n) hexit
      have hU : pathShift k x n ∈ W \ Θ := mem_of_lt_vExitTime hn
      have hU' : x (k + n) ∉ Θ := hU.2
      have hpe : pathShift k x n = x (k + n) := rfl
      rw [hpe]
      exact ⟨hin.resolve_right hU', hU'⟩
    · exact Or.inl hxG
  calc srwLaw m a {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime W x → x n ∈ S ∪ Θ}
      ≤ srwLaw m a (Goodᶜ ∪ ((univ : Set (ℕ → ℤ)) ∩ {x | ∃ k : ℕ, layerHit L x = (k : ℕ∞) ∧ pathShift k x ∈ G (x k)})) :=
        measure_mono hsub
    _ ≤ srwLaw m a Goodᶜ + srwLaw m a ((univ : Set (ℕ → ℤ)) ∩ {x | ∃ k : ℕ, layerHit L x = (k : ℕ∞) ∧ pathShift k x ∈ G (x k)}) :=
        measure_union_le _ _
    _ = srwLaw m a ((univ : Set (ℕ → ℤ)) ∩ {x | ∃ k : ℕ, layerHit L x = (k : ℕ∞) ∧ pathShift k x ∈ G (x k)}) := by
        rw [hGood, zero_add]
    _ ≤ c * srwLaw m a ((univ : Set (ℕ → ℤ)) ∩ {x | ∃ k : ℕ, layerHit L x = (k : ℕ∞)}) := hmain
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hone (by simp)
    _ = c := mul_one c

/-- **The uniform visit bound** (LEMMA68.md, "Proof of Lemma 6.7"): under the same hypotheses, the walk from `a`
visits `W \ (S ∪ Θ)` before it leaves `W` with probability at least `1 - c`. With `c = 1/2` this is the uniform
`s₂ = 1/2` of the target `UniformConstantOrderLowerBoundStmt` (`q4`'s `MatedCRT/FirstPass/S6d.lean:90`). -/
theorem srwLaw_visit_ge_of_layer (m : ℤ → ℤ → ℕ) (a : ℤ) (W Θ S L : Set ℤ) (Good : Set (ℕ → ℤ)) {c : ℝ≥0∞}
    (hGood : srwLaw m a Goodᶜ = 0)
    (hcross : ∀ x ∈ Good, ∃ k : ℕ, layerHit L x = (k : ℕ∞) ∧ (k : ℕ∞) < vExitTime W x)
    (hLayer : ∀ y ∈ L, srwLaw m y {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime (W \ Θ) x → x n ∈ S \ Θ} ≤ c) :
    1 - c ≤ srwLaw m a {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime W x ∧ x n ∈ W \ (S ∪ Θ)} := by
  have hstay := srwLaw_stay_le_of_layer m a W Θ S L Good hGood hcross hLayer
  have hE : {x : ℕ → ℤ | ∃ n : ℕ, (n : ℕ∞) < vExitTime W x ∧ x n ∈ W \ (S ∪ Θ)} =
      {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime W x → x n ∈ S ∪ Θ}ᶜ := by
    ext x
    constructor
    · rintro ⟨n, hn, hmem⟩ hB
      exact hmem.2 (hB n hn)
    · intro hB
      by_contra hcon
      apply hB
      intro n hn
      by_contra hn'
      exact hcon ⟨n, hn, mem_of_lt_vExitTime hn, hn'⟩
  have hBmeas : MeasurableSet {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime W x → x n ∈ S ∪ Θ} :=
    measurableSet_stayInRegion (fun _ => W) (S ∪ Θ) a
  rw [hE, prob_compl_eq_one_sub hBmeas]
  exact tsub_le_tsub_left hstay 1

#print axioms MatedCRT.UniformLayer68.srwLaw_stay_le_of_layer
#print axioms MatedCRT.UniformLayer68.srwLaw_visit_ge_of_layer

end UniformLayer68
end MatedCRT
