import MatedCRT.FirstPass.S4S6c.StrongMarkovState
import MatedCRT.FirstPass.S4S6c.TraceFrom68
import MatedCRT.FirstPass.S6j.PerState

/-!
# Geometric decay over successive stages for the simple random walk

A *stage* is a segment of the walk between two successive hitting times of the sets `S n`, `S (n+1)`:
the walk is at `y ∈ S n`, runs until it hits `S (n+1)` for the first time, and the stage *succeeds* when
the history up to that hitting time lies in a prescribed set `F n y`.  The stage events involve the history
up to the hitting time only, so the strong Markov property at the hitting time gives: if each stage fails with
probability at most `q` from every starting point of `S n`, then the walk started in `S n` fails at the next
`k` consecutive stages with probability at most `q ^ k`, where stage `i + 1` starts at the hitting point of
stage `i`.  No nesting of the sets `S n` is used.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The success event of one stage: the first hit of `S'` occurs at a time `k` such that the history up to
time `k` lies in `F k`. -/
def stageEvent (S' : Set ℤ) (F : ∀ k : ℕ, Set (Fin (k + 1) → ℤ)) : Set (ℕ → ℤ) :=
  {ξ | ∃ k : ℕ, vHitTime S' ξ = (k : ℕ∞) ∧ pathHist k ξ ∈ F k}

/-- The event that the walk started at `y` fails at the next `k` stages, the stage `n` being the one that runs
from `S n` to `S (n+1)` with success sets `F n y`; stage `n + 1` is run from the position at the hitting time. -/
noncomputable def stageFail (S : ℕ → Set ℤ) (F : ℕ → ℤ → ∀ k : ℕ, Set (Fin (k + 1) → ℤ)) :
    ℕ → ℕ → ℤ → Set (ℕ → ℤ)
  | 0, _, _ => univ
  | k + 1, n, y =>
      (stageEvent (S (n + 1)) (F n y))ᶜ ∩
        {ξ | ∃ j : ℕ, vHitTime (S (n + 1)) ξ = (j : ℕ∞) ∧
          WalkPotential.pathShift j ξ ∈ stageFail S F k (n + 1) (ξ j)}

theorem measurableSet_stageEvent (S' : Set ℤ) (F : ∀ k : ℕ, Set (Fin (k + 1) → ℤ)) :
    MeasurableSet (stageEvent S' F) := by
  have h : stageEvent S' F =
      ⋃ k : ℕ, {ξ | vHitTime S' ξ = (k : ℕ∞)} ∩ {ξ | pathHist k ξ ∈ F k} := by
    ext ξ
    simp only [stageEvent, mem_iUnion, mem_inter_iff, Set.mem_ofPred_eq]
  rw [h]
  refine MeasurableSet.iUnion fun k => ?_
  exact (S6j.histSigma_le k _ (S6j.hit_isWalkRandomTime S' k)).inter
    ((measurable_pathHist k) (Set.to_countable _).measurableSet)

theorem measurableSet_stageFail (S : ℕ → Set ℤ) (F : ℕ → ℤ → ∀ k : ℕ, Set (Fin (k + 1) → ℤ)) :
    ∀ (k n : ℕ) (y : ℤ), MeasurableSet (stageFail S F k n y) := by
  intro k
  induction k with
  | zero => intro n y; exact MeasurableSet.univ
  | succ k ih =>
    intro n y
    exact (measurableSet_stageEvent _ _).compl.inter
      (S6j.measurableSet_walkTestEvent (S6j.hit_isWalkRandomTime _) (fun z => ih (n + 1) z))

/-- **Stage decay.**  If every stage `i < N` fails with probability at most `q` from every point of `S i`,
then from a point of `S n` the walk fails at `k` consecutive stages (`n + k ≤ N`) with probability at most
`q ^ k`. -/
theorem srwLaw_stageFail_le (m : ℤ → ℤ → ℕ) (S : ℕ → Set ℤ)
    (F : ℕ → ℤ → ∀ k : ℕ, Set (Fin (k + 1) → ℤ)) (q : ℝ≥0∞) (N : ℕ)
    (hq : ∀ i < N, ∀ y ∈ S i, srwLaw m y (stageEvent (S (i + 1)) (F i y))ᶜ ≤ q) :
    ∀ (k n : ℕ), n + k ≤ N → ∀ y ∈ S n, srwLaw m y (stageFail S F k n y) ≤ q ^ k := by
  intro k
  induction k with
  | zero =>
    intro n _ y _
    simp only [stageFail, pow_zero]
    exact prob_le_one
  | succ k ih =>
    intro n hn y hy
    have hnN : n < N := by omega
    set τ : (ℕ → ℤ) → ℕ∞ := vHitTime (S (n + 1)) with hτ
    set Ev : Set (ℕ → ℤ) := stageEvent (S (n + 1)) (F n y) with hEv
    set G : ℤ → Set (ℕ → ℤ) := fun z => stageFail S F k (n + 1) z with hGdef
    have hG : ∀ z, MeasurableSet (G z) := fun z => measurableSet_stageFail S F k (n + 1) z
    have hS : ∀ j : ℕ, ∃ F' : Set (Fin (j + 1) → ℤ), MeasurableSet F' ∧
        Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)} = {ξ | pathHist j ξ ∈ F'} := by
      intro j
      refine ⟨{f | f (Fin.last j) ∈ S (n + 1) ∧ (∀ i : Fin (j + 1), i.val < j → f i ∉ S (n + 1)) ∧
        f ∉ F n y j}, (Set.to_countable _).measurableSet, ?_⟩
      ext ξ
      simp only [mem_inter_iff, mem_compl_iff, Set.mem_ofPred_eq, hEv, stageEvent, not_exists,
        not_and, pathHist, hτ]
      constructor
      · rintro ⟨hnev, hj⟩
        have h1 := (TraceFrom68.vHitTime_eq_iff (S (n + 1)) j ξ).1 hj
        exact ⟨h1.1, fun i hi => h1.2 i.val hi, hnev j hj⟩
      · rintro ⟨h1, h2, h3⟩
        have hj : vHitTime (S (n + 1)) ξ = (j : ℕ∞) :=
          (TraceFrom68.vHitTime_eq_iff (S (n + 1)) j ξ).2 ⟨h1, fun i hi => h2 ⟨i, Nat.lt_succ_of_lt hi⟩ hi⟩
        refine ⟨fun k hk hmem => ?_, hj⟩
        have hkj : k = j := by
          have := hk.symm.trans hj
          exact_mod_cast this
        subst hkj
        exact h3 hmem
    have hmeas : ∀ j : ℕ, MeasurableSet (Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}) := by
      intro j
      obtain ⟨F', hF', heq⟩ := hS j
      rw [heq]
      exact (measurable_pathHist j) hF'
    have hdisj : Pairwise (Disjoint on fun j : ℕ => Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}) := by
      intro j j' hjj'
      refine Set.disjoint_left.2 fun ξ h1 h2 => hjj' ?_
      have h3 : (j : ℕ∞) = (j' : ℕ∞) := h1.2.symm.trans h2.2
      exact_mod_cast h3
    have hSM := srwLaw_strong_markov_state m y τ G hG hS
    have hdef : stageFail S F (k + 1) n y =
        Evᶜ ∩ {ξ | ∃ j : ℕ, τ ξ = (j : ℕ∞) ∧ WalkPotential.pathShift j ξ ∈ G (ξ j)} := rfl
    rw [hdef, hSM]
    have hbound : ∀ j : ℕ, ∫⁻ ξ in Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}, srwLaw m (ξ j) (G (ξ j)) ∂srwLaw m y ≤
        q ^ k * srwLaw m y (Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}) := by
      intro j
      calc ∫⁻ ξ in Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}, srwLaw m (ξ j) (G (ξ j)) ∂srwLaw m y
          ≤ ∫⁻ ξ in Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}, q ^ k ∂srwLaw m y := by
            refine setLIntegral_mono' (hmeas j) fun ξ hξ => ?_
            have hmem : ξ j ∈ S (n + 1) := ((TraceFrom68.vHitTime_eq_iff (S (n + 1)) j ξ).1 hξ.2).1
            exact ih (n + 1) (by omega) (ξ j) hmem
        _ = q ^ k * srwLaw m y (Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}) := by
            rw [setLIntegral_const]
    calc ∑' j : ℕ, ∫⁻ ξ in Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}, srwLaw m (ξ j) (G (ξ j)) ∂srwLaw m y
        ≤ ∑' j : ℕ, q ^ k * srwLaw m y (Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}) := ENNReal.tsum_le_tsum hbound
      _ = q ^ k * ∑' j : ℕ, srwLaw m y (Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}) := ENNReal.tsum_mul_left
      _ = q ^ k * srwLaw m y (⋃ j : ℕ, Evᶜ ∩ {ξ | τ ξ = (j : ℕ∞)}) := by
          rw [measure_iUnion hdisj hmeas]
      _ ≤ q ^ k * srwLaw m y Evᶜ := by
          gcongr
          exact Set.iUnion_subset fun j => Set.inter_subset_left
      _ ≤ q ^ k * q := by
          gcongr
          exact hq n hnN y hy
      _ = q ^ (k + 1) := (pow_succ q k).symm

end MatedCRT.FirstPass.Derived
