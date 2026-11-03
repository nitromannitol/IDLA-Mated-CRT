import MatedCRT.Defs.RandomWalk

/-!
# IDLA on a fixed multigraph: exit times and monotonicity of the aggregate

* `mem_of_lt_vExitTime`, `apply_vExitTime_not_mem`: a path is in `A` strictly before its exit time from `A`, and
  outside `A` at a finite exit time; `apply_vHitTime_eq`: at a finite hitting time of `{a}` the path is at `a`.
* `idlaStep_fst_subset`, `idlaRun_ofFn_succ`, `idlaAggregate_ofFn_mono`: releasing walkers only enlarges the
  aggregate; in particular `idlaCluster xs` and `stoppedIDLACluster Θ' xs` are monotone in the number of walkers.
-/

namespace MatedCRT

open Set

open Classical in
/-- A path is in `A` at every time `k < τ_A`. -/
theorem mem_of_lt_vExitTime {A : Set ℤ} {x : ℕ → ℤ} {k : ℕ} (h : (k : ℕ∞) < vExitTime A x) : x k ∈ A := by
  by_contra hk
  have hex : ∃ n, x n ∉ A := ⟨k, hk⟩
  unfold vExitTime at h
  rw [dite_eq_left hex] at h
  exact absurd h (not_lt.2 (Nat.cast_le.2 (Nat.find_min' hex hk)))

open Classical in
/-- At a finite exit time `τ_A = k` the path is outside `A`. -/
theorem apply_vExitTime_not_mem {A : Set ℤ} {x : ℕ → ℤ} {k : ℕ} (h : vExitTime A x = k) : x k ∉ A := by
  unfold vExitTime at h
  split_ifs at h with hex
  · have hk : Nat.find hex = k := by exact_mod_cast h
    rw [← hk]
    exact Nat.find_spec hex
  · simp at h

/-- At a finite hitting time of `{a}` the path is at `a`. -/
theorem apply_vHitTime_eq {a : ℤ} {x : ℕ → ℤ} {k : ℕ} (h : vHitTime {a} x = k) : x k = a := by
  have := apply_vExitTime_not_mem (A := {a}ᶜ) h
  simpa using this

/-- Releasing one walker only enlarges the aggregate. -/
theorem idlaStep_fst_subset (Θ' : Set ℤ) (s : Set ℤ × List ℤ) (x : ℕ → ℤ) : s.1 ⊆ (idlaStep Θ' s x).1 := by
  unfold idlaStep
  cases firstExitSite s.1 x with
  | none => exact subset_rfl
  | some b =>
    dsimp only
    split_ifs
    · exact subset_union_left
    · exact subset_rfl

/-- The state after `n + 1` walkers is one step from the state after `n` walkers. -/
theorem idlaRun_ofFn_succ (Θ Θ' : Set ℤ) (xs : ℕ → ℕ → ℤ) (n : ℕ) :
    idlaRun Θ Θ' (List.ofFn fun i : Fin (n + 1) => xs i) =
      idlaStep Θ' (idlaRun Θ Θ' (List.ofFn fun i : Fin n => xs i)) (xs n) := by
  unfold idlaRun
  rw [List.ofFn_succ_last, List.foldl_append]
  simp

/-- The aggregate after the first `n` walkers is monotone in `n`. -/
theorem idlaAggregate_ofFn_mono (Θ Θ' : Set ℤ) (xs : ℕ → ℕ → ℤ) :
    Monotone fun n => idlaAggregate Θ Θ' (List.ofFn fun i : Fin n => xs i) := by
  refine monotone_nat_of_le_succ fun n => ?_
  show idlaAggregate Θ Θ' (List.ofFn fun i : Fin n => xs i) ⊆
    idlaAggregate Θ Θ' (List.ofFn fun i : Fin (n + 1) => xs i)
  unfold idlaAggregate
  rw [idlaRun_ofFn_succ]
  exact idlaStep_fst_subset _ _ _

theorem idlaCluster_mono (xs : ℕ → ℕ → ℤ) {i n : ℕ} (h : i ≤ n) : idlaCluster xs i ⊆ idlaCluster xs n :=
  idlaAggregate_ofFn_mono ∅ univ xs h

theorem stoppedIDLACluster_mono (Θ' : Set ℤ) (xs : ℕ → ℕ → ℤ) {i n : ℕ} (h : i ≤ n) :
    stoppedIDLACluster Θ' xs i ⊆ stoppedIDLACluster Θ' xs n :=
  idlaAggregate_ofFn_mono ∅ Θ' xs h

end MatedCRT
