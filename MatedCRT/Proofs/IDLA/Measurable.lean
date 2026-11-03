import MatedCRT.Proofs.IDLA.Basic

/-!
# Measurability of exit times and hitting events on path space

* `natCast_lt_vExitTime_iff`, `vExitTime_eq_top_iff`, `vExitTime_eq_natCast_iff`: descriptions of the exit time
  through the coordinates of the path;
* `measurable_vExitTime`, `measurable_vHitTime`: exit and hitting times are measurable maps `(ℕ → ℤ) → ℕ∞`;
* `measurableSet_hitBeforeExit`: the event `{τ_a < T_O}`.
-/

namespace MatedCRT

open MeasureTheory Set

/-- `{x | x j ∈ B}` is a measurable set of paths. -/
theorem measurableSet_coord (j : ℕ) (B : Set ℤ) : MeasurableSet {x : ℕ → ℤ | x j ∈ B} :=
  measurable_pi_apply j MeasurableSet.of_discrete

/-- `k < τ_A` iff the path stays in `A` up to time `k`. -/
theorem natCast_lt_vExitTime_iff {A : Set ℤ} {x : ℕ → ℤ} {k : ℕ} :
    (k : ℕ∞) < vExitTime A x ↔ ∀ j ≤ k, x j ∈ A := by
  constructor
  · intro h j hj
    exact mem_of_lt_vExitTime (lt_of_le_of_lt (Nat.cast_le.2 hj) h)
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have hne : vExitTime A x ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
    have hj : vExitTime A x = ((vExitTime A x).toNat : ℕ∞) := (ENat.natCast_toNat hne).symm
    have hjk : (vExitTime A x).toNat ≤ k := by
      have h' := hle
      rw [hj] at h'
      exact_mod_cast h'
    exact apply_vExitTime_not_mem hj (h _ hjk)

/-- `τ_A = ∞` iff the path never leaves `A`. -/
theorem vExitTime_eq_top_iff {A : Set ℤ} {x : ℕ → ℤ} : vExitTime A x = ⊤ ↔ ∀ n, x n ∈ A := by
  constructor
  · intro h n
    exact mem_of_lt_vExitTime (by rw [h]; exact ENat.natCast_lt_top n)
  · intro h
    by_contra hne
    have hj : vExitTime A x = ((vExitTime A x).toNat : ℕ∞) := (ENat.natCast_toNat hne).symm
    exact apply_vExitTime_not_mem hj (h _)

/-- `τ_A = k` iff the path is in `A` before time `k` and not at time `k`. -/
theorem vExitTime_eq_natCast_iff {A : Set ℤ} {x : ℕ → ℤ} {k : ℕ} :
    vExitTime A x = k ↔ ¬ (k : ℕ∞) < vExitTime A x ∧ ∀ j < k, x j ∈ A := by
  constructor
  · intro h
    refine ⟨by rw [h]; exact lt_irrefl _, fun j hj => mem_of_lt_vExitTime ?_⟩
    rw [h]
    exact_mod_cast hj
  · rintro ⟨h1, h2⟩
    rw [not_lt] at h1
    have hne : vExitTime A x ≠ ⊤ := ne_top_of_le_ne_top (by simp) h1
    have hj : vExitTime A x = ((vExitTime A x).toNat : ℕ∞) := (ENat.natCast_toNat hne).symm
    have hjk : (vExitTime A x).toNat ≤ k := by
      have h' := h1
      rw [hj] at h'
      exact_mod_cast h'
    rcases hjk.lt_or_eq with hlt | heq
    · exact absurd (h2 _ hlt) (apply_vExitTime_not_mem hj)
    · rw [hj, heq]

theorem measurableSet_natCast_lt_vExitTime (A : Set ℤ) (k : ℕ) :
    MeasurableSet {x : ℕ → ℤ | (k : ℕ∞) < vExitTime A x} := by
  have h : {x : ℕ → ℤ | (k : ℕ∞) < vExitTime A x} = ⋂ j : ℕ, ⋂ (_ : j ≤ k), {x | x j ∈ A} := by
    ext x
    simp only [mem_iInter]
    exact natCast_lt_vExitTime_iff
  rw [h]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => measurableSet_coord j A

/-- The exit time from `A` is a measurable function of the path. -/
theorem measurable_vExitTime (A : Set ℤ) : Measurable (vExitTime A) := by
  refine measurable_to_countable' fun y => ?_
  induction y using ENat.recTopCoe with
  | top =>
    have h : vExitTime A ⁻¹' {⊤} = ⋂ n : ℕ, {x | x n ∈ A} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_iInter]
      exact vExitTime_eq_top_iff
    rw [h]
    exact MeasurableSet.iInter fun n => measurableSet_coord n A
  | coe k =>
    have h : vExitTime A ⁻¹' {(k : ℕ∞)} =
        {x | (k : ℕ∞) < vExitTime A x}ᶜ ∩ ⋂ j : ℕ, ⋂ (_ : j < k), {x | x j ∈ A} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_compl_iff, mem_iInter]
      exact vExitTime_eq_natCast_iff
    rw [h]
    exact (measurableSet_natCast_lt_vExitTime A k).compl.inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => measurableSet_coord j A)

/-- The hitting time of `B` is a measurable function of the path. -/
theorem measurable_vHitTime (B : Set ℤ) : Measurable (vHitTime B) :=
  measurable_vExitTime Bᶜ

/-- The event `{τ_a < T_O}` that the path hits `a` before exiting `O` is measurable. -/
theorem measurableSet_hitBeforeExit (O : Set ℤ) (a : ℤ) :
    MeasurableSet {x : ℕ → ℤ | vHitTime {a} x < vExitTime O x} :=
  ((measurable_vHitTime {a}).prodMk (measurable_vExitTime O))
    (MeasurableSet.of_discrete (s := {p : ℕ∞ × ℕ∞ | p.1 < p.2}))

end MatedCRT
