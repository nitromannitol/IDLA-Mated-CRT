import MatedCRT.Proofs.IDLA.Counts
import MatedCRT.Proofs.IDLA.Walkers
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff

/-!
# Lemma 5.2: the count `L` along a list of walkers

`lateCount U O a S l` is the number `L` of walkers of the list `l`, released one at a time from the aggregate `S`
(absorption region `U`), which hit `a` before exiting `O` but not before leaving the current aggregate
(`IsLateVisit`). It is the `lateVisitCount` of the walker sequence (`lateVisitCount_eq_lateCount`), it splits off
the first walker (`lateCount_cons`, by definition), and it is a measurable function of the walkers
(`measurable_lateCount`). The aggregates are `Absorption.aggRun`/`Absorption.aggStep`
(MatedCRT/Proofs/Sec6/ChanceOfBeingAbsorbed/Chernoff.lean).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The walker `x`, released from the aggregate `S`, hits `a` before exiting `O` but not before leaving `S`
(`σ ≤ τ_a < T`, line 2167). -/
def IsLateVisit (O : Set ℤ) (a : ℤ) (S : Set ℤ) (x : ℕ → ℤ) : Prop :=
  vExitTime S x ≤ vHitTime {a} x ∧ vHitTime {a} x < vExitTime O x

open Classical in
/-- `L` along the list of walkers `l` released from the aggregate `S` with absorption region `U`. -/
noncomputable def lateCount (U O : Set ℤ) (a : ℤ) : Set ℤ → List (ℕ → ℤ) → ℕ
  | _, [] => 0
  | S, x :: l => (if IsLateVisit O a S x then 1 else 0) + lateCount U O a (Absorption.aggStep U S x) l

theorem measurableSet_isLateVisit (O : Set ℤ) (a : ℤ) (S : Set ℤ) :
    MeasurableSet {x : ℕ → ℤ | IsLateVisit O a S x} :=
  (((measurable_vExitTime S).prodMk (measurable_vHitTime {a}))
    (MeasurableSet.of_discrete (s := {p : ℕ∞ × ℕ∞ | p.1 ≤ p.2}))).inter (measurableSet_hitBeforeExit O a)

open Classical in
theorem lateCount_append_singleton (U O : Set ℤ) (a : ℤ) (l : List (ℕ → ℤ)) (x : ℕ → ℤ) :
    ∀ S, lateCount U O a S (l ++ [x]) =
      lateCount U O a S l + (if IsLateVisit O a (Absorption.aggRun U S l) x then 1 else 0) := by
  induction l with
  | nil =>
    intro S
    simp only [lateCount, List.nil_append, Absorption.aggRun_nil, zero_add, add_zero]
    all_goals (split_ifs with h <;> simp [h])
  | cons y l ih =>
    intro S
    simp only [List.cons_append, lateCount, ih, Absorption.aggRun_cons]
    ring

open Classical in
/-- `lateVisitCount` of the walker sequence is `lateCount` of the list of its first `n` walkers. -/
theorem lateVisitCount_eq_lateCount (U O : Set ℤ) (a : ℤ) (xs : ℕ → ℕ → ℤ) (n : ℕ) :
    lateVisitCount (fun i => idlaAggregate ∅ U (List.ofFn fun j : Fin i => xs j)) O a xs n =
      lateCount U O a ∅ (List.ofFn fun i : Fin n => xs i) := by
  induction n with
  | zero => simp [lateVisitCount, lateCount]
  | succ n ih =>
    have hsplit : lateVisitCount (fun i => idlaAggregate ∅ U (List.ofFn fun j : Fin i => xs j)) O a xs (n + 1) =
        lateVisitCount (fun i => idlaAggregate ∅ U (List.ofFn fun j : Fin i => xs j)) O a xs n +
          (if IsLateVisit O a (idlaAggregate ∅ U (List.ofFn fun j : Fin n => xs j)) (xs n) then 1 else 0) := by
      unfold lateVisitCount
      rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
      congr 1
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1 h2
      · exact absurd h2 h1
      · rfl
    rw [hsplit, ih, List.ofFn_succ_last, lateCount_append_singleton]
    simp only [Fin.val_castSucc, Fin.val_last]
    rfl

open Classical in
theorem measurable_lateCount (U O : Set ℤ) (a : ℤ) :
    ∀ (k : ℕ) (S : Set ℤ), Measurable fun ys : Fin k → ℕ → ℤ => lateCount U O a S (List.ofFn ys)
  | 0, S => by
    have h0 : ∀ ys : Fin 0 → ℕ → ℤ, List.ofFn ys = [] := fun _ => List.ofFn_zero
    simp only [h0, lateCount]
    exact measurable_const
  | k + 1, S => by
    refine measurable_to_countable' fun n => ?_
    have h : (fun ys : Fin (k + 1) → ℕ → ℤ => lateCount U O a S (List.ofFn ys)) ⁻¹' {n} =
        ⋃ o : Option ℤ, (fun ys : Fin (k + 1) → ℕ → ℤ => ys 0) ⁻¹' {x | firstExitSite S x = o} ∩
          (((fun ys : Fin (k + 1) → ℕ → ℤ => ys 0) ⁻¹' {x | IsLateVisit O a S x} ∩
            (fun ys : Fin (k + 1) → ℕ → ℤ => fun i : Fin k => ys i.succ) ⁻¹'
              {zs | lateCount U O a (Absorption.nextAgg U S o) (List.ofFn zs) + 1 = n}) ∪
           ((fun ys : Fin (k + 1) → ℕ → ℤ => ys 0) ⁻¹' {x | IsLateVisit O a S x}ᶜ ∩
            (fun ys : Fin (k + 1) → ℕ → ℤ => fun i : Fin k => ys i.succ) ⁻¹'
              {zs | lateCount U O a (Absorption.nextAgg U S o) (List.ofFn zs) = n})) := by
      ext ys
      simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_inter_iff, mem_union, mem_ofPred_eq,
        mem_compl_iff]
      rw [List.ofFn_succ]
      simp only [lateCount, Absorption.aggStep_eq]
      constructor
      · intro hn
        refine ⟨firstExitSite S (ys 0), rfl, ?_⟩
        by_cases hl : IsLateVisit O a S (ys 0)
        · left
          simp only [hl, ↓reduceIte] at hn
          exact ⟨hl, by omega⟩
        · right
          simp only [hl, ↓reduceIte] at hn
          exact ⟨hl, by omega⟩
      · rintro ⟨o, ho, (⟨hl, hn⟩ | ⟨hl, hn⟩)⟩
        · rw [ho]
          simp only [hl, ↓reduceIte]
          omega
        · rw [ho]
          simp only [hl, ↓reduceIte]
          omega
    rw [h]
    have htail : Measurable fun ys : Fin (k + 1) → ℕ → ℤ => fun i : Fin k => ys i.succ :=
      Measurable.of_eval fun i => measurable_pi_apply _
    exact MeasurableSet.iUnion fun o =>
      ((Absorption.measurableSet_firstExitSite_eq S o).preimage (measurable_pi_apply 0)).inter
        ((((measurableSet_isLateVisit O a S).preimage (measurable_pi_apply 0)).inter
          (((measurable_lateCount U O a k _) (MeasurableSet.of_discrete
            (s := {j : ℕ | j + 1 = n}))).preimage htail)).union
        (((measurableSet_isLateVisit O a S).compl.preimage (measurable_pi_apply 0)).inter
          (((measurable_lateCount U O a k _) (MeasurableSet.of_discrete
            (s := {j : ℕ | j = n}))).preimage htail)))

end MatedCRT
