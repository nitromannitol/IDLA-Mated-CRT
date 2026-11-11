import Mathlib

/-! # Measurable least-index selections

Generic measurability facts behind the measurable selection of `OdometerMeasurableSelectionStep`
(Lemma 4.6; GAPS 2026-11-06 position-indexed pigeonhole). Every selected index is the least index
with a measurable property. The statements are relative to an explicit σ-algebra `M` on `Ω`. -/

namespace MatedCRT

open MeasureTheory Set

/-- The least `n` with `P ω n`, and `0` if there is none. Total in `ω`. -/
noncomputable def leastOr {Ω : Type} (P : Ω → ℕ → Prop) (ω : Ω) : ℕ := by
  classical
  exact if h : ∃ n, P ω n then Nat.find h else 0

lemma leastOr_spec {Ω : Type} (P : Ω → ℕ → Prop) (ω : Ω) (h : ∃ n, P ω n) :
    P ω (leastOr P ω) ∧ ∀ m < leastOr P ω, ¬ P ω m := by
  classical
  have hl : leastOr P ω = Nat.find h := by
    unfold leastOr
    split_ifs
    rfl
  rw [hl]
  exact ⟨Nat.find_spec h, fun m hm => Nat.find_min h hm⟩

lemma leastOr_of_not {Ω : Type} (P : Ω → ℕ → Prop) (ω : Ω) (h : ¬ ∃ n, P ω n) :
    leastOr P ω = 0 := by
  classical
  unfold leastOr
  split_ifs
  simp_all

/-- The least index selection is measurable when each level set is. -/
lemma measurable_leastOr {Ω : Type} (M : MeasurableSpace Ω) (P : Ω → ℕ → Prop)
    (hP : ∀ n, MeasurableSet[M] {ω | P ω n}) : Measurable[M] (leastOr P) := by
  classical
  -- the same least-index map, with a default witness at `0` when there is no index
  set P' : Ω → ℕ → Prop := fun ω n => P ω n ∨ (n = 0 ∧ ¬ ∃ m, P ω m) with hP'def
  have hex : ∀ ω, ∃ n, P' ω n := by
    intro ω
    by_cases h : ∃ m, P ω m
    · obtain ⟨m, hm⟩ := h
      exact ⟨m, Or.inl hm⟩
    · exact ⟨0, Or.inr ⟨rfl, h⟩⟩
  have hnone : MeasurableSet[M] {ω | ¬ ∃ m, P ω m} := by
    have heq : {ω | ¬ ∃ m, P ω m} = ⋂ m, {ω | P ω m}ᶜ := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iInter fun m => (hP m).compl
  have hP'meas : ∀ n, MeasurableSet[M] {ω | P' ω n} := by
    intro n
    exact (hP n).union ((MeasurableSet.const (n = 0)).inter hnone)
  have hfun : leastOr P = fun ω => Nat.find (hex ω) := by
    funext ω
    by_cases h : ∃ n, P ω n
    · have hsp := leastOr_spec P ω h
      apply le_antisymm
      · by_contra hlt
        rw [not_le] at hlt
        rcases Nat.find_spec (hex ω) with hPb | ⟨_, hne⟩
        · exact hsp.2 _ hlt hPb
        · exact hne h
      · exact Nat.find_min' (hex ω) (Or.inl hsp.1)
    · have h0 : Nat.find (hex ω) = 0 := by
        rw [Nat.find_eq_zero]
        exact Or.inr ⟨rfl, h⟩
      rw [h0, leastOr_of_not P ω h]
  rw [hfun]
  exact measurable_find hex hP'meas

/-- A family of measurable selections indexed by a measurable natural-valued map is measurable. -/
lemma measurable_comp_nat {Ω : Type} (M : MeasurableSpace Ω) {g : Ω → ℕ} (hg : Measurable[M] g)
    {f : ℕ → Ω → ℕ} (hf : ∀ n, Measurable[M] (f n)) :
    Measurable[M] (fun ω => f (g ω) ω) := by
  refine measurable_to_countable' fun v => ?_
  have heq : (fun ω => f (g ω) ω) ⁻¹' {v} = ⋃ n, {ω | g ω = n} ∩ {ω | f n ω = v} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨g ω, rfl, h⟩
    · rintro ⟨n, hn, hv⟩
      rw [hn]
      exact hv
  rw [heq]
  refine MeasurableSet.iUnion fun n => ?_
  exact (hg (measurableSet_singleton n)).inter ((hf n) (measurableSet_singleton v))

/-- The set of `ω` for which infinitely many `n` satisfy `P ω n` is measurable. -/
lemma measurableSet_infinite_nat {Ω : Type} (M : MeasurableSpace Ω) (P : Ω → ℕ → Prop)
    (hP : ∀ n, MeasurableSet[M] {ω | P ω n}) :
    MeasurableSet[M] {ω | {n | P ω n}.Infinite} := by
  have heq : {ω | {n | P ω n}.Infinite} = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ _ : N < n, {ω | P ω n} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro h N
      obtain ⟨b, hb, hNb⟩ := h.exists_gt N
      exact ⟨b, hNb, hb⟩
    · intro h
      refine Set.infinite_of_forall_exists_gt fun N => ?_
      obtain ⟨b, hb, hPb⟩ := h N
      exact ⟨b, hPb, hb⟩
  rw [heq]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ => hP n

end MatedCRT
