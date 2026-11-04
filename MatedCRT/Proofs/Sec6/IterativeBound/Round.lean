import MatedCRT.Steps.Sec6.IterativeBound
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff

/-!
# Lemma 6.10: one round of the iteration (lines 2715-2726, 2767-2775)

* `measurableSet_aggRun`: every event of the aggregate `A(S; x₁, …, x_k → U)` is measurable in the walks.
* `aggRun_eq_union_finset`: the aggregate is `S` plus finitely many sites, so it takes countably many values.
* `walkersLaw_not_subset_le_lintegral`: the Abelian property (compared on each value of the aggregate) for the events
  `{A(Θ; a) ⊄ T}`: `P[A(Θ; a) ⊄ T] ≤ E[P[A(A(Θ; a → Θ'); P(Θ; a → Θ')) ⊄ T]]`.
* `walkersLaw_not_subset_le_round`: the round bound `P[A(Θ; a) ⊄ T] ≤ P[Gᶜ] + sup_G P[restarted ⊄ T]`.
* `foldl_idlaStep_facts`: the stopped run absorbs inside `Θ'`, `|A \ Θ| + |P| ≤ k`, and (walks along edges from
  `cl(Θ)`) the stopped positions lie in `cl(A)`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace IterativeBound

open Absorption

/-! ### Measurability and countability of the aggregate -/

theorem measurableSet_aggRun (U : Set ℤ) (P : Set ℤ → Prop) :
    ∀ (k : ℕ) (S : Set ℤ), MeasurableSet {xs : Fin k → ℕ → ℤ | P (aggRun U S (List.ofFn xs))}
  | 0, S => by
    have h0 : ∀ xs : Fin 0 → ℕ → ℤ, List.ofFn xs = [] := fun _ => List.ofFn_zero
    simp only [h0, aggRun_nil]
    exact MeasurableSet.const _
  | k + 1, S => by
    have h : {xs : Fin (k + 1) → ℕ → ℤ | P (aggRun U S (List.ofFn xs))} =
        ⋃ o : Option ℤ, (fun xs : Fin (k + 1) → ℕ → ℤ => xs 0) ⁻¹' {x | firstExitSite S x = o} ∩
          (fun xs : Fin (k + 1) → ℕ → ℤ => fun i : Fin k => xs i.succ) ⁻¹'
            {ys | P (aggRun U (nextAgg U S o) (List.ofFn ys))} := by
      ext xs
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, List.ofFn_succ, aggRun_cons, aggStep_eq]
      constructor
      · intro hx
        exact ⟨_, rfl, hx⟩
      · rintro ⟨o, ho, hx⟩
        rw [ho]
        exact hx
    rw [h]
    exact MeasurableSet.iUnion fun o =>
      ((measurableSet_firstExitSite_eq S o).preimage (measurable_pi_apply 0)).inter
        ((measurableSet_aggRun U P k (nextAgg U S o)).preimage
          (Measurable.of_eval fun i => measurable_pi_apply _))

theorem nextAgg_eq_union_finset (U S : Set ℤ) (o : Option ℤ) : ∃ F : Finset ℤ, nextAgg U S o = S ∪ ↑F := by
  cases o with
  | none => exact ⟨∅, by simp [nextAgg]⟩
  | some b =>
    by_cases hb : b ∈ U
    · exact ⟨{b}, by simp [nextAgg, hb]⟩
    · exact ⟨∅, by simp [nextAgg, hb]⟩

theorem aggRun_eq_union_finset (U : Set ℤ) :
    ∀ (l : List (ℕ → ℤ)) (S : Set ℤ), ∃ F : Finset ℤ, aggRun U S l = S ∪ ↑F
  | [], S => ⟨∅, by simp⟩
  | x :: l, S => by
    obtain ⟨F₁, h₁⟩ := nextAgg_eq_union_finset U S (firstExitSite S x)
    obtain ⟨F₂, h₂⟩ := aggRun_eq_union_finset U l (nextAgg U S (firstExitSite S x))
    refine ⟨F₁ ∪ F₂, ?_⟩
    rw [aggRun_cons, aggStep_eq, h₂, h₁, Finset.coe_union, union_assoc]

/-- The values `Θ ∪ F`, `F` finite: a countable family containing every aggregate started from `Θ`. -/
def finExt (Θ : Set ℤ) : Set (Set ℤ) := range fun F : Finset ℤ => Θ ∪ ↑F

theorem finExt_countable (Θ : Set ℤ) : (finExt Θ).Countable := countable_range _

theorem aggRun_mem_finExt (U Θ : Set ℤ) (l : List (ℕ → ℤ)) : aggRun U Θ l ∈ finExt Θ := by
  obtain ⟨F, hF⟩ := aggRun_eq_union_finset U l Θ
  exact ⟨F, hF.symm⟩

theorem aggRun_mem_finExt_of_mem {U Θ S : Set ℤ} (hS : S ∈ finExt Θ) (l : List (ℕ → ℤ)) :
    aggRun U S l ∈ finExt Θ := by
  obtain ⟨F, rfl⟩ := hS
  obtain ⟨G, hG⟩ := aggRun_eq_union_finset U l (Θ ∪ ↑F)
  exact ⟨F ∪ G, by simp only [hG, Finset.coe_union, union_assoc]⟩

/-! ### The Abelian property for the events `{A ⊄ T}` -/

/-- `∑' ∫⁻ ≤ ∫⁻ ∑'` for arbitrary (not necessarily measurable) functions. -/
theorem tsum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (f : ι → α → ℝ≥0∞) :
    ∑' i, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑' i, f i a ∂μ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert i s hi ih =>
          simp only [Finset.sum_insert hi]
          exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)
    _ ≤ ∫⁻ a, ∑' i, f i a ∂μ := lintegral_mono fun a => ENNReal.sum_le_tsum s

/-- The event `{A(S; xs) ⊄ T}` (aggregate started from `S ∈ finExt Θ`) as a disjoint union over the countably many
values of the aggregate. -/
theorem measure_aggRun_not_subset_eq_tsum (m : ℤ → ℤ → ℕ) {k : ℕ} (a : Fin k → ℤ) {Θ S : Set ℤ}
    (hS : S ∈ finExt Θ) (T : Set ℤ) :
    walkersLaw m a {xs | ¬ aggRun univ S (List.ofFn xs) ⊆ T} =
      ∑' B : {B | B ∈ finExt Θ ∧ ¬ B ⊆ T},
        walkersLaw m a {xs | aggRun univ S (List.ofFn xs) = (B : Set ℤ)} := by
  have hc : {B | B ∈ finExt Θ ∧ ¬ B ⊆ T}.Countable := (finExt_countable Θ).mono fun B hB => hB.1
  have heq : {xs : Fin k → ℕ → ℤ | ¬ aggRun univ S (List.ofFn xs) ⊆ T} =
      ⋃ B ∈ {B | B ∈ finExt Θ ∧ ¬ B ⊆ T}, {xs | aggRun univ S (List.ofFn xs) = B} := by
    ext xs
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨aggRun_mem_finExt_of_mem hS _, h⟩, rfl⟩
    · rintro ⟨B, ⟨-, hB⟩, rfl⟩
      exact hB
  rw [heq, measure_biUnion hc]
  · intro B₁ _ B₂ _ hne
    exact Set.disjoint_left.2 fun xs h₁ h₂ => hne (h₁.symm.trans h₂)
  · intro B _
    exact measurableSet_aggRun univ (fun A => A = B) k S

/-- **The Abelian property for the events `{A ⊄ T}`** (from the comparison on each value of the aggregate). -/
theorem walkersLaw_not_subset_le_lintegral {m : ℤ → ℤ → ℕ} (hab : IsAbelianIDLA m) {Θ Θ' : Set ℤ} (hΘ : Θ ⊆ Θ')
    {k : ℕ} (a : Fin k → ℤ) (T : Set ℤ) :
    walkersLaw m a {xs | ¬ idlaAggregate Θ univ (List.ofFn xs) ⊆ T} ≤
      ∫⁻ xs, walkersLaw m (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
          (idlaStopped Θ Θ' (List.ofFn xs)).get i)
        {ys | ¬ idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) ⊆ T}
        ∂walkersLaw m a := by
  have hΘmem : Θ ∈ finExt Θ := ⟨∅, by simp⟩
  calc walkersLaw m a {xs | ¬ idlaAggregate Θ univ (List.ofFn xs) ⊆ T}
      = ∑' B : {B | B ∈ finExt Θ ∧ ¬ B ⊆ T},
          walkersLaw m a {xs | idlaAggregate Θ univ (List.ofFn xs) = (B : Set ℤ)} :=
        measure_aggRun_not_subset_eq_tsum m a hΘmem T
    _ = ∑' B : {B | B ∈ finExt Θ ∧ ¬ B ⊆ T},
          ∫⁻ xs, walkersLaw m (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
              (idlaStopped Θ Θ' (List.ofFn xs)).get i)
            {ys | idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) = (B : Set ℤ)}
            ∂walkersLaw m a := by
        congr 1
        ext B
        exact hab Θ Θ' k a hΘ B
    _ ≤ ∫⁻ xs, ∑' B : {B | B ∈ finExt Θ ∧ ¬ B ⊆ T},
          walkersLaw m (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
              (idlaStopped Θ Θ' (List.ofFn xs)).get i)
            {ys | idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) = (B : Set ℤ)}
            ∂walkersLaw m a := tsum_lintegral_le _ _
    _ = ∫⁻ xs, walkersLaw m (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
          (idlaStopped Θ Θ' (List.ofFn xs)).get i)
        {ys | ¬ idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) ⊆ T}
        ∂walkersLaw m a := by
        refine lintegral_congr fun xs => ?_
        exact (measure_aggRun_not_subset_eq_tsum m _ (aggRun_mem_finExt Θ' Θ (List.ofFn xs)) T).symm

/-- **One round.** If the restarted walkers fail with probability at most `c` on the event `G` of the first stage,
then `P[A(Θ; a) ⊄ T] ≤ P[Gᶜ] + c`. -/
theorem walkersLaw_not_subset_le_round {m : ℤ → ℤ → ℕ} (hab : IsAbelianIDLA m) {Θ Θ' : Set ℤ} (hΘ : Θ ⊆ Θ')
    {k : ℕ} (a : Fin k → ℤ) (T : Set ℤ) (G : Set (Fin k → ℕ → ℤ)) (c : ℝ≥0∞)
    (hG : ∀ xs ∈ G, walkersLaw m (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
        (idlaStopped Θ Θ' (List.ofFn xs)).get i)
      {ys | ¬ idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) ⊆ T} ≤ c) :
    walkersLaw m a {xs | ¬ idlaAggregate Θ univ (List.ofFn xs) ⊆ T} ≤ walkersLaw m a Gᶜ + c := by
  refine (walkersLaw_not_subset_le_lintegral hab hΘ a T).trans ?_
  set M := toMeasurable (walkersLaw m a) Gᶜ with hM
  have hpt : ∀ xs, walkersLaw m (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
        (idlaStopped Θ Θ' (List.ofFn xs)).get i)
      {ys | ¬ idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) ⊆ T} ≤
        M.indicator 1 xs + c := by
    intro xs
    by_cases hxs : xs ∈ M
    · rw [indicator_of_mem hxs]
      exact prob_le_one.trans le_self_add
    · have : xs ∈ G := by
        by_contra h
        exact hxs (subset_toMeasurable _ _ h)
      exact (hG xs this).trans le_add_self
  calc _ ≤ ∫⁻ xs, (M.indicator 1 xs + c) ∂walkersLaw m a := lintegral_mono hpt
    _ = walkersLaw m a M + c := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_indicator_one (measurableSet_toMeasurable _ _), lintegral_const, measure_univ, mul_one]
    _ = walkersLaw m a Gᶜ + c := by rw [hM, measure_toMeasurable]

/-! ### Invariants of the stopped run -/

/-- One walker of the stopped run: it is absorbed inside `Θ'` or stopped outside `Θ'`, next to the aggregate. -/
theorem idlaStep_facts (m : ℤ → ℤ → ℕ) {Θ Θ' A : Set ℤ} {p : List ℤ} {x : ℕ → ℤ}
    (h1 : Θ ⊆ A) (h2 : A ⊆ Θ') (h3 : (A \ Θ).Finite) (h4 : ∀ b ∈ p, b ∉ Θ' ∧ ∃ c ∈ A, m c b ≠ 0)
    (hx0 : x 0 ∈ vClosure m Θ) (hxadj : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) :
    Θ ⊆ (idlaStep Θ' (A, p) x).1 ∧ (idlaStep Θ' (A, p) x).1 ⊆ Θ' ∧ ((idlaStep Θ' (A, p) x).1 \ Θ).Finite ∧
      ((idlaStep Θ' (A, p) x).1 \ Θ).ncard + (idlaStep Θ' (A, p) x).2.length ≤ (A \ Θ).ncard + p.length + 1 ∧
      ∀ b ∈ (idlaStep Θ' (A, p) x).2, b ∉ Θ' ∧ ∃ c ∈ (idlaStep Θ' (A, p) x).1, m c b ≠ 0 := by
  rcases ho : firstExitSite A x with _ | b
  · simp only [idlaStep, ho]
    exact ⟨h1, h2, h3, by omega, h4⟩
  · have hbA : b ∉ A := not_mem_of_firstExitSite_eq_some ho
    by_cases hb : b ∈ Θ'
    · simp only [idlaStep, ho, hb, ↓reduceIte]
      have hbΘ : b ∉ Θ := fun h => hbA (h1 h)
      have hdiff : (A ∪ {b}) \ Θ = insert b (A \ Θ) := by
        rw [union_singleton, insert_sdiff_of_notMem _ hbΘ]
      refine ⟨h1.trans subset_union_left, union_subset h2 (singleton_subset_iff.2 hb), ?_, ?_, ?_⟩
      · rw [hdiff]
        exact h3.insert b
      · rw [hdiff, ncard_insert_of_notMem (fun h => hbA h.1) h3]
        omega
      · intro c hc
        obtain ⟨hc1, d, hd, hdc⟩ := h4 c hc
        exact ⟨hc1, d, Or.inl hd, hdc⟩
    · simp only [idlaStep, ho, hb, ↓reduceIte]
      refine ⟨h1, h2, h3, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro c hc
        rw [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | hc
        · exact h4 c hc
        · rw [hc]
          refine ⟨hb, ?_⟩
          obtain ⟨n, hn, -, hlt⟩ := firstExitSite_eq_some_iff.1 ho
          cases n with
          | zero =>
            rw [hn] at hx0
            rcases hx0 with hx0 | ⟨-, c, hc, hcb⟩
            · exact absurd (h1 hx0) hbA
            · exact ⟨c, h1 hc, hcb⟩
          | succ j =>
            have hj : x j ∈ A := hlt j (Nat.lt_succ_self j)
            refine ⟨x j, hj, ?_⟩
            rcases hxadj j with h | h
            · rw [hn] at h
              exact absurd (h ▸ hj) hbA
            · rw [hn] at h
              exact h

/-- The invariants along the stopped run. -/
theorem foldl_idlaStep_facts (m : ℤ → ℤ → ℕ) {Θ Θ' : Set ℤ} :
    ∀ (l : List (ℕ → ℤ)) (A : Set ℤ) (p : List ℤ), Θ ⊆ A → A ⊆ Θ' → (A \ Θ).Finite →
      (∀ b ∈ p, b ∉ Θ' ∧ ∃ c ∈ A, m c b ≠ 0) →
      (∀ x ∈ l, x 0 ∈ vClosure m Θ ∧ ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) →
      Θ ⊆ (l.foldl (idlaStep Θ') (A, p)).1 ∧ (l.foldl (idlaStep Θ') (A, p)).1 ⊆ Θ' ∧
      ((l.foldl (idlaStep Θ') (A, p)).1 \ Θ).Finite ∧
      ((l.foldl (idlaStep Θ') (A, p)).1 \ Θ).ncard + (l.foldl (idlaStep Θ') (A, p)).2.length ≤
        (A \ Θ).ncard + p.length + l.length ∧
      ∀ b ∈ (l.foldl (idlaStep Θ') (A, p)).2, b ∉ Θ' ∧ ∃ c ∈ (l.foldl (idlaStep Θ') (A, p)).1, m c b ≠ 0
  | [], A, p, h1, h2, h3, h4, _ => by
    simp only [List.foldl_nil, List.length_nil, add_zero]
    exact ⟨h1, h2, h3, le_rfl, h4⟩
  | x :: l, A, p, h1, h2, h3, h4, h5 => by
    rw [List.foldl_cons]
    obtain ⟨hx0, hxadj⟩ := h5 x List.mem_cons_self
    have h5' : ∀ y ∈ l, y 0 ∈ vClosure m Θ ∧ ∀ n, y (n + 1) = y n ∨ m (y n) (y (n + 1)) ≠ 0 :=
      fun y hy => h5 y (List.mem_cons_of_mem x hy)
    have key := idlaStep_facts m h1 h2 h3 h4 hx0 hxadj
    rcases hs : idlaStep Θ' (A, p) x with ⟨A₁, p₁⟩
    simp only [hs] at key
    obtain ⟨k1, k2, k3, k4, k5⟩ := key
    obtain ⟨r1, r2, r3, r4, r5⟩ := foldl_idlaStep_facts m l A₁ p₁ k1 k2 k3 k5 h5'
    refine ⟨r1, r2, r3, ?_, r5⟩
    simp only [List.length_cons]
    omega

/-- The invariants of the stopped run `A(Θ; xs → Θ')`, `P(Θ; xs → Θ')` for walks along edges from `cl(Θ)`:
`Θ ⊆ A ⊆ Θ'`, `|A \ Θ| + |P| ≤ k`, and the stopped positions lie outside `Θ'` next to `A`, hence in `cl(A)`. -/
theorem idlaRun_facts (m : ℤ → ℤ → ℕ) {Θ Θ' : Set ℤ} (hΘ : Θ ⊆ Θ') {k : ℕ} {xs : Fin k → ℕ → ℤ}
    (hxs : ∀ x ∈ List.ofFn xs, x 0 ∈ vClosure m Θ ∧ ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) :
    Θ ⊆ idlaAggregate Θ Θ' (List.ofFn xs) ∧ idlaAggregate Θ Θ' (List.ofFn xs) ⊆ Θ' ∧
      (idlaAggregate Θ Θ' (List.ofFn xs) \ Θ).Finite ∧
      (idlaAggregate Θ Θ' (List.ofFn xs) \ Θ).ncard + (idlaStopped Θ Θ' (List.ofFn xs)).length ≤ k ∧
      ∀ b ∈ idlaStopped Θ Θ' (List.ofFn xs), b ∉ Θ' ∧ b ∈ vClosure m (idlaAggregate Θ Θ' (List.ofFn xs)) := by
  have h := foldl_idlaStep_facts m (List.ofFn xs) Θ [] subset_rfl hΘ (by simp) (by simp) hxs
  simp only [Set.sdiff_self, ncard_empty, List.length_nil, List.length_ofFn, zero_add] at h
  obtain ⟨r1, r2, r3, r4, r5⟩ := h
  refine ⟨r1, r2, r3, r4, fun b hb => ?_⟩
  obtain ⟨hb1, c, hc, hcb⟩ := r5 b hb
  exact ⟨hb1, Or.inr ⟨fun h => hb1 (r2 h), c, hc, hcb⟩⟩

/-- Walkers started in `cl(Θ)` almost surely start there and move along edges. -/
theorem ae_walkersLaw_path {m : ℤ → ℤ → ℕ} (hsrw : IsSrwPathLaw m) {Θ : Set ℤ} {k : ℕ} {a : Fin k → ℤ}
    (ha : ∀ i, a i ∈ vClosure m Θ) :
    ∀ᵐ xs ∂walkersLaw m a, ∀ x ∈ List.ofFn xs,
      x 0 ∈ vClosure m Θ ∧ ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0 := by
  have h : ∀ i, ∀ᵐ xs ∂walkersLaw m a,
      xs i 0 = a i ∧ ∀ n, xs i (n + 1) = xs i n ∨ m (xs i n) (xs i (n + 1)) ≠ 0 := by
    intro i
    unfold walkersLaw
    exact (Measure.tendsto_eval_ae_ae (μ := fun i => srwLaw m (a i)) (i := i)).eventually (hsrw (a i))
  filter_upwards [ae_all_iff.2 h] with xs hxs x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact ⟨(hxs i).1 ▸ ha i, (hxs i).2⟩

end IterativeBound

end MatedCRT
