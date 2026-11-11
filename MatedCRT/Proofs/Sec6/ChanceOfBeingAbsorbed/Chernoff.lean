import MatedCRT.Steps.Sec6.ChanceOfBeingAbsorbed

/-!
# Lemma 6.9: the Chernoff-type iteration (`AbsorptionChernoffStep`)

The walkers of `walkersLaw` are independent. Releasing them one at a time from the aggregate `S`, the `k'`-th walker
is absorbed in `U` (it leaves the current aggregate at a site of `U`) with probability at least `s₂` whatever the
first `k' - 1` walkers did; each absorption adds one site outside `Θ`. By induction on the number of walkers, the
exponential moment `E[2^{-N}]` of the number `N` of sites added outside `Θ` is at most `(1 - s₂/2)^k`, and Markov's
inequality gives `P[N ≤ s₂ k/4] ≤ e^{s₂ k/4} (1 - s₂/2)^k ≤ e^{-s₂ k/4}`.
-/

namespace MatedCRT

namespace Absorption

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

instance isProbabilityMeasure_walkersLaw (m : ℤ → ℤ → ℕ) {k : ℕ} (a : Fin k → ℤ) :
    IsProbabilityMeasure (walkersLaw m a) := by
  unfold walkersLaw; infer_instance

/-! ### The aggregate, forgetting the stopped walkers -/

/-- The aggregate obtained from the occupied set `S` by releasing the walkers `l` with absorption region `U`. -/
noncomputable def aggRun (U S : Set ℤ) (l : List (ℕ → ℤ)) : Set ℤ :=
  (l.foldl (idlaStep U) (S, [])).1

/-- The aggregate after releasing one walker `x` from the occupied set `S`. -/
noncomputable def aggStep (U S : Set ℤ) (x : ℕ → ℤ) : Set ℤ :=
  (idlaStep U (S, []) x).1

/-- The walker `x` released from the occupied set `S` is absorbed in `U`: the first site outside `S` which it visits
lies in `U`. -/
def Absorbs (U S : Set ℤ) (x : ℕ → ℤ) : Prop :=
  ∃ b ∈ U, firstExitSite S x = some b

open Classical in
/-- The aggregate after one walker, as a function of its first exit site from `S`. -/
noncomputable def nextAgg (U S : Set ℤ) : Option ℤ → Set ℤ
  | some b => if b ∈ U then S ∪ {b} else S
  | none => S

theorem idlaStep_fst (U S : Set ℤ) (p p' : List ℤ) (x : ℕ → ℤ) :
    (idlaStep U (S, p) x).1 = (idlaStep U (S, p') x).1 := by
  dsimp only [idlaStep]
  cases firstExitSite S x with
  | none => rfl
  | some b => by_cases hb : b ∈ U <;> simp [hb]

theorem foldl_idlaStep_fst (U : Set ℤ) :
    ∀ (l : List (ℕ → ℤ)) (S : Set ℤ) (p p' : List ℤ),
      (l.foldl (idlaStep U) (S, p)).1 = (l.foldl (idlaStep U) (S, p')).1
  | [], _, _, _ => rfl
  | x :: l, S, p, p' => by
    simp only [List.foldl_cons]
    have h := idlaStep_fst U S p p' x
    rcases hs : idlaStep U (S, p) x with ⟨A, q⟩
    rcases hs' : idlaStep U (S, p') x with ⟨A', q'⟩
    rw [hs, hs'] at h
    simp only at h
    subst h
    exact foldl_idlaStep_fst U l A q q'

theorem idlaAggregate_eq_aggRun (Θ U : Set ℤ) (l : List (ℕ → ℤ)) : idlaAggregate Θ U l = aggRun U Θ l := rfl

@[simp] theorem aggRun_nil (U S : Set ℤ) : aggRun U S [] = S := rfl

theorem aggRun_cons (U S : Set ℤ) (x : ℕ → ℤ) (l : List (ℕ → ℤ)) :
    aggRun U S (x :: l) = aggRun U (aggStep U S x) l := by
  unfold aggRun aggStep
  rw [List.foldl_cons]
  rcases hs : idlaStep U (S, []) x with ⟨A, q⟩
  exact foldl_idlaStep_fst U l A q []

theorem aggStep_eq (U S : Set ℤ) (x : ℕ → ℤ) : aggStep U S x = nextAgg U S (firstExitSite S x) := by
  unfold aggStep
  dsimp only [idlaStep]
  cases firstExitSite S x with
  | none => rfl
  | some b => by_cases hb : b ∈ U <;> simp [nextAgg, hb]

/-! ### First exit sites -/

open Classical in
theorem firstExitSite_eq_some_iff {S : Set ℤ} {x : ℕ → ℤ} {b : ℤ} :
    firstExitSite S x = some b ↔ ∃ n, x n = b ∧ b ∉ S ∧ ∀ j < n, x j ∈ S := by
  unfold firstExitSite
  split_ifs with h
  · constructor
    · intro e
      have e' : x (Nat.find h) = b := Option.some_injective _ e
      refine ⟨Nat.find h, e', e' ▸ Nat.find_spec h, fun j hj => ?_⟩
      exact not_not.1 (Nat.find_min h hj)
    · rintro ⟨n, hn, hb, hlt⟩
      have hfind : Nat.find h = n := by
        rw [Nat.find_eq_iff]
        exact ⟨by rw [hn]; exact hb, fun j hj => not_not.2 (hlt j hj)⟩
      rw [hfind, hn]
  · constructor
    · intro e; exact absurd e (by simp)
    · rintro ⟨n, hn, hb, -⟩
      exact absurd ⟨n, by rw [hn]; exact hb⟩ h

open Classical in
theorem firstExitSite_eq_none_iff {S : Set ℤ} {x : ℕ → ℤ} :
    firstExitSite S x = none ↔ ∀ n, x n ∈ S := by
  unfold firstExitSite
  split_ifs with h
  · constructor
    · intro e; exact absurd e (by simp)
    · intro hall
      obtain ⟨n, hn⟩ := h
      exact absurd (hall n) hn
  · exact ⟨fun _ n => not_not.1 fun hn => h ⟨n, hn⟩, fun _ => rfl⟩

theorem not_mem_of_firstExitSite_eq_some {S : Set ℤ} {x : ℕ → ℤ} {b : ℤ} (h : firstExitSite S x = some b) :
    b ∉ S := by
  obtain ⟨_, _, hb, _⟩ := firstExitSite_eq_some_iff.1 h
  exact hb

open Classical in
/-- Before its exit time from `U`, a path is in `U`. -/
theorem mem_of_lt_vExitTime {U : Set ℤ} {x : ℕ → ℤ} {j : ℕ} (h : (j : ℕ∞) < vExitTime U x) : x j ∈ U := by
  unfold vExitTime at h
  split_ifs at h with hex
  · have hj : j < Nat.find hex := by exact_mod_cast h
    exact not_not.1 (Nat.find_min hex hj)
  · exact not_not.1 fun hj => hex ⟨j, hj⟩

open Classical in
/-- A walker which visits `U \ S` before exiting `U` is absorbed in `U` by the aggregate `S`. -/
theorem absorbs_of_visit {U S : Set ℤ} {x : ℕ → ℤ} {n : ℕ} (hn : (n : ℕ∞) < vExitTime U x) (hxS : x n ∉ S) :
    Absorbs U S x := by
  have hex : ∃ j, x j ∉ S := ⟨n, hxS⟩
  have hle : Nat.find hex ≤ n := Nat.find_min' hex hxS
  refine ⟨x (Nat.find hex), mem_of_lt_vExitTime (lt_of_le_of_lt (by exact_mod_cast hle) hn), ?_⟩
  exact firstExitSite_eq_some_iff.2
    ⟨Nat.find hex, rfl, Nat.find_spec hex, fun j hj => not_not.1 (Nat.find_min hex hj)⟩

/-! ### Measurability -/

theorem measurableSet_firstExitSite_eq (S : Set ℤ) (o : Option ℤ) :
    MeasurableSet {x : ℕ → ℤ | firstExitSite S x = o} := by
  cases o with
  | none =>
    have : {x : ℕ → ℤ | firstExitSite S x = none} = ⋂ n, (fun x : ℕ → ℤ => x n) ⁻¹' S := by
      ext x; simp [firstExitSite_eq_none_iff]
    rw [this]
    exact MeasurableSet.iInter fun n => (Set.to_countable S).measurableSet.preimage (measurable_pi_apply n)
  | some b =>
    have : {x : ℕ → ℤ | firstExitSite S x = some b} =
        ⋃ n : ℕ, (fun x : ℕ → ℤ => fun j : Fin (n + 1) => x j) ⁻¹'
          {y | y (Fin.last n) = b ∧ b ∉ S ∧ ∀ j : Fin (n + 1), (j : ℕ) < n → y j ∈ S} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_preimage, Fin.val_last, firstExitSite_eq_some_iff]
      constructor
      · rintro ⟨n, h1, h2, h3⟩
        exact ⟨n, h1, h2, fun j hj => h3 j hj⟩
      · rintro ⟨n, h1, h2, h3⟩
        exact ⟨n, h1, h2, fun j hj => h3 ⟨j, by omega⟩ hj⟩
    rw [this]
    exact MeasurableSet.iUnion fun n => (Set.to_countable _).measurableSet.preimage
      (Measurable.of_eval fun j => measurable_pi_apply _)

theorem measurableSet_absorbs (U S : Set ℤ) : MeasurableSet {x : ℕ → ℤ | Absorbs U S x} := by
  have : {x : ℕ → ℤ | Absorbs U S x} = ⋃ b : ℤ, {_x : ℕ → ℤ | b ∈ U} ∩ {x | firstExitSite S x = some b} := by
    ext x; simp [Absorbs]
  rw [this]
  exact MeasurableSet.iUnion fun b => (MeasurableSet.const _).inter (measurableSet_firstExitSite_eq S (some b))

theorem ofFn_cons' {k : ℕ} (x : ℕ → ℤ) (ys : Fin k → ℕ → ℤ) :
    List.ofFn (Fin.cons x ys : Fin (k + 1) → ℕ → ℤ) = x :: List.ofFn ys := by
  simp [List.ofFn_succ]

theorem measurableSet_aggRun_ncard_eq (U Θ : Set ℤ) :
    ∀ (k : ℕ) (S : Set ℤ) (n : ℕ),
      MeasurableSet {xs : Fin k → ℕ → ℤ | (aggRun U S (List.ofFn xs) \ Θ).ncard = n}
  | 0, S, n => by
    have h0 : ∀ xs : Fin 0 → ℕ → ℤ, List.ofFn xs = [] := fun _ => List.ofFn_zero
    simp only [h0, aggRun_nil]
    exact MeasurableSet.const _
  | k + 1, S, n => by
    have h : {xs : Fin (k + 1) → ℕ → ℤ | (aggRun U S (List.ofFn xs) \ Θ).ncard = n} =
        ⋃ o : Option ℤ, (fun xs : Fin (k + 1) → ℕ → ℤ => xs 0) ⁻¹' {x | firstExitSite S x = o} ∩
          (fun xs : Fin (k + 1) → ℕ → ℤ => fun i : Fin k => xs i.succ) ⁻¹'
            {ys | (aggRun U (nextAgg U S o) (List.ofFn ys) \ Θ).ncard = n} := by
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
        ((measurableSet_aggRun_ncard_eq U Θ k (nextAgg U S o) n).preimage
          (Measurable.of_eval fun i => measurable_pi_apply _))

theorem measurable_aggRun_ncard (U Θ S : Set ℤ) (k : ℕ) :
    Measurable fun xs : Fin k → ℕ → ℤ => (aggRun U S (List.ofFn xs) \ Θ).ncard :=
  measurable_to_countable' fun n => measurableSet_aggRun_ncard_eq U Θ k S n

/-! ### Splitting off the first walker -/

theorem lintegral_walkersLaw_succ (m : ℤ → ℤ → ℕ) {k : ℕ} (a : Fin (k + 1) → ℤ)
    (F : (Fin (k + 1) → ℕ → ℤ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ xs, F xs ∂walkersLaw m a =
      ∫⁻ x, ∫⁻ ys, F (Fin.cons x ys) ∂walkersLaw m (fun i => a i.succ) ∂srwLaw m (a 0) := by
  have hmp := measurePreserving_piFinSuccAbove (fun i : Fin (k + 1) => srwLaw m (a i)) 0
  have he : ∀ p : (ℕ → ℤ) × (Fin k → ℕ → ℤ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℕ → ℤ) 0).symm p = Fin.cons p.1 p.2 := by
    intro p
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    exact Fin.insertNth_zero' p.1 p.2
  have hμ : (Measure.pi fun j : Fin k => srwLaw m (a (Fin.succAbove 0 j))) = walkersLaw m (fun i => a i.succ) := by
    unfold walkersLaw
    congr 1
  calc ∫⁻ xs, F xs ∂walkersLaw m a
      = ∫⁻ xs, (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℕ → ℤ) 0).symm)
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℕ → ℤ) 0) xs)
          ∂Measure.pi (fun i : Fin (k + 1) => srwLaw m (a i)) := by
        unfold walkersLaw
        simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
    _ = ∫⁻ p, (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℕ → ℤ) 0).symm) p
          ∂((srwLaw m (a 0)).prod (Measure.pi fun j : Fin k => srwLaw m (a (Fin.succAbove 0 j)))) :=
        hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _
    _ = ∫⁻ x, ∫⁻ ys, (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℕ → ℤ) 0).symm) (x, ys)
          ∂(Measure.pi fun j : Fin k => srwLaw m (a (Fin.succAbove 0 j))) ∂srwLaw m (a 0) :=
        lintegral_prod _ (hF.comp (MeasurableEquiv.measurable _)).aemeasurable
    _ = _ := by
        rw [hμ]
        simp only [Function.comp_apply, he]

/-! ### The exponential moment -/

/-- The weight `1/2` on absorption and `1` otherwise. -/
noncomputable def absorbWeight (U S : Set ℤ) (x : ℕ → ℤ) : ℝ≥0∞ :=
  {x | Absorbs U S x}.indicator (fun _ => ENNReal.ofReal (1 / 2)) x + {x | Absorbs U S x}ᶜ.indicator (fun _ => 1) x

theorem absorbWeight_of_absorbs {U S : Set ℤ} {x : ℕ → ℤ} (h : Absorbs U S x) :
    absorbWeight U S x = ENNReal.ofReal (1 / 2) := by
  simp [absorbWeight, h]

theorem absorbWeight_of_not_absorbs {U S : Set ℤ} {x : ℕ → ℤ} (h : ¬ Absorbs U S x) :
    absorbWeight U S x = 1 := by
  simp [absorbWeight, h]

theorem one_sub_add_half_le {t : ℝ≥0∞} {s₂ : ℝ} (ht1 : t ≤ 1) (hs : ENNReal.ofReal s₂ ≤ t) :
    ENNReal.ofReal (1 / 2) * t + (1 - t) ≤ ENNReal.ofReal (1 - s₂ / 2) := by
  have htop : t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ht1
  rw [← ENNReal.ofReal_toReal htop] at ht1 hs ⊢
  have hτ0 : 0 ≤ t.toReal := ENNReal.toReal_nonneg
  have hτ1 : t.toReal ≤ 1 := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at ht1
  have hsτ : s₂ ≤ t.toReal := (ENNReal.ofReal_le_ofReal_iff hτ0).1 hs
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hτ0,
    ← ENNReal.ofReal_add (by positivity) (by linarith)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem lintegral_half_pow_le (m : ℤ → ℤ → ℕ) (Θ U : Set ℤ) (s₂ L : ℝ)
    (habs : ∀ a ∈ vClosure m Θ, ∀ S : Set ℤ, Θ ⊆ S → (S \ Θ).Finite → ((S \ Θ).ncard : ℝ) < L →
      ENNReal.ofReal s₂ ≤ srwLaw m a {x | Absorbs U S x}) :
    ∀ (k : ℕ) (a : Fin k → ℤ) (S : Set ℤ), (∀ i, a i ∈ vClosure m Θ) → Θ ⊆ S → (S \ Θ).Finite →
      ((S \ Θ).ncard + k : ℝ) ≤ L →
      ∫⁻ xs, ENNReal.ofReal (1 / 2) ^ (aggRun U S (List.ofFn xs) \ Θ).ncard ∂walkersLaw m a ≤
        ENNReal.ofReal (1 / 2) ^ (S \ Θ).ncard * ENNReal.ofReal (1 - s₂ / 2) ^ k
  | 0, a, S, _, _, _, _ => by
    have h0 : ∀ xs : Fin 0 → ℕ → ℤ, List.ofFn xs = [] := fun _ => List.ofFn_zero
    simp only [h0, aggRun_nil, pow_zero, mul_one, lintegral_const, measure_univ]
    exact le_rfl
  | k + 1, a, S, ha, hΘS, hfin, hL => by
    have hmeas : ∀ (j : ℕ) (S' : Set ℤ), Measurable fun xs : Fin j → ℕ → ℤ =>
        ENNReal.ofReal (1 / 2) ^ (aggRun U S' (List.ofFn xs) \ Θ).ncard :=
      fun j S' => measurable_from_nat.comp (measurable_aggRun_ncard U Θ S' j)
    refine (lintegral_walkersLaw_succ m a _ (hmeas _ _)).trans_le ?_
    simp only [ofFn_cons', aggRun_cons]
    push_cast at hL
    have hNk : ((S \ Θ).ncard : ℝ) + k ≤ L := by linarith
    have hinner : ∀ x : ℕ → ℤ, ∫⁻ ys, ENNReal.ofReal (1 / 2) ^ (aggRun U (aggStep U S x) (List.ofFn ys) \ Θ).ncard
        ∂walkersLaw m (fun i => a i.succ) ≤
        ENNReal.ofReal (1 / 2) ^ (S \ Θ).ncard * ENNReal.ofReal (1 - s₂ / 2) ^ k * absorbWeight U S x := by
      intro x
      by_cases hx : Absorbs U S x
      · obtain ⟨b, hbU, hb⟩ := hx
        have hbS : b ∉ S := not_mem_of_firstExitSite_eq_some hb
        have hstep : aggStep U S x = insert b S := by
          rw [aggStep_eq, hb]
          simp [nextAgg, hbU, Set.union_singleton]
        have hdiff : insert b S \ Θ = insert b (S \ Θ) := Set.insert_sdiff_of_notMem _ (fun h => hbS (hΘS h))
        have hcard : (insert b S \ Θ).ncard = (S \ Θ).ncard + 1 := by
          rw [hdiff]
          exact Set.ncard_insert_of_notMem (fun h => hbS h.1) hfin
        have ih := lintegral_half_pow_le m Θ U s₂ L habs k (fun i => a i.succ) (insert b S) (fun i => ha _)
          (hΘS.trans (subset_insert _ _)) (by rw [hdiff]; exact hfin.insert b)
          (by rw [hcard]; push_cast; linarith)
        rw [hstep, absorbWeight_of_absorbs ⟨b, hbU, hb⟩]
        refine ih.trans (le_of_eq ?_)
        rw [hcard, pow_succ]
        ring
      · have hstep : aggStep U S x = S := by
          rw [aggStep_eq]
          cases h : firstExitSite S x with
          | none => rfl
          | some b =>
            have hbU : b ∉ U := fun hbU => hx ⟨b, hbU, h⟩
            simp [nextAgg, hbU]
        have ih := lintegral_half_pow_le m Θ U s₂ L habs k (fun i => a i.succ) S (fun i => ha _) hΘS hfin hNk
        rw [hstep, absorbWeight_of_not_absorbs hx, mul_one]
        exact ih
    have hA := measurableSet_absorbs U S
    have hg : Measurable (absorbWeight U S) :=
      (measurable_const.indicator hA).add (measurable_const.indicator hA.compl)
    have hprob : ENNReal.ofReal s₂ ≤ srwLaw m (a 0) {x | Absorbs U S x} :=
      habs (a 0) (ha 0) S hΘS hfin (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have hint : ∫⁻ x, absorbWeight U S x ∂srwLaw m (a 0) ≤ ENNReal.ofReal (1 - s₂ / 2) := by
      unfold absorbWeight
      rw [lintegral_add_left (measurable_const.indicator hA), lintegral_indicator_const hA,
        lintegral_indicator_const hA.compl, one_mul, prob_compl_eq_one_sub hA]
      exact one_sub_add_half_le prob_le_one hprob
    calc ∫⁻ x, ∫⁻ ys, ENNReal.ofReal (1 / 2) ^ (aggRun U (aggStep U S x) (List.ofFn ys) \ Θ).ncard
          ∂walkersLaw m (fun i => a i.succ) ∂srwLaw m (a 0)
        ≤ ∫⁻ x, ENNReal.ofReal (1 / 2) ^ (S \ Θ).ncard * ENNReal.ofReal (1 - s₂ / 2) ^ k * absorbWeight U S x
          ∂srwLaw m (a 0) := lintegral_mono hinner
      _ = ENNReal.ofReal (1 / 2) ^ (S \ Θ).ncard * ENNReal.ofReal (1 - s₂ / 2) ^ k *
          ∫⁻ x, absorbWeight U S x ∂srwLaw m (a 0) := lintegral_const_mul _ hg
      _ ≤ ENNReal.ofReal (1 / 2) ^ (S \ Θ).ncard * ENNReal.ofReal (1 - s₂ / 2) ^ k *
          ENNReal.ofReal (1 - s₂ / 2) := by gcongr
      _ = ENNReal.ofReal (1 / 2) ^ (S \ Θ).ncard * ENNReal.ofReal (1 - s₂ / 2) ^ (k + 1) := by
          rw [pow_succ]; ring

/-! ### The step -/

theorem real_bound {s₂ : ℝ} (hs₂ : 0 < s₂) (hs₂1 : s₂ < 1) (k : ℕ) :
    (1 - s₂ / 2) ^ k / Real.exp (-(s₂ / 4 * k)) ≤ Real.exp (-(s₂ / 4) * k) := by
  rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
  have h1 : 1 - s₂ / 2 ≤ Real.exp (-(s₂ / 2)) := by linarith [Real.add_one_le_exp (-(s₂ / 2))]
  calc (1 - s₂ / 2) ^ k ≤ Real.exp (-(s₂ / 2)) ^ k := pow_le_pow_left₀ (by linarith) h1 k
    _ = Real.exp (-(s₂ / 4) * k + -(s₂ / 4 * k)) := by
        rw [← Real.exp_nat_mul]; congr 1; ring

theorem half_pow_ge {N : ℕ} {t : ℝ} (hN : (N : ℝ) ≤ t) :
    ENNReal.ofReal (Real.exp (-t)) ≤ ENNReal.ofReal (1 / 2) ^ N := by
  rw [← ENNReal.ofReal_pow (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  calc Real.exp (-t) ≤ Real.exp (-(N : ℝ)) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-1) ^ N := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ (1 / 2) ^ N := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le N

/-- **The Chernoff-type iteration of Lemma 6.9.** -/
theorem absorptionChernoffStep : AbsorptionChernoffStep := by
  intro m Θ U s₂ L hs₂ hs₂1 h k a hkL ha
  have habs : ∀ a ∈ vClosure m Θ, ∀ S : Set ℤ, Θ ⊆ S → (S \ Θ).Finite → ((S \ Θ).ncard : ℝ) < L →
      ENNReal.ofReal s₂ ≤ srwLaw m a {x | Absorbs U S x} := by
    intro a' ha' S _ hfin hlt
    refine (h a' ha' (S ∩ U) inter_subset_right ?_).trans (measure_mono ?_)
    · calc (((S ∩ U) \ Θ).ncard : ℝ) ≤ (S \ Θ).ncard := by
            exact_mod_cast Set.ncard_le_ncard (s := (S ∩ U) \ Θ) (t := S \ Θ)
              (fun y hy => ⟨hy.1.1, hy.2⟩) hfin
        _ < L := hlt
    · rintro x ⟨n, hn, hxU, hxS⟩
      exact absorbs_of_visit hn fun hS => hxS (Or.inl ⟨hS, hxU⟩)
  have hmom := lintegral_half_pow_le m Θ U s₂ L habs k a Θ ha subset_rfl (by simp) (by simpa using hkL)
  simp only [Set.sdiff_self, ncard_empty, pow_zero, one_mul] at hmom
  rw [← ENNReal.ofReal_pow (by linarith)] at hmom
  have hf : Measurable fun xs : Fin k → ℕ → ℤ => ENNReal.ofReal (1 / 2) ^ (aggRun U Θ (List.ofFn xs) \ Θ).ncard :=
    measurable_from_nat.comp (measurable_aggRun_ncard U Θ Θ k)
  have hthr0 : ENNReal.ofReal (Real.exp (-(s₂ / 4 * k))) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  calc walkersLaw m a {xs | ((idlaAggregate Θ U (List.ofFn xs) \ Θ).ncard : ℝ) ≤ s₂ / 4 * k}
      ≤ walkersLaw m a {xs | ENNReal.ofReal (Real.exp (-(s₂ / 4 * k))) ≤
          ENNReal.ofReal (1 / 2) ^ (aggRun U Θ (List.ofFn xs) \ Θ).ncard} :=
        measure_mono fun xs hxs => half_pow_ge hxs
    _ ≤ (∫⁻ xs, ENNReal.ofReal (1 / 2) ^ (aggRun U Θ (List.ofFn xs) \ Θ).ncard ∂walkersLaw m a) /
          ENNReal.ofReal (Real.exp (-(s₂ / 4 * k))) :=
        meas_ge_le_lintegral_div hf.aemeasurable hthr0 ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((1 - s₂ / 2) ^ k) / ENNReal.ofReal (Real.exp (-(s₂ / 4 * k))) := by gcongr
    _ = ENNReal.ofReal ((1 - s₂ / 2) ^ k / Real.exp (-(s₂ / 4 * k))) :=
        (ENNReal.ofReal_div_of_pos (Real.exp_pos _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(s₂ / 4) * k)) := ENNReal.ofReal_le_ofReal (real_bound hs₂ hs₂1 k)

end Absorption

/-- **Lemma 6.9** (local-rate reading) from Lemma 6.7. -/
theorem chanceOfBeingAbsorbedLocalRate (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundStmt 𝒮) :
    ChanceOfBeingAbsorbedLocalRateStmt 𝒮 :=
  chanceOfBeingAbsorbedLocalRate_of_steps 𝒮 h67 Absorption.absorptionChernoffStep

end MatedCRT
