import MatedCRT.Proofs.Sec4.ConvergenceDivisible.OdometerSelectionRecursion

/-! # The deterministic stage argument of the measurable selection (fixed sample point)

At a fixed `ω` the recursion of `OdometerSelectionRecursion` is a combinatorial construction. Assume the
proxies agree with the truth at `ω` (`hag`: `ω ∈ G p i n q` iff the rescaled function is within `(1/2)^q`
of `cen p i` on `K`), and that `ω` satisfies the criterion of the chosen pair (`hcrit`).
* the positions `n_s` are strictly increasing and carry the stage-`s` event (`posSeq_strictMono`, `pos_mem`);
* the stage sets `T_k` are nested and infinite (`inT_infinite`, the pigeonhole over the finite net);
* the diagonal positions `s_k` are strictly increasing with `s_k ∈ T_k` (`stage_succ_spec`);
* the selected subsequence is strictly increasing with uniform Cauchy bound `2 (1/2)^k` on `K` for indices `≥ k+1`
  (`selSeq_strictMono`, `selSeq_cauchy`). -/

namespace MatedCRT

open MeasureTheory Set Filter Topology

/-- Static data of the selection: the enumerated classes, their nets and the proxy events. -/
structure SelStatic (Ω : Type) where
  K : Set ℂ
  cls : ℕ → (ℂ → ℝ) → Prop
  cen : ℕ → ℕ → ℂ → ℝ
  NetN : ℕ → ℕ → Finset ℕ
  G : ℕ → ℕ → ℕ → ℕ → Set Ω
  Pst : Ω → ℕ
  hcls : ∀ p i, cls p (cen p i)
  hnet : ∀ p k h, cls p h → ∃ i ∈ NetN p k, ∀ x ∈ K, |h x - cen p i x| < (1 / 2 : ℝ) ^ k

namespace SelStatic

variable {Ω : Type} (D : SelStatic Ω)

lemma crit_mem {ω : Ω} (hcrit : ω ∈ critSet D.G (D.Pst ω)) (q N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ i, ω ∈ D.G (D.Pst ω) i n q := by
  simp only [critSet, Set.mem_iInter, Set.mem_iUnion] at hcrit
  obtain ⟨n, hn, i, hi⟩ := hcrit q N
  exact ⟨n, hn, i, hi⟩

lemma pos_spec_zero {ω : Ω} (hcrit : ω ∈ critSet D.G (D.Pst ω)) :
    ∃ i, ω ∈ D.G (D.Pst ω) i (posSeq D.G D.Pst 0 ω) 0 := by
  obtain ⟨n0, -, i0, hi0⟩ := crit_mem D hcrit 0 0
  have h := leastOr_spec (fun ω' n => ∃ i, ω' ∈ D.G (D.Pst ω') i n 0) ω ⟨n0, i0, hi0⟩
  exact h.1

lemma pos_spec_succ {ω : Ω} (hcrit : ω ∈ critSet D.G (D.Pst ω)) (s : ℕ) :
    posSeq D.G D.Pst s ω < posSeq D.G D.Pst (s + 1) ω ∧
      ∃ i, ω ∈ D.G (D.Pst ω) i (posSeq D.G D.Pst (s + 1) ω) (s + 1) := by
  obtain ⟨n0, hn0, i0, hi0⟩ := crit_mem D hcrit (s + 1) (posSeq D.G D.Pst s ω + 1)
  have h := leastOr_spec (fun ω' n => posSeq D.G D.Pst s ω' < n ∧
    ∃ i, ω' ∈ D.G (D.Pst ω') i n (s + 1)) ω ⟨n0, by omega, i0, hi0⟩
  exact h.1

lemma pos_mem {ω : Ω} (hcrit : ω ∈ critSet D.G (D.Pst ω)) (s : ℕ) :
    ∃ i, ω ∈ D.G (D.Pst ω) i (posSeq D.G D.Pst s ω) s := by
  cases s with
  | zero => exact pos_spec_zero D hcrit
  | succ s => exact (pos_spec_succ D hcrit s).2

lemma posSeq_strictMono {ω : Ω} (hcrit : ω ∈ critSet D.G (D.Pst ω)) :
    StrictMono (fun s => posSeq D.G D.Pst s ω) :=
  strictMono_nat_of_lt_succ fun s => (pos_spec_succ D hcrit s).1

lemma inT_anti (k : ℕ) {ω : Ω} : ∀ d s, inTSet D.G D.Pst D.NetN (k + d) ω s →
    inTSet D.G D.Pst D.NetN k ω s := by
  intro d
  induction d with
  | zero => intro s h; exact h
  | succ d ih => intro s h; exact ih s h.1

lemma inT_anti_le {ω : Ω} {k ℓ : ℕ} (hkℓ : k ≤ ℓ) {s : ℕ}
    (h : inTSet D.G D.Pst D.NetN ℓ ω s) : inTSet D.G D.Pst D.NetN k ω s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkℓ
  exact inT_anti D k d s h

/-- The stage-`k` positions are infinite, by the pigeonhole over the finite net at each stage. -/
lemma inT_infinite (F : ℕ → Ω → ℂ → ℝ) {ω : Ω}
    (hag : ∀ p i n q, ω ∈ D.G p i n q ↔ ∀ x ∈ D.K, |F n ω x - D.cen p i x| ≤ (1 / 2 : ℝ) ^ q)
    (hcrit : ω ∈ critSet D.G (D.Pst ω)) (k : ℕ) :
    {s | inTSet D.G D.Pst D.NetN k ω s}.Infinite := by
  induction k with
  | zero =>
    have h0 : {s | inTSet D.G D.Pst D.NetN 0 ω s} = univ := Set.ext fun s => Iff.rfl
    rw [h0]
    exact Set.infinite_univ
  | succ k ih =>
    have hT' : {s | inTSet D.G D.Pst D.NetN k ω s ∧ k + 1 ≤ s}.Infinite :=
      Set.Infinite.mono (fun s hs => ⟨hs.1, not_lt.1 hs.2⟩) (ih.sdiff (Set.finite_Iio (k + 1)))
    -- every position of `T'` lies in the net-indexed set of some centre within `(1/2)^k`
    have hcover : ∀ s, (inTSet D.G D.Pst D.NetN k ω s ∧ k + 1 ≤ s) →
        ∃ i ∈ D.NetN (D.Pst ω) (k + 1), ω ∈ D.G (D.Pst ω) i (posSeq D.G D.Pst s ω) k := by
      intro s hs
      obtain ⟨i', hi'⟩ := pos_mem D hcrit s
      have htr := (hag _ _ _ _).1 hi'
      obtain ⟨i, hiN, hi⟩ := D.hnet (D.Pst ω) (k + 1) (D.cen (D.Pst ω) i') (D.hcls _ _)
      refine ⟨i, hiN, (hag _ _ _ _).2 fun x hx => ?_⟩
      have h1 := htr x hx
      have h2 := (hi x hx).le
      have hpow : (1 / 2 : ℝ) ^ s ≤ (1 / 2 : ℝ) ^ (k + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hs.2
      have hsum : (1 / 2 : ℝ) ^ (k + 1) + (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k := by ring
      have htri := abs_sub_le (F (posSeq D.G D.Pst s ω) ω x) (D.cen (D.Pst ω) i' x)
        (D.cen (D.Pst ω) i x)
      linarith
    have hex : ∃ i ∈ D.NetN (D.Pst ω) (k + 1),
        {s | inTSet D.G D.Pst D.NetN k ω s ∧ k + 1 ≤ s ∧
          ω ∈ D.G (D.Pst ω) i (posSeq D.G D.Pst s ω) k}.Infinite := by
      by_contra hcon
      have hfin : ∀ i ∈ D.NetN (D.Pst ω) (k + 1),
          {s | inTSet D.G D.Pst D.NetN k ω s ∧ k + 1 ≤ s ∧
            ω ∈ D.G (D.Pst ω) i (posSeq D.G D.Pst s ω) k}.Finite :=
        fun i hi => Set.not_infinite.1 fun h => hcon ⟨i, hi, h⟩
      apply hT'
      refine (Set.Finite.biUnion (Finset.finite_toSet _) hfin).subset ?_
      intro s hs
      obtain ⟨i, hi, hmem⟩ := hcover s hs
      exact Set.mem_iUnion₂.2 ⟨i, hi, hs.1, hs.2, hmem⟩
    obtain ⟨i0, hi0N, hi0⟩ := hex
    have hsp := leastOr_spec (fun ω' i => i ∈ D.NetN (D.Pst ω') (k + 1) ∧
      {s | inTSet D.G D.Pst D.NetN k ω' s ∧ k + 1 ≤ s ∧
        ω' ∈ D.G (D.Pst ω') i (posSeq D.G D.Pst s ω') k}.Infinite) ω ⟨i0, hi0N, hi0⟩
    have heq : {s | inTSet D.G D.Pst D.NetN (k + 1) ω s} =
        {s | inTSet D.G D.Pst D.NetN k ω s ∧ k + 1 ≤ s ∧
          ω ∈ D.G (D.Pst ω) (idxSel D.G D.Pst D.NetN (inTSet D.G D.Pst D.NetN k) k ω)
            (posSeq D.G D.Pst s ω) k} :=
      Set.ext fun s => Iff.rfl
    rw [heq]
    exact hsp.1.2

/-- The diagonal positions: `s_k < s_{k+1}` and `s_{k+1} ∈ T_{k+1}`. -/
lemma stage_succ_spec (F : ℕ → Ω → ℂ → ℝ) {ω : Ω}
    (hag : ∀ p i n q, ω ∈ D.G p i n q ↔ ∀ x ∈ D.K, |F n ω x - D.cen p i x| ≤ (1 / 2 : ℝ) ^ q)
    (hcrit : ω ∈ critSet D.G (D.Pst ω)) (k : ℕ) :
    stageSp D.G D.Pst D.NetN k ω < stageSp D.G D.Pst D.NetN (k + 1) ω ∧
      inTSet D.G D.Pst D.NetN (k + 1) ω (stageSp D.G D.Pst D.NetN (k + 1) ω) := by
  obtain ⟨s0, hs0, hlt⟩ :=
    (inT_infinite D F hag hcrit (k + 1)).exists_gt (stageSp D.G D.Pst D.NetN k ω)
  exact (leastOr_spec (fun ω' s => stageSp D.G D.Pst D.NetN k ω' < s ∧
    inTSet D.G D.Pst D.NetN (k + 1) ω' s) ω ⟨s0, hlt, hs0⟩).1

lemma stage_mem (F : ℕ → Ω → ℂ → ℝ) {ω : Ω}
    (hag : ∀ p i n q, ω ∈ D.G p i n q ↔ ∀ x ∈ D.K, |F n ω x - D.cen p i x| ≤ (1 / 2 : ℝ) ^ q)
    (hcrit : ω ∈ critSet D.G (D.Pst ω)) (ℓ : ℕ) :
    inTSet D.G D.Pst D.NetN ℓ ω (stageSp D.G D.Pst D.NetN ℓ ω) := by
  cases ℓ with
  | zero => trivial
  | succ ℓ => exact (stage_succ_spec D F hag hcrit ℓ).2

/-- The truth at the stage `k+1` positions: within `(1/2)^k` of the stage-`k+1` centre on `K`. -/
lemma inT_succ_truth (F : ℕ → Ω → ℂ → ℝ) {ω : Ω}
    (hag : ∀ p i n q, ω ∈ D.G p i n q ↔ ∀ x ∈ D.K, |F n ω x - D.cen p i x| ≤ (1 / 2 : ℝ) ^ q)
    (k s : ℕ) (h : inTSet D.G D.Pst D.NetN (k + 1) ω s) :
    ∀ x ∈ D.K, |F (posSeq D.G D.Pst s ω) ω x -
      D.cen (D.Pst ω) (idxSel D.G D.Pst D.NetN (inTSet D.G D.Pst D.NetN k) k ω) x| ≤ (1 / 2 : ℝ) ^ k :=
  (hag _ _ _ _).1 h.2.2

/-- The selected subsequence is strictly increasing. -/
lemma selSeq_strictMono {ω : Ω} (F : ℕ → Ω → ℂ → ℝ)
    (hag : ∀ p i n q, ω ∈ D.G p i n q ↔ ∀ x ∈ D.K, |F n ω x - D.cen p i x| ≤ (1 / 2 : ℝ) ^ q)
    (hcrit : ω ∈ critSet D.G (D.Pst ω)) :
    StrictMono (fun k => selSeq D.G D.Pst D.NetN k ω) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  exact posSeq_strictMono D hcrit (stage_succ_spec D F hag hcrit k).1

/-- Uniform Cauchy bound on `K` for the selected subsequence, indices at least `k+1`. -/
lemma selSeq_cauchy {ω : Ω} (F : ℕ → Ω → ℂ → ℝ)
    (hag : ∀ p i n q, ω ∈ D.G p i n q ↔ ∀ x ∈ D.K, |F n ω x - D.cen p i x| ≤ (1 / 2 : ℝ) ^ q)
    (hcrit : ω ∈ critSet D.G (D.Pst ω)) (k ℓ ℓ' : ℕ) (hℓ : k + 1 ≤ ℓ) (hℓ' : k + 1 ≤ ℓ')
    {x : ℂ} (hx : x ∈ D.K) :
    |F (selSeq D.G D.Pst D.NetN ℓ ω) ω x - F (selSeq D.G D.Pst D.NetN ℓ' ω) ω x| ≤
      2 * (1 / 2 : ℝ) ^ k := by
  have h1 := inT_succ_truth D F hag k _ (inT_anti_le D hℓ (stage_mem D F hag hcrit ℓ)) x hx
  have h2 := inT_succ_truth D F hag k _ (inT_anti_le D hℓ' (stage_mem D F hag hcrit ℓ')) x hx
  unfold selSeq
  set c := D.cen (D.Pst ω) (idxSel D.G D.Pst D.NetN (inTSet D.G D.Pst D.NetN k) k ω) with hc
  have h3 := abs_sub_le (F (posSeq D.G D.Pst (stageSp D.G D.Pst D.NetN ℓ ω) ω) ω x) (c x)
    (F (posSeq D.G D.Pst (stageSp D.G D.Pst D.NetN ℓ' ω) ω) ω x)
  have h4 : |c x - F (posSeq D.G D.Pst (stageSp D.G D.Pst D.NetN ℓ' ω) ω) ω x| =
      |F (posSeq D.G D.Pst (stageSp D.G D.Pst D.NetN ℓ' ω) ω) ω x - c x| := abs_sub_comm _ _
  linarith

end SelStatic

end MatedCRT
