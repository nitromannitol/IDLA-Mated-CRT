import MatedCRT.Proofs.Sec4.ConvergenceDivisible.OdometerSelectionMeasurable

/-! # The position-indexed selection of `OdometerMeasurableSelectionStep`: definitions and measurability

Given measurable proxy events `G p i n q` (`OdometerSelectionProxy`), the selection of GAPS 2026-11-06 is
defined by least-index recursions (`leastOr`):
* `selPair`: the least pair `p` whose proxy events satisfy the criterion `critSet`;
* `posSeq s`: positions `n_s` with `n_{s+1} > n_s` and the stage-`s` event at `n_s`;
* `inTSet k`: the stage-`k` positions `T_k`, nested, cut by the pigeonhole index `idxSel`;
* `stageSp k`: the diagonal positions `s_k` in `T_k`, strictly increasing, and `selSeq k = n_{s_k}`.
All objects are measurable for the σ-algebra `M` (the envSigma of the environment). -/

namespace MatedCRT

open MeasureTheory Set

section Countable

variable {Ω : Type} (M : MeasurableSpace Ω)

/-- Sets of the form `{ω | ω ∈ E (g ω)}` with a measurable countable-valued `g`. -/
lemma measurableSet_comp_countable {β : Type} [Countable β] [MeasurableSpace β]
    [MeasurableSingletonClass β] {g : Ω → β} (hg : Measurable[M] g) {E : β → Set Ω}
    (hE : ∀ b, MeasurableSet[M] (E b)) : MeasurableSet[M] {ω | ω ∈ E (g ω)} := by
  have heq : {ω | ω ∈ E (g ω)} = ⋃ b : β, {ω | g ω = b} ∩ E b := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨g ω, rfl, h⟩
    · rintro ⟨b, hb, h⟩
      rw [hb]
      exact h
  rw [heq]
  exact MeasurableSet.iUnion fun b => (hg (measurableSet_singleton b)).inter (hE b)

/-- A set-valued predicate on the value of a countable-valued measurable map. -/
lemma measurableSet_comp_prop {β : Type} [Countable β] [MeasurableSpace β]
    [MeasurableSingletonClass β] {g : Ω → β} (hg : Measurable[M] g) (Q : β → Prop) :
    MeasurableSet[M] {ω | Q (g ω)} :=
  hg (Set.to_countable {b | Q b}).measurableSet

end Countable

section Recursion

variable {Ω : Type} (M : MeasurableSpace Ω)

/-- The events of the criterion: for the pair `p`, infinitely many positions `n` with proxy events. -/
def critSet (G : ℕ → ℕ → ℕ → ℕ → Set Ω) (p : ℕ) : Set Ω :=
  ⋂ q : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ _ : N ≤ n, ⋃ i : ℕ, G p i n q

/-- The least pair whose criterion holds (default `0`). -/
noncomputable def selPair (G : ℕ → ℕ → ℕ → ℕ → Set Ω) : Ω → ℕ :=
  leastOr fun ω p => ω ∈ critSet G p

/-- The positions `n_s` (stage `s`), with `n_{s+1}` the least index above `n_s` carrying the stage-`s+1` event. -/
noncomputable def posSeq (G : ℕ → ℕ → ℕ → ℕ → Set Ω) (Pst : Ω → ℕ) : ℕ → Ω → ℕ
  | 0 => fun ω => leastOr (fun ω' n => ∃ i, ω' ∈ G (Pst ω') i n 0) ω
  | s + 1 => fun ω => leastOr (fun ω' n => posSeq G Pst s ω' < n ∧ ∃ i, ω' ∈ G (Pst ω') i n (s + 1)) ω

/-- The pigeonhole index of stage `k + 1`: the least net index `i` for which the stage-`k` positions
within `(1/2)^k` of `cen i` are infinite. -/
noncomputable def idxSel (G : ℕ → ℕ → ℕ → ℕ → Set Ω) (Pst : Ω → ℕ) (NetN : ℕ → ℕ → Finset ℕ)
    (T : Ω → ℕ → Prop) (k : ℕ) : Ω → ℕ :=
  leastOr fun ω' i => i ∈ NetN (Pst ω') (k + 1) ∧
    {s | T ω' s ∧ k + 1 ≤ s ∧ ω' ∈ G (Pst ω') i (posSeq G Pst s ω') k}.Infinite

/-- The stage-`k` positions `T_k`, nested in `k`. -/
noncomputable def inTSet (G : ℕ → ℕ → ℕ → ℕ → Set Ω) (Pst : Ω → ℕ) (NetN : ℕ → ℕ → Finset ℕ) :
    ℕ → Ω → ℕ → Prop
  | 0 => fun _ _ => True
  | k + 1 => fun ω s => inTSet G Pst NetN k ω s ∧ k + 1 ≤ s ∧
      ω ∈ G (Pst ω) (idxSel G Pst NetN (inTSet G Pst NetN k) k ω) (posSeq G Pst s ω) k

/-- The diagonal positions `s_k`: strictly increasing, with `s_k ∈ T_k`. -/
noncomputable def stageSp (G : ℕ → ℕ → ℕ → ℕ → Set Ω) (Pst : Ω → ℕ) (NetN : ℕ → ℕ → Finset ℕ) :
    ℕ → Ω → ℕ
  | 0 => fun _ => 0
  | k + 1 => leastOr fun ω s => stageSp G Pst NetN k ω < s ∧ inTSet G Pst NetN (k + 1) ω s

/-- The selected subsequence `k ↦ n_{s_k}`. -/
noncomputable def selSeq (G : ℕ → ℕ → ℕ → ℕ → Set Ω) (Pst : Ω → ℕ) (NetN : ℕ → ℕ → Finset ℕ) (k : ℕ)
    (ω : Ω) : ℕ :=
  posSeq G Pst (stageSp G Pst NetN k ω) ω

variable {M}

lemma measurable_selPair {G : ℕ → ℕ → ℕ → ℕ → Set Ω}
    (hG : ∀ p i n q, MeasurableSet[M] (G p i n q)) : Measurable[M] (selPair G) := by
  unfold selPair
  refine measurable_leastOr M _ fun p => ?_
  have hc : MeasurableSet[M] (critSet G p) :=
    MeasurableSet.iInter fun q => MeasurableSet.iInter fun N =>
      MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
        MeasurableSet.iUnion fun i => hG p i n q
  exact hc

lemma measurable_posSeq {G : ℕ → ℕ → ℕ → ℕ → Set Ω} {Pst : Ω → ℕ} (hPst : Measurable[M] Pst)
    (hG : ∀ p i n q, MeasurableSet[M] (G p i n q)) :
    ∀ s, Measurable[M] (posSeq G Pst s) := by
  intro s
  induction s with
  | zero =>
    refine measurable_leastOr M _ fun n => ?_
    have heq : {ω | ∃ i, ω ∈ G (Pst ω) i n 0} = ⋃ i, {ω | ω ∈ G (Pst ω) i n 0} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun i =>
      measurableSet_comp_countable M hPst fun p => hG p i n 0
  | succ s ih =>
    refine measurable_leastOr M _ fun n => ?_
    have heq : {ω | posSeq G Pst s ω < n ∧ ∃ i, ω ∈ G (Pst ω) i n (s + 1)} =
        {ω | posSeq G Pst s ω < n} ∩ ⋃ i, {ω | ω ∈ G (Pst ω) i n (s + 1)} := by
      ext ω
      simp
    rw [heq]
    refine (measurableSet_lt ih measurable_const).inter (MeasurableSet.iUnion fun i => ?_)
    exact measurableSet_comp_countable M hPst fun p => hG p i n (s + 1)

/-- The pigeonhole index is measurable when the stage sets are. -/
lemma measurable_idxSel {G : ℕ → ℕ → ℕ → ℕ → Set Ω} {Pst : Ω → ℕ} (hPst : Measurable[M] Pst)
    {NetN : ℕ → ℕ → Finset ℕ} (hG : ∀ p i n q, MeasurableSet[M] (G p i n q))
    (hpos : ∀ s, Measurable[M] (posSeq G Pst s)) {T : Ω → ℕ → Prop}
    (hT : ∀ s, MeasurableSet[M] {ω | T ω s}) (k : ℕ) :
    Measurable[M] (idxSel G Pst NetN T k) := by
  unfold idxSel
  refine measurable_leastOr M _ fun i => ?_
  have hN : MeasurableSet[M] {ω | i ∈ NetN (Pst ω) (k + 1)} :=
    measurableSet_comp_prop M hPst (fun p => i ∈ NetN p (k + 1))
  have hinf : MeasurableSet[M] {ω | {s | T ω s ∧ k + 1 ≤ s ∧
      ω ∈ G (Pst ω) i (posSeq G Pst s ω) k}.Infinite} := by
    refine measurableSet_infinite_nat M _ fun s => ?_
    refine (hT s).inter ((MeasurableSet.const (k + 1 ≤ s)).inter ?_)
    exact measurableSet_comp_countable M (hPst.prodMk (hpos s)) fun b => hG b.1 i b.2 k
  exact hN.inter hinf

/-- The stage-`k` positions are measurable, for every stage and position. -/
lemma measurableSet_inTSet {G : ℕ → ℕ → ℕ → ℕ → Set Ω} {Pst : Ω → ℕ} (hPst : Measurable[M] Pst)
    {NetN : ℕ → ℕ → Finset ℕ} (hG : ∀ p i n q, MeasurableSet[M] (G p i n q)) (k : ℕ) :
    ∀ s, MeasurableSet[M] {ω | inTSet G Pst NetN k ω s} := by
  induction k with
  | zero =>
    intro s
    have heq : {ω | inTSet G Pst NetN 0 ω s} = univ := Set.ext fun ω => Iff.rfl
    rw [heq]
    exact MeasurableSet.univ
  | succ k ih =>
    intro s
    have hpos := measurable_posSeq hPst hG
    have hidx := measurable_idxSel (NetN := NetN) (T := inTSet G Pst NetN k) hPst hG hpos ih k
    have heq : {ω | inTSet G Pst NetN (k + 1) ω s} = {ω | inTSet G Pst NetN k ω s} ∩
        ({ω | k + 1 ≤ s} ∩
          {ω | ω ∈ G (Pst ω) (idxSel G Pst NetN (inTSet G Pst NetN k) k ω) (posSeq G Pst s ω) k}) :=
      Set.ext fun ω => Iff.rfl
    rw [heq]
    refine (ih s).inter ((MeasurableSet.const (k + 1 ≤ s)).inter ?_)
    exact measurableSet_comp_countable M (hPst.prodMk (hidx.prodMk (hpos s)))
      fun b => hG b.1 b.2.1 b.2.2 k

/-- The diagonal positions `s_k` are measurable. -/
lemma measurable_stageSp {G : ℕ → ℕ → ℕ → ℕ → Set Ω} {Pst : Ω → ℕ} {NetN : ℕ → ℕ → Finset ℕ}
    (hPst : Measurable[M] Pst) (hG : ∀ p i n q, MeasurableSet[M] (G p i n q)) (k : ℕ) :
    Measurable[M] (stageSp G Pst NetN k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    show Measurable[M] (leastOr fun ω s => stageSp G Pst NetN k ω < s ∧
      inTSet G Pst NetN (k + 1) ω s)
    refine measurable_leastOr M _ fun s => ?_
    exact (measurableSet_lt ih measurable_const).inter (measurableSet_inTSet hPst hG (k + 1) s)

/-- The selected subsequence `k ↦ n_{s_k}` is measurable for each `k`. -/
lemma measurable_selSeq {G : ℕ → ℕ → ℕ → ℕ → Set Ω} {Pst : Ω → ℕ} {NetN : ℕ → ℕ → Finset ℕ}
    (hPst : Measurable[M] Pst) (hG : ∀ p i n q, MeasurableSet[M] (G p i n q)) (k : ℕ) :
    Measurable[M] (selSeq G Pst NetN k) :=
  measurable_comp_nat M (measurable_stageSp (NetN := NetN) hPst hG k) (measurable_posSeq hPst hG)

end Recursion

end MatedCRT
