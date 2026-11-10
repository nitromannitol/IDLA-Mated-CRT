import MatedCRT.FirstPass.S2i.FamilyCode

/-! # Measurable decoder and process code (FirstPass S2i, z2)

The space-time process of a family stopped at `T` is coded by its bits at the dense pairs `(posTime i, centre k)`
(`processCodeTimed`). This file proves that the decoder `decodeFamily` is jointly measurable in the code, that the process code
is a measurable function of the pair (horizon, process), and that the code of a stopped family is its process code
(`codeFamily_eq_processCode`). It also proves the deterministic congruence of LQG limits under equality of the circle
averages at positive radii (Duplantier-Sheffield, Berestycki-Powell). Used by the canonical factor
(`FirstPass/S2i/CanonicalFactor.lean`, notes/fp-gaps/CHATGPT-q1-open-steps.md Section 7). -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

open Classical in
/-- The process code at horizon `T`: the bits of the space-time process `p` at the dense pairs
`(posTime i, centre k)`, with the horizon `T` attached. For a family stopped at `T`,
`processCodeTimed T (familyProcess Λ T) = codeFamily T Λ` (`codeFamily_eq_processCode`). -/
noncomputable def processCodeTimed (T : ℝ) (p : ℝ × ℂ → Prop) : ℝ × (ℕ → ℕ → Bool) :=
  (T, fun i k => decide (p ((posTime i : ℝ), centre k)))

/-- The bit `y.2 i k` is a measurable event of the code. -/
theorem measurableSet_bit (i k : ℕ) :
    MeasurableSet {y : ℝ × (ℕ → ℕ → Bool) | y.2 i k = true} := by
  have h : Measurable fun y : ℝ × (ℕ → ℕ → Bool) => y.2 i k := by
    fun_prop
  exact h (measurableSet_singleton true)

/-- The closure test `CodeCl y t z` is a measurable event of the code. -/
theorem measurableSet_codeCl (t : ℝ) (z : ℂ) :
    MeasurableSet {y : ℝ × (ℕ → ℕ → Bool) | CodeCl y t z} := by
  have h : {y : ℝ × (ℕ → ℕ → Bool) | CodeCl y t z} =
      ⋂ n : ℕ, ⋃ k : ℕ, ({_y | dist (centre k) z < 1 / ((n : ℝ) + 1)} ∩
        ⋃ i : ℕ, ({_y | (posTime i : ℝ) < t} ∩ {y | y.2 i k = true})) := by
    ext y
    simp only [CodeCl, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
  rw [h]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
    (MeasurableSet.const _).inter (MeasurableSet.iUnion fun i =>
      (MeasurableSet.const _).inter (measurableSet_bit i k))

/-- For fixed `(t, z)`, the event `decodeFamily y (t, z)` is measurable in the code `y`. -/
theorem measurableSet_decodeFamily_coord (p : ℝ × ℂ) :
    MeasurableSet {y : ℝ × (ℕ → ℕ → Bool) | decodeFamily y p} := by
  have h : {y : ℝ × (ℕ → ℕ → Bool) | decodeFamily y p} =
      {_y | 0 < p.1} ∩ ({y | p.1 < y.1} ∩
        ⋃ m : ℕ, ⋂ k : ℕ, ({_y | ¬ dist (centre k) p.2 < 1 / ((m : ℝ) + 1)} ∪
          {y | CodeCl y p.1 (centre k)})) := by
    ext y
    simp only [decodeFamily, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, mem_union, imp_iff_not_or]
  rw [h]
  exact (MeasurableSet.const _).inter ((measurableSet_lt measurable_const measurable_fst).inter
    (MeasurableSet.iUnion fun m => MeasurableSet.iInter fun k =>
      (MeasurableSet.const _).union (measurableSet_codeCl _ _)))

/-- The decoder is a measurable map from the code space to the space-time processes (product σ-algebra on
`ℝ × ℂ → Prop`). -/
theorem measurable_decodeFamily : Measurable decodeFamily :=
  Measurable.of_eval fun p => measurableSet_setOfPred.1 (measurableSet_decodeFamily_coord p)

/-- The bit `y.2 i k` as an event of the pair (code, point). -/
theorem measurableSet_bit_uncurry (i k : ℕ) :
    MeasurableSet {q : (ℝ × (ℕ → ℕ → Bool)) × (ℝ × ℂ) | q.1.2 i k = true} :=
  (measurableSet_bit i k).preimage measurable_fst

/-- The closure test `CodeCl y t z` as an event of the triple (code, time, point), jointly. -/
theorem measurableSet_codeCl_uncurry :
    MeasurableSet {q : (ℝ × (ℕ → ℕ → Bool)) × ℝ × ℂ | CodeCl q.1 q.2.1 q.2.2} := by
  have h : {q : (ℝ × (ℕ → ℕ → Bool)) × ℝ × ℂ | CodeCl q.1 q.2.1 q.2.2} =
      ⋂ n : ℕ, ⋃ k : ℕ, ({q | dist (centre k) q.2.2 < 1 / ((n : ℝ) + 1)} ∩
        ⋃ i : ℕ, ({q | (posTime i : ℝ) < q.2.1} ∩ {q | q.1.2 i k = true})) := by
    ext q
    simp only [CodeCl, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
  rw [h]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k => ?_
  refine MeasurableSet.inter ?_ (MeasurableSet.iUnion fun i => MeasurableSet.inter ?_ (measurableSet_bit_uncurry i k))
  · exact measurableSet_lt (by fun_prop) measurable_const
  · exact measurableSet_lt measurable_const (by fun_prop)

/-- **The decoder is jointly measurable in the code and the space-time point**: the set of `(y, (t, z))` with
`decodeFamily y (t, z)` is measurable. Used for the measurability of the glued global family (FirstPass S2i). -/
theorem measurableSet_decodeFamily_uncurry :
    MeasurableSet {q : (ℝ × (ℕ → ℕ → Bool)) × (ℝ × ℂ) | decodeFamily q.1 q.2} := by
  have h : {q : (ℝ × (ℕ → ℕ → Bool)) × (ℝ × ℂ) | decodeFamily q.1 q.2} =
      {q | 0 < q.2.1} ∩ ({q | q.2.1 < q.1.1} ∩
        ⋃ m : ℕ, ⋂ k : ℕ, ({q | ¬ dist (centre k) q.2.2 < 1 / ((m : ℝ) + 1)} ∪
          {q | CodeCl q.1 q.2.1 (centre k)})) := by
    ext q
    simp only [decodeFamily, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, mem_union, imp_iff_not_or]
  rw [h]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_lt measurable_const (by fun_prop)
  · exact measurableSet_lt (by fun_prop) (by fun_prop)
  · refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun k => MeasurableSet.union ?_ ?_
    · have hd : Measurable fun q : (ℝ × (ℕ → ℕ → Bool)) × (ℝ × ℂ) => dist (centre k) q.2.2 := by
        fun_prop
      exact (measurableSet_lt hd measurable_const).compl
    · exact measurableSet_codeCl_uncurry.preimage
        (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk measurable_const))

/-- The decoder as a jointly measurable map of (code, point). -/
theorem measurable_decodeFamily_uncurry :
    Measurable fun q : (ℝ × (ℕ → ℕ → Bool)) × (ℝ × ℂ) => decodeFamily q.1 q.2 :=
  measurableSet_setOfPred.1 measurableSet_decodeFamily_uncurry

/-- The process code is jointly measurable in the horizon and the process. -/
theorem measurable_processCodeTimed :
    Measurable fun q : ℝ × (ℝ × ℂ → Prop) => processCodeTimed q.1 q.2 := by
  refine Measurable.prodMk measurable_fst ?_
  refine Measurable.of_eval fun i => Measurable.of_eval fun k => ?_
  have hp : Measurable fun q : ℝ × (ℝ × ℂ → Prop) => q.2 ((posTime i : ℝ), centre k) :=
    (measurable_pi_apply _).comp measurable_snd
  open Classical in
  have hd : Measurable (fun P : Prop => decide P) := measurable_from_top
  exact hd.comp hp

/-- The code of a family stopped at `T` is the process code of its space-time process (the dense pairs with
`posTime i > 0` are exactly the pairs with `posTime i ∈ (0, T)` once `posTime i < T`). -/
theorem codeFamily_eq_processCode (T : ℝ) (Λ : ℝ → Set ℂ) :
    codeFamily T Λ = processCodeTimed T (familyProcess Λ T) := by
  unfold codeFamily processCodeTimed
  congr 1
  funext i k
  apply decide_eq_decide.2
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨(posTime i).2, h1⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, h2⟩

/-- **Congruence of LQG limits.** The LQG limit `m` of an average process `hε` is the same for any `hε'` agreeing with
`hε` at positive radii: `IsLQGLimit` only uses the dyadic scales `2^{-k}`. -/
theorem isLQGLimit_congr {γ : ℝ} {h h' : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hh : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, h ε z = h' ε z) (hm : IsLQGLimit γ h m) : IsLQGLimit γ h' m := by
  have hA : ∀ k : ℕ, lqgApprox γ h (dyadicScale k) = lqgApprox γ h' (dyadicScale k) := by
    intro k
    have hpos : 0 < dyadicScale k := by unfold dyadicScale; positivity
    unfold lqgApprox
    simp only [hh _ hpos]
  exact ⟨hm.isLocallyFiniteMeasure, fun f hf hc => by
    simpa only [hA] using hm.tendsto_integral f hf hc⟩

end MatedCRT
