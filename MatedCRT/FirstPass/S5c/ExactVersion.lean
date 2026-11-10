import MatedCRT.FirstPass.S5c.ThresholdField

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), measure layer, step M3): exact measurable versions from thresholds

Generic, no frozen input. Let `v : Ω → ℝ` and, for each rational `c`, let `E c` be `m`-measurable with
`ω ∈ E c ↔ c < v ω` almost surely (for every rational `c` simultaneously, by countability). Then the rational supremum
`ratSup E ω = sSup {c ∈ ℚ | ω ∈ E c}` (value `0` off the set where the family is nonempty and bounded above) is an exact
`m`-measurable function equal to `v` almost surely. Monotonicity of the family is not needed: `lt_csSup_iff` gives
`{a < ratSup E} = Good ∩ ⋃ (c ∈ ℚ, a < c), E c` on the good set, which is exact.

Here `m` is the field σ-algebra when this is applied to `threshold_field_borel` (ThresholdField.lean).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Filter

/-- The rational supremum of a countable family of sets: `sSup {c : ℚ | ω ∈ E c}` (in `ℝ`). -/
noncomputable def ratSup {Ω : Type*} (E : ℚ → Set Ω) (ω : Ω) : ℝ :=
  sSup ((fun c : ℚ => (c : ℝ)) '' {c : ℚ | ω ∈ E c})

/-- Pointwise: if `E` is exactly the rational threshold family of `v` at `ω`, then `ratSup E ω = v ω`. -/
theorem ratSup_eq_of_thresholds {Ω : Type*} {E : ℚ → Set Ω} {v : Ω → ℝ} {ω : Ω}
    (h : ∀ c : ℚ, ω ∈ E c ↔ (c : ℝ) < v ω) : ratSup E ω = v ω := by
  unfold ratSup
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_
  · obtain ⟨q, hq⟩ := exists_rat_lt (v ω)
    exact ⟨(q : ℝ), q, (h q).2 hq, rfl⟩
  · rintro x ⟨c, hc, rfl⟩
    exact ((h c).1 hc).le
  · intro w hw
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hw
    exact ⟨(q : ℝ), ⟨q, (h q).2 hq2, rfl⟩, hq1⟩

/-- Off the good set (the family is empty or unbounded above), `ratSup` vanishes. -/
theorem ratSup_of_not_good {Ω : Type*} {E : ℚ → Set Ω} {ω : Ω}
    (h : ¬ ((∃ c : ℚ, ω ∈ E c) ∧ ∃ M : ℚ, ∀ c : ℚ, ω ∈ E c → c ≤ M)) : ratSup E ω = 0 := by
  unfold ratSup
  by_cases hne : ∃ c : ℚ, ω ∈ E c
  · have hunb : ¬ BddAbove ((fun c : ℚ => (c : ℝ)) '' {c : ℚ | ω ∈ E c}) := by
      rintro ⟨B, hB⟩
      obtain ⟨M, hM⟩ := exists_rat_gt B
      apply h
      refine ⟨hne, M, fun c hc => ?_⟩
      have h1 : (c : ℝ) ≤ B := hB ⟨c, hc, rfl⟩
      exact_mod_cast (show (c : ℝ) ≤ (M : ℝ) from h1.trans hM.le)
    exact Real.sSup_of_not_bddAbove hunb
  · have hempty : (fun c : ℚ => (c : ℝ)) '' {c : ℚ | ω ∈ E c} = ∅ := by
      ext x
      simp only [mem_image, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨c, hc, -⟩
      exact hne ⟨c, hc⟩
    rw [hempty, Real.sSup_empty]

/-- The rational supremum is exact `m`-measurable: `{a < ratSup E}` is a countable union of the sets `E c` on the good set. -/
theorem measurableSet_ratSup_lt {Ω : Type*} {m : MeasurableSpace Ω} {E : ℚ → Set Ω}
    (hE : ∀ c : ℚ, MeasurableSet[m] (E c)) (a : ℝ) :
    MeasurableSet[m] {ω | a < ratSup E ω} := by
  set Good : Set Ω := (⋃ c : ℚ, E c) ∩ ⋃ M : ℚ, ⋂ c : ℚ, {ω | ω ∈ E c → c ≤ M} with hGood
  have himp : ∀ c M : ℚ, MeasurableSet[m] {ω | ω ∈ E c → c ≤ M} := by
    intro c M
    by_cases h : c ≤ M
    · have : {ω | ω ∈ E c → c ≤ M} = Set.univ := by
        ext ω
        simp [h]
      rw [this]
      exact MeasurableSet.univ
    · have : {ω | ω ∈ E c → c ≤ M} = (E c)ᶜ := by
        ext ω
        simp [h]
      rw [this]
      exact (hE c).compl
  have hGm : MeasurableSet[m] Good := by
    refine MeasurableSet.inter (MeasurableSet.iUnion hE) ?_
    exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun c => himp c M
  have hA : MeasurableSet[m] {ω : Ω | a < (0 : ℝ)} := MeasurableSet.const _
  have key : {ω | a < ratSup E ω} =
      (Goodᶜ ∩ {_ω : Ω | a < (0 : ℝ)}) ∪ (Good ∩ ⋃ c : ℚ, ⋃ (_ : a < (c : ℝ)), E c) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, mem_iUnion, exists_prop]
    by_cases hg : (∃ c : ℚ, ω ∈ E c) ∧ ∃ M : ℚ, ∀ c : ℚ, ω ∈ E c → c ≤ M
    · have hgood : ω ∈ Good := by
        obtain ⟨c0, hc0⟩ := hg.1
        refine ⟨mem_iUnion.2 ⟨c0, hc0⟩, ?_⟩
        obtain ⟨M, hM⟩ := hg.2
        exact mem_iUnion.2 ⟨M, mem_iInter.2 fun c => hM c⟩
      have hbdd : BddAbove ((fun c : ℚ => (c : ℝ)) '' {c : ℚ | ω ∈ E c}) := by
        obtain ⟨M, hM⟩ := hg.2
        refine ⟨(M : ℝ), ?_⟩
        rintro x ⟨c, hc, rfl⟩
        show (c : ℝ) ≤ (M : ℝ)
        exact_mod_cast hM c hc
      have hne : ((fun c : ℚ => (c : ℝ)) '' {c : ℚ | ω ∈ E c}).Nonempty := by
        obtain ⟨c, hc⟩ := hg.1
        exact ⟨(c : ℝ), c, hc, rfl⟩
      unfold ratSup
      rw [lt_csSup_iff hbdd hne]
      constructor
      · rintro ⟨x, ⟨c, hc, rfl⟩, hax⟩
        right
        exact ⟨hgood, c, hax, hc⟩
      · rintro (⟨hng, _⟩ | ⟨_, c, hac, hc⟩)
        · exact absurd hgood hng
        · exact ⟨(c : ℝ), ⟨c, hc, rfl⟩, hac⟩
    · rw [ratSup_of_not_good hg]
      have hnot : ω ∉ Good := by
        rintro ⟨hU, hM⟩
        apply hg
        refine ⟨mem_iUnion.1 hU, ?_⟩
        obtain ⟨M, hM'⟩ := mem_iUnion.1 hM
        exact ⟨M, fun c hc => mem_iInter.1 hM' c hc⟩
      constructor
      · rintro hlt
        exact Or.inl ⟨hnot, hlt⟩
      · rintro (⟨_, hlt⟩ | ⟨hgm, _⟩)
        · exact hlt
        · exact absurd hgm hnot
  rw [key]
  exact (hGm.compl.inter hA).union (hGm.inter (MeasurableSet.iUnion fun c =>
    MeasurableSet.iUnion fun _ => hE c))

/-- **Exact version** (M3): countably many almost sure thresholds of `v` give an exact `m`-measurable version of `v`. -/
theorem exists_measurable_version_of_thresholds {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : @Measure Ω mΩ} (v : Ω → ℝ)
    (hthr : ∀ c : ℚ, ∃ E : Set Ω, MeasurableSet[m] E ∧ ∀ᵐ ω ∂P, (ω ∈ E ↔ (c : ℝ) < v ω)) :
    ∃ v' : Ω → ℝ, Measurable[m] v' ∧ ∀ᵐ ω ∂P, v' ω = v ω := by
  choose E hE hEω using hthr
  refine ⟨ratSup E, measurable_of_Ioi fun a => measurableSet_ratSup_lt hE a, ?_⟩
  filter_upwards [ae_all_iff.2 hEω] with ω hω
  exact ratSup_eq_of_thresholds hω

end MatedCRT.S5c
