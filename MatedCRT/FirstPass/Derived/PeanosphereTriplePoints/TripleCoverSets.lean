import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.TripleCoverWalk

/-!
# The compact sets of times of the triple-point cover

For coordinates `X`, `Y`, rationals `a < b < q < r` and `n`, the set `Eset X Y a b q r n` of
times `t ∈ [a, b]` with `X t = min_{[t, q]} X`, `Y t = min_{[t, r]} Y` and
`min_{[q, r]} X ≤ X t - 1 / (n + 1)` is compact. When `X` is nowhere monotone it has empty
interior, and any traversal whose fibres are the classes of `Jrel X Y` is injective on it: for
`t < t'` in the set the `X`-class of `t` ends in `[q, r)` while the `Y`-class of `t'` ends at or
after `r`, so the two classes cross.
-/

set_option autoImplicit false

open Set Filter Topology

namespace MatedCRT.PeanosphereTriplePoints

variable {X Y : ℝ → ℝ}

/-- The data of a traversal `η` whose fibres are the classes of `Jrel X Y`. -/
structure Setup (X Y : ℝ → ℝ) (η : ℝ → ℂ) : Prop where
  coordX : Coord X
  coordY : Coord Y
  noXY : NoOppositeSideMin X Y
  noYX : NoOppositeSideMin Y X
  fib : ∀ s t, η s = η t ↔ Jrel X Y s t

/-- The compact sets of times used to cover the triple points. -/
def Eset (X Y : ℝ → ℝ) (a b q r : ℝ) (n : ℕ) : Set ℝ :=
  {t | t ∈ Icc a b ∧ (∀ s ∈ Icc t q, X t ≤ X s) ∧ (∀ s ∈ Icc t r, Y t ≤ Y s) ∧
    ∃ s ∈ Icc q r, X s ≤ X t - 1 / ((n : ℝ) + 1)}

theorem isClosed_leftMin {X : ℝ → ℝ} (hX : Continuous X) (q : ℝ) :
    IsClosed {t : ℝ | ∀ s ∈ Icc t q, X t ≤ X s} := by
  have : {t : ℝ | ∀ s ∈ Icc t q, X t ≤ X s} =
      ⋂ s : ℝ, {t : ℝ | s ≤ q → t ≤ s → X t ≤ X s} := by
    ext t
    simp only [mem_ofPred_eq, mem_iInter, mem_Icc]
    constructor
    · intro h s hsq hts
      exact h s ⟨hts, hsq⟩
    · intro h s hs
      exact h s hs.2 hs.1
  rw [this]
  refine isClosed_iInter fun s => ?_
  by_cases hsq : s ≤ q
  · have : {t : ℝ | s ≤ q → t ≤ s → X t ≤ X s} = (Iio s ∩ {t | X s < X t})ᶜ := by
      ext t
      simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff, mem_Iio, not_and, not_lt]
      constructor
      · intro h hts
        exact h hsq hts.le
      · intro h _ hts
        rcases hts.eq_or_lt with rfl | hlt
        · exact le_rfl
        · exact h hlt
    rw [this]
    exact (isOpen_Iio.inter (isOpen_lt continuous_const hX)).isClosed_compl
  · have : {t : ℝ | s ≤ q → t ≤ s → X t ≤ X s} = univ := by
      ext t
      simp [hsq]
    rw [this]
    exact isClosed_univ

theorem isClosed_Eset (hX : Coord X) (hY : Coord Y) {a b q r : ℝ} (hqr : q ≤ r) (n : ℕ) :
    IsClosed (Eset X Y a b q r n) := by
  obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hqr)
    hX.cont.continuousOn
  have h3 : IsClosed {t : ℝ | ∃ s ∈ Icc q r, X s ≤ X t - 1 / ((n : ℝ) + 1)} := by
    have : {t : ℝ | ∃ s ∈ Icc q r, X s ≤ X t - 1 / ((n : ℝ) + 1)} =
        {t | X s0 ≤ X t - 1 / ((n : ℝ) + 1)} := by
      ext t
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨s, hs, h⟩
        exact (isMinOn_iff.1 hmin s hs).trans h
      · intro h
        exact ⟨s0, hs0, h⟩
    rw [this]
    exact isClosed_le continuous_const (hX.cont.sub continuous_const)
  have : Eset X Y a b q r n = Icc a b ∩ ({t | ∀ s ∈ Icc t q, X t ≤ X s} ∩
      ({t | ∀ s ∈ Icc t r, Y t ≤ Y s} ∩ {t | ∃ s ∈ Icc q r, X s ≤ X t - 1 / ((n : ℝ) + 1)})) := by
    ext t
    simp only [Eset, mem_ofPred_eq, mem_inter_iff]
  rw [this]
  exact isClosed_Icc.inter ((isClosed_leftMin hX.cont q).inter
    ((isClosed_leftMin hY.cont r).inter h3))

theorem isCompact_Eset (hX : Coord X) (hY : Coord Y) {a b q r : ℝ} (hqr : q ≤ r) (n : ℕ) :
    IsCompact (Eset X Y a b q r n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_Eset hX hY hqr n) fun _ ht => ht.1

theorem interior_Eset_eq_empty (hmono : NowhereMonotone X) {a b q r : ℝ} (hbq : b < q) (n : ℕ) :
    interior (Eset X Y a b q r n) = ∅ := by
  by_contra hne
  obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior t ht
  have hsub : Icc (t - ε / 2) (t + ε / 2) ⊆ Eset X Y a b q r n := by
    intro s hs
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  apply (hmono (t - ε / 2) (t + ε / 2) (by linarith)).1
  intro s1 hs1 s2 hs2 h12
  have h1 := hsub hs1
  have h2 := hsub hs2
  exact h1.2.1 s2 ⟨h12, by linarith [h2.1.2]⟩

theorem Eset_facts (hX : Coord X) (hY : Coord Y) (hXY : NoOppositeSideMin X Y)
    (hYX : NoOppositeSideMin Y X) {a b q r : ℝ} (hbq : b < q) (hqr : q < r) (n : ℕ) {t : ℝ}
    (ht : t ∈ Eset X Y a b q r n) :
    lo X t = t ∧ lo Y t = t ∧ q ≤ hi X t ∧ hi X t < r ∧ r ≤ hi Y t := by
  obtain ⟨⟨-, htb⟩, hXm, hYm, s0, hs0, hs0'⟩ := ht
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  refine ⟨lo_eq_of_right_min hX hXY (c := r) (by linarith) hYm,
    lo_eq_of_right_min hY hYX (c := q) (by linarith) hXm, ?_, ?_, ?_⟩
  · refine le_csInf (hiSet_nonempty hX t) fun u hu => ?_
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (hXm u ⟨hu.1, hlt.le⟩) (not_le.2 hu.2)
  · have hlt : X s0 < X t := lt_of_le_of_lt hs0' (sub_lt_self _ hpos)
    have hle : hi X t ≤ s0 :=
      csInf_le (hiSet_bddBelow X t) ⟨htb.trans (hbq.le.trans hs0.1), hlt⟩
    have hne : hi X t ≠ s0 := by
      intro h
      have := X_hi hX t
      rw [h] at this
      linarith
    exact lt_of_lt_of_le (lt_of_le_of_ne hle hne) hs0.2
  · refine le_csInf (hiSet_nonempty hY t) fun u hu => ?_
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (hYm u ⟨hu.1, hlt.le⟩) (not_le.2 hu.2)

theorem Eset_injOn {η : ℝ → ℂ} (hS : Setup X Y η) {a b q r : ℝ} (hbq : b < q) (hqr : q < r)
    (n : ℕ) : InjOn η (Eset X Y a b q r n) := by
  have key : ∀ t ∈ Eset X Y a b q r n, ∀ t' ∈ Eset X Y a b q r n, t < t' → η t ≠ η t' := by
    intro t ht t' ht' hlt heq
    obtain ⟨h1, h2, h3, h4, h5⟩ := Eset_facts hS.coordX hS.coordY hS.noXY hS.noYX hbq hqr n ht
    obtain ⟨h1', h2', -, -, h5'⟩ :=
      Eset_facts hS.coordX hS.coordY hS.noXY hS.noYX hbq hqr n ht'
    refine not_jrel_of_cross hS.coordX hS.coordY hS.noXY hS.noYX ⟨h1, h2⟩ ⟨h1', h2'⟩ hlt
      ?_ ?_ ?_ ((hS.fib t t').1 heq)
    · exact lt_of_le_of_lt ht'.1.2 (lt_of_lt_of_le hbq h3)
    · exact lt_of_lt_of_le h4 h5'
    · exact lt_of_lt_of_le h4 h5
  intro t ht t' ht' heq
  rcases lt_trichotomy t t' with h | h | h
  · exact absurd heq (key t ht t' ht' h)
  · exact h
  · exact absurd heq.symm (key t' ht' t ht h)

/-- Local minima of a coordinate form a countable set. -/
theorem countable_isLocalMin (hX : Coord X) : {m : ℝ | IsLocalMin X m}.Countable := by
  have hsub : {m : ℝ | IsLocalMin X m} ⊆
      ⋃ (p : ℚ) (q : ℚ), {m : ℝ | m ∈ Ioo (p : ℝ) q ∧ ∀ x ∈ Ioo (p : ℝ) q, X m ≤ X x} := by
    intro m hm
    have hm' : ∀ᶠ y in 𝓝 m, X m ≤ X y := hm
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hm'
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show m - ε < m by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show m < m + ε by linarith)
    simp only [mem_iUnion]
    refine ⟨p, q, ⟨hp2, hq1⟩, fun x hx => ?_⟩
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  refine Set.Countable.mono hsub (countable_iUnion fun p => countable_iUnion fun q => ?_)
  refine Set.Subsingleton.countable ?_
  intro m hm m' hm'
  by_contra hne
  have hl : IsLocalMin X m := isLocalMin_of_Ioo hm.1.1 hm.1.2 hm.2
  have hl' : IsLocalMin X m' := isLocalMin_of_Ioo hm'.1.1 hm'.1.2 hm'.2
  exact hX.locMin_ne m m' hne hl hl' (le_antisymm (hm.2 m' hm'.1) (hm'.2 m hm.1))

end MatedCRT.PeanosphereTriplePoints
