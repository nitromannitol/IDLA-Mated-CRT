import Mathlib

/-!
# FIRST PASS, Proposition 4.2: countably many jump times of positive probability

This file contains the countable-witness argument and the
probabilistic conclusion, in generic form for an increasing family of random open sets.

For a family `U t ω` (increasing in `t`, open values) and a deterministic time `t`, the jump event is
`{U_t ≠ U_{t-}}` with `U_{t-} = ⋃_{0<s<t} U_s`. A jump is witnessed pathwise by a set `K` of a countable cover
`𝒦` with `K ⊆ U_t` and `K ⊄ U_q` for every rational `0 < q < t`. For fixed `K` these witness events are pairwise
disjoint in `t`, so only countably many `t` have positive witness probability.
-/

open MeasureTheory Set Filter Topology

namespace MatedCRT

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The jump event `{U_t ≠ U_{t-}}` with `U_{t-} = ⋃_{0<s<t} U_s`. -/
def strictGapJumpEvent (U : ℝ → Ω → Set ℂ) (t : ℝ) : Set Ω :=
  {ω | U t ω ≠ ⋃ s ∈ Ioo (0 : ℝ) t, U s ω}

/-- The witness event `A_t^K = {K ⊆ U_t} ∩ ⋂_{q ∈ ℚ ∩ (0,t)} {K ⊄ U_q}`. -/
def strictGapWitnessEvent (U : ℝ → Ω → Set ℂ) (K : Set ℂ) (t : ℝ) : Set Ω :=
  {ω | K ⊆ U t ω ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ K ⊆ U (q : ℝ) ω}

/-- Measurability of the witness event, from measurability of `{K ⊆ U_q}` at fixed times (countably many
rational times suffice). -/
theorem measurableSet_strictGapWitnessEvent {U : ℝ → Ω → Set ℂ} {K : Set ℂ}
    (hK : ∀ t : ℝ, MeasurableSet {ω | K ⊆ U t ω}) (t : ℝ) :
    MeasurableSet (strictGapWitnessEvent U K t) := by
  have hq : MeasurableSet {ω : Ω | ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ K ⊆ U (q : ℝ) ω} := by
    have heq : {ω : Ω | ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ K ⊆ U (q : ℝ) ω}
        = ⋂ q : ℚ, ({ω : Ω | ¬ (0 < (q : ℝ) ∧ (q : ℝ) < t)} ∪ {ω : Ω | K ⊆ U (q : ℝ) ω}ᶜ) := by
      ext ω
      simp only [Set.mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff]
      constructor
      · intro h q
        by_cases hc : 0 < (q : ℝ) ∧ (q : ℝ) < t
        · exact Or.inr (h q hc.1 hc.2)
        · exact Or.inl hc
      · intro h q h1 h2
        rcases h q with h3 | h3
        · exact absurd ⟨h1, h2⟩ h3
        · exact h3
    rw [heq]
    refine MeasurableSet.iInter fun q => MeasurableSet.union ?_ ?_
    · exact MeasurableSet.const _
    · exact (hK (q : ℝ)).compl
  have hset : strictGapWitnessEvent U K t
      = {ω : Ω | K ⊆ U t ω} ∩ {ω : Ω | ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ K ⊆ U (q : ℝ) ω} := by
    ext ω
    rfl
  rw [hset]
  exact (hK t).inter hq

omit [MeasurableSpace Ω] in
/-- Two witness events at distinct positive times are disjoint, since `A_a^K ⊆ {K ⊆ U_q}` for a rational
`q ∈ (a, b)` by monotonicity. -/
theorem strictGapWitnessEvent_disjoint {U : ℝ → Ω → Set ℂ}
    (hmono : ∀ ω : Ω, ∀ s t : ℝ, 0 < s → s ≤ t → U s ω ⊆ U t ω) (K : Set ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Disjoint (strictGapWitnessEvent U K a) (strictGapWitnessEvent U K b) := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hab
  have hq0 : 0 < (q : ℝ) := lt_trans ha hq1
  have hKq : K ⊆ U (q : ℝ) ω := h1.1.trans (hmono ω a q ha hq1.le)
  exact h2.2 q hq0 hq2 hKq

/-- For a fixed `K`, only countably many positive times have positive witness probability. -/
theorem strictGapWitness_pos_countable {U : ℝ → Ω → Set ℂ}
    (hmono : ∀ ω : Ω, ∀ s t : ℝ, 0 < s → s ≤ t → U s ω ⊆ U t ω) {K : Set ℂ}
    (hK : ∀ t : ℝ, MeasurableSet {ω | K ⊆ U t ω}) (P : Measure Ω) [IsFiniteMeasure P] :
    {t : ℝ | 0 < t ∧ 0 < P (strictGapWitnessEvent U K t)}.Countable := by
  let A : Ioi (0 : ℝ) → Set Ω := fun t => strictGapWitnessEvent U K (t : ℝ)
  have hA : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    have hne : (i : ℝ) ≠ (j : ℝ) := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact strictGapWitnessEvent_disjoint hmono K (Set.mem_Ioi.mp i.2) h
    · exact (strictGapWitnessEvent_disjoint hmono K (Set.mem_Ioi.mp j.2) h).symm
  have hc : Set.Countable {i : Ioi (0 : ℝ) | 0 < P (A i)} :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun i => measurableSet_strictGapWitnessEvent hK _) hA
  refine (hc.image Subtype.val).mono ?_
  rintro t ⟨ht0, htP⟩
  exact ⟨⟨t, ht0⟩, htP, rfl⟩

omit [MeasurableSpace Ω] in
/-- Pathwise witnesses: a jump at `t` is witnessed by some `K ∈ 𝒦` with
`x ∈ K ⊆ U_t`, where `x ∈ U_t \ U_{t-}`. -/
theorem strictGapJumpEvent_subset_witness {U : ℝ → Ω → Set ℂ}
    (hmono : ∀ ω : Ω, ∀ s t : ℝ, 0 < s → s ≤ t → U s ω ⊆ U t ω)
    (hopen : ∀ t : ℝ, ∀ ω : Ω, IsOpen (U t ω)) {𝒦 : Set (Set ℂ)}
    (hcov : ∀ V : Set ℂ, IsOpen V → ∀ x ∈ V, ∃ K ∈ 𝒦, x ∈ K ∧ K ⊆ V) (t : ℝ) :
    strictGapJumpEvent U t ⊆ ⋃ K ∈ 𝒦, strictGapWitnessEvent U K t := by
  intro ω hω
  have hle : (⋃ s ∈ Ioo (0 : ℝ) t, U s ω) ⊆ U t ω := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact hmono ω s t hs.1 hs.2.le hxs
  have hex : ∃ x ∈ U t ω, x ∉ ⋃ s ∈ Ioo (0 : ℝ) t, U s ω := by
    by_contra hcon
    apply hω
    refine Subset.antisymm ?_ hle
    intro x hxU
    by_contra hxn
    exact hcon ⟨x, hxU, hxn⟩
  obtain ⟨x, hxU, hxn⟩ := hex
  obtain ⟨K, hK𝒦, hxK, hKU⟩ := hcov (U t ω) (hopen t ω) x hxU
  refine mem_iUnion₂.mpr ⟨K, hK𝒦, hKU, fun q hq0 hqt hKq => hxn ?_⟩
  exact mem_iUnion₂.mpr ⟨(q : ℝ), ⟨hq0, hqt⟩, hKq hxK⟩

/-- **Countably many jump times of positive probability**. For an increasing family
of random open sets indexed by `t > 0`, with a countable cover `𝒦` of the open sets by sets whose witness
events are measurable, the set of `t > 0` at which `P(U_t ≠ U_{t-}) > 0` is countable. -/
theorem strictGapJump_pos_countable {U : ℝ → Ω → Set ℂ}
    (hmono : ∀ ω : Ω, ∀ s t : ℝ, 0 < s → s ≤ t → U s ω ⊆ U t ω)
    (hopen : ∀ t : ℝ, ∀ ω : Ω, IsOpen (U t ω)) {𝒦 : Set (Set ℂ)} (h𝒦 : 𝒦.Countable)
    (hcov : ∀ V : Set ℂ, IsOpen V → ∀ x ∈ V, ∃ K ∈ 𝒦, x ∈ K ∧ K ⊆ V)
    (hK : ∀ K ∈ 𝒦, ∀ t : ℝ, MeasurableSet {ω | K ⊆ U t ω}) (P : Measure Ω) [IsFiniteMeasure P] :
    {t : ℝ | 0 < t ∧ 0 < P (strictGapJumpEvent U t)}.Countable := by
  have hJ : ∀ t : ℝ, 0 < P (strictGapJumpEvent U t) → ∃ K ∈ 𝒦, 0 < P (strictGapWitnessEvent U K t) := by
    intro t ht
    by_contra hcon
    have hcon' : ∀ K ∈ 𝒦, P (strictGapWitnessEvent U K t) ≤ 0 := by
      intro K hK𝒦
      by_contra hlt
      exact hcon ⟨K, hK𝒦, lt_of_not_ge hlt⟩
    have h0 : P (⋃ K ∈ 𝒦, strictGapWitnessEvent U K t) = 0 := by
      rw [measure_biUnion_null_iff h𝒦]
      intro K hK𝒦
      exact nonpos_iff_eq_zero.mp (hcon' K hK𝒦)
    have hle := (measure_mono (strictGapJumpEvent_subset_witness hmono hopen hcov t)).trans_eq h0
    exact (not_le.mpr ht) hle
  have hbu : (⋃ K ∈ 𝒦, {t : ℝ | 0 < t ∧ 0 < P (strictGapWitnessEvent U K t)}).Countable :=
    Set.Countable.biUnion h𝒦 (fun K hK𝒦 => strictGapWitness_pos_countable hmono (hK K hK𝒦) P)
  refine hbu.mono ?_
  rintro t ⟨ht0, htP⟩
  obtain ⟨K, hK𝒦, hKP⟩ := hJ t htP
  exact mem_iUnion₂.mpr ⟨K, hK𝒦, ht0, hKP⟩

/-- `(0,∞)` is uncountable. -/
theorem not_countable_Ioi_zero_real : ¬ (Ioi (0 : ℝ)).Countable := by
  intro h
  apply Cardinal.not_countable_real
  have hsub : (Set.univ : Set ℝ) ⊆ Real.log '' Ioi (0 : ℝ) :=
    fun y _ => ⟨Real.exp y, Real.exp_pos y, Real.log_exp y⟩
  exact Set.Countable.mono hsub (h.image Real.log)

/-- **Probabilistic conclusion.** If `t ↦ P(U_t ≠ U_{t-})` is constant on `(0,∞)` and the
jump times of positive probability are countable, the constant is `0`: for every deterministic `t > 0`, almost
surely `U_t = U_{t-}`. -/
theorem strictGapJump_null_of_const {U : ℝ → Ω → Set ℂ} (P : Measure Ω)
    (hcount : {t : ℝ | 0 < t ∧ 0 < P (strictGapJumpEvent U t)}.Countable)
    (hconst : ∀ s t : ℝ, 0 < s → 0 < t → P (strictGapJumpEvent U s) = P (strictGapJumpEvent U t))
    {t : ℝ} (ht : 0 < t) : P (strictGapJumpEvent U t) = 0 := by
  by_contra hne
  have hpos : 0 < P (strictGapJumpEvent U t) := pos_iff_ne_zero.mpr hne
  have hsub : Ioi (0 : ℝ) ⊆ {s : ℝ | 0 < s ∧ 0 < P (strictGapJumpEvent U s)} :=
    fun s hs => ⟨hs, by rw [hconst s t hs ht]; exact hpos⟩
  exact not_countable_Ioi_zero_real (hcount.mono hsub)

/-- A countable cover of `ℂ`: closed balls centred in a countable dense set with positive rational radii. Every
open set is a union of such balls, and each point of an open `V` lies in one of them inside `V`. -/
theorem exists_countable_closedBall_cover :
    ∃ 𝒦 : Set (Set ℂ), 𝒦.Countable ∧ ∀ V : Set ℂ, IsOpen V → ∀ x ∈ V, ∃ K ∈ 𝒦, x ∈ K ∧ K ⊆ V := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  refine ⟨(fun p : ℂ × ℚ => Metric.closedBall p.1 (p.2 : ℝ)) '' (D ×ˢ {r : ℚ | 0 < r}), ?_, ?_⟩
  · exact (hDc.prod (Set.to_countable _)).image _
  · intro V hV x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV x hx
    obtain ⟨c, hcD, hcx⟩ := hDd.exists_dist_lt x (by linarith : (0 : ℝ) < ε / 3)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show dist x c < 2 * ε / 3 by linarith)
    have hr0 : (0 : ℚ) < r := by
      have : (0 : ℝ) < (r : ℝ) := lt_of_le_of_lt dist_nonneg hr1
      exact_mod_cast this
    refine ⟨Metric.closedBall c (r : ℝ), ⟨(c, r), ⟨hcD, hr0⟩, rfl⟩, ?_, ?_⟩
    · exact Metric.mem_closedBall.mpr hr1.le
    · intro y hy
      apply hball
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      have h1 := dist_triangle y c x
      rw [dist_comm c x] at h1
      linarith

end MatedCRT
