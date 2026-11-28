import MatedCRT.FirstPass.Derived.ConeConfigReconstructionMap

/-!
# Cutoffs for the curve event of the reconstruction

For a random curve `ηL` with `ηL 0 = 0`, proper, and vanishing only at the time `0`, the curve event
`ReconCurveEvent α R a L δ M` has probability at least `1 - ε` for suitable cutoffs `a, L, δ, M`.
Each of the four conditions of the event holds eventually along an increasing sequence of cutoffs,
so its failure probability tends to `0` (continuity at `0`, properness, and compactness of the two
time blocks).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRT

/-- An increasing sequence of measurable events with an almost sure union has failure
probabilities tending to `0`. -/
theorem exists_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : ℕ → Set Ω} (hs : ∀ m, MeasurableSet (s m)) (hmono : Monotone s)
    (hae : ∀ᵐ ω ∂P, ∃ m, ω ∈ s m) {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ m, P (s m)ᶜ ≤ ε := by
  have hanti : Antitone fun m => (s m)ᶜ := fun m n h => compl_subset_compl.2 (hmono h)
  have hlim := tendsto_measure_iInter_atTop (μ := P) (fun m => (hs m).compl.nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ m, (s m)ᶜ) = 0 := by
    have h := ae_iff.1 hae
    convert h using 2
    ext ω
    simp
  rw [hnull] at hlim
  obtain ⟨m, hm⟩ := ((ENNReal.tendsto_nhds_zero.1 hlim) ε hε).exists
  exact ⟨m, hm⟩

/-- The curve stays in `B_{α/4}(0)` on `[-2a, 2a]` for small `a`. -/
theorem exists_a_mapsTo {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ηL : Ω → C(ℝ, ℂ)} (hη : Measurable ηL) (h0 : ∀ᵐ ω ∂P, ηL ω 0 = 0) {α : ℝ} (hα : 0 < α)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧
      P {ω | ¬ MapsTo (ηL ω) (Icc (-(2 * a)) (2 * a)) (ball (0 : ℂ) (α / 4))} ≤ ε := by
  let s : ℕ → Set Ω := fun m => ηL ⁻¹'
    {e | MapsTo e (Icc (-(2 * (1 / ((m : ℝ) + 1)))) (2 * (1 / ((m : ℝ) + 1))))
      (ball (0 : ℂ) (α / 4))}
  have hs : ∀ m, MeasurableSet (s m) := fun m =>
    hη (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc isOpen_ball).measurableSet
  have hmono : Monotone s := by
    intro m n hmn ω hω t ht
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    exact hω ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hae : ∀ᵐ ω ∂P, ∃ m, ω ∈ s m := by
    filter_upwards [h0] with ω hω
    have hball : ball (0 : ℂ) (α / 4) ∈ 𝓝 (ηL ω 0) := by
      rw [hω]
      exact ball_mem_nhds _ (by positivity)
    obtain ⟨r, hr, hr'⟩ :=
      Metric.mem_nhds_iff.1 ((ηL ω).continuous.continuousAt.preimage_mem_nhds hball)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < r / 2 by positivity)
    refine ⟨m, fun t ht => hr' ?_⟩
    rw [mem_ball, Real.dist_eq, sub_zero]
    have := abs_le.2 ⟨ht.1, ht.2⟩
    linarith
  obtain ⟨m, hm⟩ := exists_measure_compl_le hs hmono hae hε
  exact ⟨1 / ((m : ℝ) + 1), by positivity, hm⟩

/-- The two outer tails of the curve lie outside `closedBall 0 (2R + 2)`: a form of the condition
over all compact intervals of times. -/
theorem forall_mapsTo_tails_iff {e : C(ℝ, ℂ)} {L : ℝ} {r : ℝ} :
    (∀ k : ℕ, MapsTo e (Icc (L / 2) (L / 2 + k) ∪ Icc (-(L / 2) - k) (-(L / 2)))
      (closedBall (0 : ℂ) r)ᶜ) ↔ ∀ t : ℝ, L / 2 ≤ |t| → e t ∉ closedBall (0 : ℂ) r := by
  constructor
  · intro h t ht
    rcases le_abs'.1 ht with h1 | h1
    · refine h ⌈-(L / 2) - t⌉₊ (Or.inr ⟨?_, h1⟩)
      linarith [Nat.le_ceil (-(L / 2) - t)]
    · refine h ⌈t - L / 2⌉₊ (Or.inl ⟨h1, ?_⟩)
      linarith [Nat.le_ceil (t - L / 2)]
  · intro h k t ht
    rcases ht with ht | ht
    · exact h t (le_trans ht.1 (le_abs_self t))
    · exact h t (le_trans (by linarith [ht.2]) (neg_le_abs t))

/-- The curve is outside `closedBall 0 (2R + 2)` for large times, for suitable `L > 4a`. -/
theorem exists_L_tails {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ηL : Ω → C(ℝ, ℂ)} (hη : Measurable ηL)
    (hprop : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ)) {R a : ℝ} (ha : 0 < a)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ L : ℝ, 4 * a < L ∧ P {ω | ¬ ∀ k : ℕ, MapsTo (ηL ω)
      (Icc (L / 2) (L / 2 + k) ∪ Icc (-(L / 2) - k) (-(L / 2))) (closedBall (0 : ℂ) (2 * R + 2))ᶜ} ≤
        ε := by
  let s : ℕ → Set Ω := fun m => ⋂ k : ℕ, ηL ⁻¹'
    {e | MapsTo e (Icc ((4 * a + 1 + m) / 2) ((4 * a + 1 + m) / 2 + k) ∪
      Icc (-((4 * a + 1 + m) / 2) - k) (-((4 * a + 1 + m) / 2))) (closedBall (0 : ℂ) (2 * R + 2))ᶜ}
  have hs : ∀ m, MeasurableSet (s m) := fun m => MeasurableSet.iInter fun k =>
    hη (ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_Icc.union isCompact_Icc)
      isClosed_closedBall.isOpen_compl).measurableSet
  have hmem : ∀ m ω, ω ∈ s m ↔ ∀ t : ℝ, (4 * a + 1 + m) / 2 ≤ |t| →
      ηL ω t ∉ closedBall (0 : ℂ) (2 * R + 2) := fun m ω => by
    rw [← forall_mapsTo_tails_iff]
    simp [s]
  have hmono : Monotone s := by
    intro m n hmn ω hω
    rw [hmem] at hω ⊢
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact fun t ht => hω t (le_trans (by linarith) ht)
  have hae : ∀ᵐ ω ∂P, ∃ m, ω ∈ s m := by
    filter_upwards [hprop] with ω hω
    have h2 : (⇑(ηL ω)) ⁻¹' (closedBall (0 : ℂ) (2 * R + 2))ᶜ ∈ cocompact ℝ :=
      hω (isCompact_closedBall _ _).compl_mem_cocompact
    obtain ⟨K, hKc, hK⟩ := Filter.mem_cocompact.1 h2
    obtain ⟨T, hT⟩ := hKc.isBounded.subset_closedBall (0 : ℝ)
    obtain ⟨m, hm⟩ := exists_nat_gt (2 * T)
    refine ⟨m, (hmem m ω).2 fun t ht => ?_⟩
    have htK : t ∉ K := fun htK => by
      have := mem_closedBall_zero_iff.1 (hT htK)
      rw [Real.norm_eq_abs] at this
      linarith
    exact hK htK
  obtain ⟨m, hm⟩ := exists_measure_compl_le hs hmono hae hε
  refine ⟨4 * a + 1 + m, by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)], ?_⟩
  refine le_trans (measure_mono ?_) hm
  intro ω hω hmem'
  apply hω
  simp only [s, mem_iInter, mem_preimage, mem_ofPred_eq] at hmem'
  exact hmem'

/-- The curve stays away from `0` on the two blocks, for small `δ`. -/
theorem exists_δ_blocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ηL : Ω → C(ℝ, ℂ)} (hη : Measurable ηL) (hz : ∀ᵐ ω ∂P, ∀ t, ηL ω t = 0 → t = 0) {a L : ℝ}
    (ha : 0 < a) (haL : a ≤ L) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ P {ω | ¬ MapsTo (ηL ω) (Icc (-L) (-a) ∪ Icc a L)
      (closedBall (0 : ℂ) (2 * δ))ᶜ} ≤ ε := by
  let s : ℕ → Set Ω := fun m => ηL ⁻¹' {e | MapsTo e (Icc (-L) (-a) ∪ Icc a L)
    (closedBall (0 : ℂ) (2 * (1 / ((m : ℝ) + 1))))ᶜ}
  have hs : ∀ m, MeasurableSet (s m) := fun m =>
    hη (ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_Icc.union isCompact_Icc)
      isClosed_closedBall.isOpen_compl).measurableSet
  have hmono : Monotone s := by
    intro m n hmn ω hω t ht
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    exact fun hc => hω ht (closedBall_subset_closedBall (by linarith) hc)
  have hae : ∀ᵐ ω ∂P, ∃ m, ω ∈ s m := by
    filter_upwards [hz] with ω hω
    have hB : IsCompact (Icc (-L) (-a) ∪ Icc a L) := isCompact_Icc.union isCompact_Icc
    obtain ⟨t₀, ht₀, hmin⟩ := hB.exists_isMinOn ⟨a, Or.inr ⟨le_rfl, haL⟩⟩
      (f := fun t => ‖ηL ω t‖) (by fun_prop)
    have ht₀ne : t₀ ≠ 0 := by
      rcases ht₀ with h | h
      · exact (by linarith [h.2] : t₀ < 0).ne
      · exact (by linarith [h.1] : 0 < t₀).ne'
    have hc : 0 < ‖ηL ω t₀‖ := norm_pos_iff.2 fun h => ht₀ne (hω t₀ h)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ‖ηL ω t₀‖ / 2 by positivity)
    refine ⟨m, fun t ht hmem => ?_⟩
    have h1 : ‖ηL ω t₀‖ ≤ ‖ηL ω t‖ := hmin ht
    have h2 := mem_closedBall_zero_iff.1 hmem
    linarith
  obtain ⟨m, hm⟩ := exists_measure_compl_le hs hmono hae hε
  exact ⟨1 / ((m : ℝ) + 1), by positivity, hm⟩

/-- The curve is bounded on the two blocks, for large `M`. -/
theorem exists_M_blocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ηL : Ω → C(ℝ, ℂ)} (hη : Measurable ηL) (a L δ : ℝ) (hδ : 0 < δ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, δ < M ∧ P {ω | ¬ MapsTo (ηL ω) (Icc (-L) (-a) ∪ Icc a L) (ball (0 : ℂ) (M / 2))} ≤
      ε := by
  let s : ℕ → Set Ω := fun m => ηL ⁻¹' {e | MapsTo e (Icc (-L) (-a) ∪ Icc a L)
    (ball (0 : ℂ) ((δ + 1 + m) / 2))}
  have hs : ∀ m, MeasurableSet (s m) := fun m =>
    hη (ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_Icc.union isCompact_Icc)
      isOpen_ball).measurableSet
  have hmono : Monotone s := by
    intro m n hmn ω hω t ht
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact ball_subset_ball (by linarith) (hω ht)
  have hae : ∀ᵐ ω ∂P, ∃ m, ω ∈ s m := by
    refine Eventually.of_forall fun ω => ?_
    obtain ⟨C, hC⟩ := (isCompact_Icc.union isCompact_Icc).exists_bound_of_continuousOn
      (f := fun t => ηL ω t) (ηL ω).continuous.continuousOn
    obtain ⟨m, hm⟩ := exists_nat_gt (2 * C)
    refine ⟨m, fun t ht => ?_⟩
    rw [mem_ball_zero_iff]
    linarith [hC t ht]
  obtain ⟨m, hm⟩ := exists_measure_compl_le hs hmono hae hε
  exact ⟨δ + 1 + m, by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)], hm⟩

/-- **Suitable cutoffs for the curve event**: for a random proper curve through `0` at time `0` and
vanishing only there, the curve event of the reconstruction has probability at least `1 - ε` for
suitable cutoffs `a, L, δ, M`. -/
theorem exists_cutoffs_reconCurveEvent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ηL : Ω → C(ℝ, ℂ)} (hm : Measurable ηL)
    (h0 : ∀ᵐ ω ∂P, ηL ω 0 = 0) (hprop : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ))
    (hz : ∀ᵐ ω ∂P, ∀ t, ηL ω t = 0 → t = 0) {α R : ℝ} (hα : 0 < α) (hαR : α < R) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ a L δ M : ℝ, 0 < a ∧ 4 * a < L ∧ 0 < δ ∧ δ < M ∧
      P {ω | ηL ω ∉ ReconCurveEvent α R a L δ M} ≤ ε := by
  clear hαR
  have hε' : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨a, ha, h1⟩ := exists_a_mapsTo hm h0 hα hε'
  obtain ⟨L, haL, h2⟩ := exists_L_tails (R := R) hm hprop ha hε'
  obtain ⟨δ, hδ, h3⟩ := exists_δ_blocks hm hz ha (by linarith) hε'
  obtain ⟨M, hδM, h4⟩ := exists_M_blocks (P := P) hm a L δ hδ hε'
  refine ⟨a, L, δ, M, ha, haL, hδ, hδM, ?_⟩
  have hsub : {ω | ηL ω ∉ ReconCurveEvent α R a L δ M} ⊆
      ({ω | ¬ MapsTo (ηL ω) (Icc (-(2 * a)) (2 * a)) (ball (0 : ℂ) (α / 4))} ∪
        {ω | ¬ ∀ k : ℕ, MapsTo (ηL ω) (Icc (L / 2) (L / 2 + k) ∪ Icc (-(L / 2) - k) (-(L / 2)))
          (closedBall (0 : ℂ) (2 * R + 2))ᶜ}) ∪
      ({ω | ¬ MapsTo (ηL ω) (Icc (-L) (-a) ∪ Icc a L) (closedBall (0 : ℂ) (2 * δ))ᶜ} ∪
        {ω | ¬ MapsTo (ηL ω) (Icc (-L) (-a) ∪ Icc a L) (ball (0 : ℂ) (M / 2))}) := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
    obtain ⟨⟨c1, c2⟩, c3, c4⟩ := hcon
    exact hω ⟨c1, c2, fun t ht => ⟨c4 ht, c3 ht⟩⟩
  calc P {ω | ηL ω ∉ ReconCurveEvent α R a L δ M}
      ≤ P (({ω | ¬ MapsTo (ηL ω) (Icc (-(2 * a)) (2 * a)) (ball (0 : ℂ) (α / 4))} ∪
        {ω | ¬ ∀ k : ℕ, MapsTo (ηL ω) (Icc (L / 2) (L / 2 + k) ∪ Icc (-(L / 2) - k) (-(L / 2)))
          (closedBall (0 : ℂ) (2 * R + 2))ᶜ}) ∪
      ({ω | ¬ MapsTo (ηL ω) (Icc (-L) (-a) ∪ Icc a L) (closedBall (0 : ℂ) (2 * δ))ᶜ} ∪
        {ω | ¬ MapsTo (ηL ω) (Icc (-L) (-a) ∪ Icc a L) (ball (0 : ℂ) (M / 2))})) :=
        measure_mono hsub
    _ ≤ (P {ω | ¬ MapsTo (ηL ω) (Icc (-(2 * a)) (2 * a)) (ball (0 : ℂ) (α / 4))} +
        P {ω | ¬ ∀ k : ℕ, MapsTo (ηL ω) (Icc (L / 2) (L / 2 + k) ∪ Icc (-(L / 2) - k) (-(L / 2)))
          (closedBall (0 : ℂ) (2 * R + 2))ᶜ}) +
        (P {ω | ¬ MapsTo (ηL ω) (Icc (-L) (-a) ∪ Icc a L) (closedBall (0 : ℂ) (2 * δ))ᶜ} +
        P {ω | ¬ MapsTo (ηL ω) (Icc (-L) (-a) ∪ Icc a L) (ball (0 : ℂ) (M / 2))}) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ ≤ (ε / 4 + ε / 4) + (ε / 4 + ε / 4) := by gcongr
    _ = ε / 4 * 4 := by ring
    _ = ε := ENNReal.div_mul_cancel (by norm_num) (by norm_num)

end MatedCRT
