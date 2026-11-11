import MatedCRT.Defs.Setting

/-!
# FIRST PASS, Lemma 5.3: a deterministic time with no new entrance

For a random family `Λ ω t` of open sets, monotone in `t > 0` (`Λ_t` is the interior of the closure of the obstacle
cluster, Harmonic-Balls-LQG Defs/Obstacle.lean:69; monotone by `SatisfiesHarmonicBallConditions.monotoneOn`), the
new-entrance event at time `t`, `J(t) = {∃ y ∈ Λ_t, ∀ s ∈ (0, t), y ∉ Λ_s}`, is covered by the entry events
`E(D, t) = {D ⊆ Λ_t and D ⊄ Λ_q for every rational 0 < q < t}` of rational closed discs `D`. Pointwise, this needs only
openness and monotonicity. The entry events for distinct `t` are disjoint, so all but countably many `t` have
`P(E(D, t)) = 0`; choosing `t₀ ∈ (1, 2)` outside that countable set gives `P(J(t₀)) = 0`.

The one input not proved here is the null-measurability of the events `{D ⊆ Λ_t}` (hypothesis `hmeas`): this is what
`nullMeasurableSet_clusterInclusion` (FirstPass/S5c/ClusterInclusion.lean) gives only when the cluster is open
almost surely at the fixed time `t`, and `ae_isOpen_cluster_of_stopped` (FirstPass/S5c/ClusterOpen.lean) gives only on
`{t < clusterExitTime}`. No new frozen input is introduced.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace MatedCRT

/-- Index of the rational closed discs `closedBall (q₁ + q₂ i) r`, with rational centre and positive rational radius. -/
abbrev RatDiscIndex : Type := {x : ℚ × ℚ × ℚ // 0 < x.2.2}

/-- The rational closed disc of index `x`. -/
def ratDisc (x : RatDiscIndex) : Set ℂ :=
  Metric.closedBall (Complex.mk (x.1.1 : ℝ) (x.1.2.1 : ℝ)) (x.1.2.2 : ℝ)

/-- A point of an open set lies in a rational closed disc contained in the set. -/
theorem exists_ratDisc_mem_subset {U : Set ℂ} (hU : IsOpen U) {y : ℂ} (hy : y ∈ U) :
    ∃ x : RatDiscIndex, y ∈ ratDisc x ∧ ratDisc x ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y hy
  obtain ⟨q1, hq1a, hq1b⟩ := exists_rat_btwn (show y.re - ε / 8 < y.re + ε / 8 by linarith)
  obtain ⟨q2, hq2a, hq2b⟩ := exists_rat_btwn (show y.im - ε / 8 < y.im + ε / 8 by linarith)
  set c : ℂ := Complex.mk (q1 : ℝ) (q2 : ℝ) with hc
  have hre : |y.re - (q1 : ℝ)| < ε / 8 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have him : |y.im - (q2 : ℝ)| < ε / 8 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have hnorm : ‖y - c‖ ≤ |y.re - (q1 : ℝ)| + |y.im - (q2 : ℝ)| := by
    have h := Complex.norm_le_abs_re_add_abs_im (y - c)
    have e1 : (y - c).re = y.re - (q1 : ℝ) := rfl
    have e2 : (y - c).im = y.im - (q2 : ℝ) := rfl
    rw [e1, e2] at h
    exact h
  have hyc : dist y c < ε / 4 := by
    rw [dist_eq_norm]
    linarith
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show dist y c < ε / 2 by linarith)
  have hr0 : (0 : ℝ) < (r : ℝ) := lt_of_le_of_lt dist_nonneg hr1
  refine ⟨⟨(q1, q2, r), by exact_mod_cast hr0⟩, ?_, ?_⟩
  · show y ∈ Metric.closedBall c (r : ℝ)
    exact mem_closedBall.2 hr1.le
  · intro z hz
    apply hball
    have hzc : dist z c ≤ (r : ℝ) := mem_closedBall.1 hz
    have hzy : dist z y < ε := by
      calc dist z y ≤ dist z c + dist c y := dist_triangle _ _ _
        _ < ε := by rw [dist_comm c y] at *; linarith
    exact mem_ball.2 hzy

/-- The entry event of the rational disc `x` at time `t`: `D_x ⊆ Λ_t`, and `D_x ⊄ Λ_q` for every rational `0 < q < t`. -/
def entryEvent {Ω : Type} (Λ : Ω → ℝ → Set ℂ) (x : RatDiscIndex) (t : ℝ) : Set Ω :=
  {ω | ratDisc x ⊆ Λ ω t} ∩
    ⋂ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t}, {ω | ratDisc x ⊆ Λ ω (q.1 : ℝ)}ᶜ

theorem mem_entryEvent {Ω : Type} {Λ : Ω → ℝ → Set ℂ} {x : RatDiscIndex} {t : ℝ} {ω : Ω} :
    ω ∈ entryEvent Λ x t ↔
      ratDisc x ⊆ Λ ω t ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ ratDisc x ⊆ Λ ω (q : ℝ) := by
  simp only [entryEvent, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_compl_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q h0 ht => h2 ⟨q, h0, ht⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q => h2 q.1 q.2.1 q.2.2⟩

/-- The entry events are null-measurable, given the null-measurability of the disc-inclusion events `hmeas`. -/
theorem nullMeasurableSet_entryEvent {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Λ : Ω → ℝ → Set ℂ}
    (hmeas : ∀ (x : RatDiscIndex) (t : ℝ), 0 < t → NullMeasurableSet {ω | ratDisc x ⊆ Λ ω t} P)
    (x : RatDiscIndex) {t : ℝ} (ht : 0 < t) : NullMeasurableSet (entryEvent Λ x t) P :=
  (hmeas x t ht).inter (NullMeasurableSet.iInter fun q => (hmeas x q.1 q.2.1).compl)

/-- A new point of `Λ_{t}` (an open set) lies in a rational disc whose entry event contains `ω`. -/
theorem exists_entryEvent_of_new_point {Ω : Type} {Λ : Ω → ℝ → Set ℂ} {ω : Ω} {t : ℝ} (hopen : IsOpen (Λ ω t))
    {y : ℂ} (hy : y ∈ Λ ω t) (hnew : ∀ s ∈ Ioo (0 : ℝ) t, y ∉ Λ ω s) :
    ∃ x : RatDiscIndex, ω ∈ entryEvent Λ x t := by
  obtain ⟨x, hyx, hsub⟩ := exists_ratDisc_mem_subset hopen hy
  exact ⟨x, mem_entryEvent.2 ⟨hsub, fun q h0 ht hq => hnew (q : ℝ) ⟨h0, ht⟩ (hq hyx)⟩⟩

/-- Along a monotone family, an entry event at `t₁` excludes the entry event at a later `t₂`. -/
theorem not_mem_entryEvent_of_mono {Ω : Type} {Λ : Ω → ℝ → Set ℂ} {ω : Ω} (hm : MonotoneOn (Λ ω) (Ioi 0))
    {x : RatDiscIndex} {t₁ t₂ : ℝ} (h1 : 0 < t₁) (h12 : t₁ < t₂) (hA : ω ∈ entryEvent Λ x t₁) :
    ω ∉ entryEvent Λ x t₂ := by
  intro hB
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h12
  have hq0 : (0 : ℝ) < q := lt_trans h1 hq1
  have hmq : Λ ω t₁ ⊆ Λ ω (q : ℝ) := hm (show t₁ ∈ Ioi (0 : ℝ) from h1) (show (q : ℝ) ∈ Ioi (0 : ℝ) from hq0)
    hq1.le
  exact (mem_entryEvent.1 hB).2 q hq0 hq2 (Set.Subset.trans (mem_entryEvent.1 hA).1 hmq)

/-- **Entry-free times.** Let `Λ ω t` be, almost surely, open and monotone in `t > 0`, with the disc-inclusion events
null-measurable (`hmeas`). Then for some `t₀ ∈ (1, 2)`, almost surely no point of `Λ_{t₀}` is new, i.e.
`Λ_{t₀} ⊆ ⋃_{0 < s < t₀} Λ_s` (the countable-atoms choice of `t₀`). -/
theorem exists_entry_free_time {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : Ω → ℝ → Set ℂ)
    (hgood : ∀ᵐ ω ∂P, (∀ t : ℝ, 0 < t → IsOpen (Λ ω t)) ∧ MonotoneOn (Λ ω) (Ioi 0))
    (hmeas : ∀ (x : RatDiscIndex) (t : ℝ), 0 < t → NullMeasurableSet {ω | ratDisc x ⊆ Λ ω t} P) :
    ∃ t₀ ∈ Ioo (1 : ℝ) 2, P {ω | ∃ y ∈ Λ ω t₀, ∀ s ∈ Ioo (0 : ℝ) t₀, y ∉ Λ ω s} = 0 := by
  set Bad : Set Ω := {ω | ¬ ((∀ t : ℝ, 0 < t → IsOpen (Λ ω t)) ∧ MonotoneOn (Λ ω) (Ioi 0))} with hBad_def
  have hBad : P Bad = 0 := ae_iff.1 hgood
  have hBadm : NullMeasurableSet Bad P := NullMeasurableSet.of_null hBad
  set E : RatDiscIndex → ℝ → Set Ω := fun x t => entryEvent Λ x t ∩ Badᶜ with hE_def
  have hEm : ∀ (x : RatDiscIndex) (t : ℝ), 0 < t → NullMeasurableSet (E x t) P := fun x t ht =>
    (nullMeasurableSet_entryEvent hmeas x ht).inter hBadm.compl
  have hEdisj : ∀ (x : RatDiscIndex) (t₁ t₂ : ℝ), 0 < t₁ → t₁ < t₂ → Disjoint (E x t₁) (E x t₂) := by
    intro x t₁ t₂ h1 h12
    refine Set.disjoint_left.2 fun ω hA hB => ?_
    have hg : (∀ t : ℝ, 0 < t → IsOpen (Λ ω t)) ∧ MonotoneOn (Λ ω) (Ioi 0) := not_not.1 hA.2
    exact not_mem_entryEvent_of_mono hg.2 h1 h12 hA.1 hB.1
  have hEpair : ∀ x : RatDiscIndex,
      Pairwise (fun i j : {t : ℝ // 0 < t} => AEDisjoint P (E x i.1) (E x j.1)) := by
    intro x i j hij
    have hne : (i : ℝ) ≠ (j : ℝ) := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hEdisj x i j i.2 h).aedisjoint
    · exact ((hEdisj x j i j.2 h).aedisjoint).symm
  have hcount : ∀ x : RatDiscIndex, Set.Countable {t : {t : ℝ // 0 < t} | 0 < P (E x t.1)} := fun x =>
    MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion₀ (As := fun t : {t : ℝ // 0 < t} => E x t.1)
      (fun t => hEm x t.1 t.2) (hEpair x)
  set S : Set ℝ := ⋃ x : RatDiscIndex,
    (Subtype.val '' {t : {t : ℝ // 0 < t} | 0 < P (E x t.1)}) with hS_def
  have hScount : S.Countable := Set.countable_iUnion fun x => (hcount x).image Subtype.val
  have ht0 : ∃ t₀ ∈ Ioo (1 : ℝ) 2, t₀ ∉ S := by
    by_contra h
    have hsub : Ioo (1 : ℝ) 2 ⊆ S := fun t ht => by_contra fun hn => h ⟨t, ht, hn⟩
    have h0 : volume (Ioo (1 : ℝ) 2) = 0 := (hScount.mono hsub).measure_zero volume
    rw [Real.volume_Ioo] at h0
    norm_num at h0
  obtain ⟨t₀, ht₀, ht₀S⟩ := ht0
  have ht₀pos : (0 : ℝ) < t₀ := by linarith [ht₀.1]
  have hzero : ∀ x : RatDiscIndex, P (E x t₀) = 0 := by
    intro x
    have hnot : ¬ 0 < P (E x t₀) := fun h =>
      ht₀S (Set.mem_iUnion.2 ⟨x, ⟨⟨t₀, ht₀pos⟩, h, rfl⟩⟩)
    exact nonpos_iff_eq_zero.1 (not_lt.1 hnot)
  refine ⟨t₀, ht₀, ?_⟩
  have hsubset : {ω | ∃ y ∈ Λ ω t₀, ∀ s ∈ Ioo (0 : ℝ) t₀, y ∉ Λ ω s} ⊆ Bad ∪ ⋃ x : RatDiscIndex, E x t₀ := by
    intro ω hω
    obtain ⟨y, hy, hnew⟩ := hω
    by_cases hbad : ω ∈ Bad
    · exact Or.inl hbad
    · right
      have hg : (∀ t : ℝ, 0 < t → IsOpen (Λ ω t)) ∧ MonotoneOn (Λ ω) (Ioi 0) := not_not.1 hbad
      obtain ⟨x, hx⟩ := exists_entryEvent_of_new_point (hg.1 t₀ ht₀pos) hy hnew
      exact Set.mem_iUnion.2 ⟨x, ⟨hx, hbad⟩⟩
  exact measure_mono_null hsubset (measure_union_null hBad (measure_iUnion_null hzero))

end MatedCRT
