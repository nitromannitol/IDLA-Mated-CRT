import Mathlib

/-!
# FIRST PASS, Proposition 4.2: countable proxies for the strict-gap jump event (B3)

For open sets `U s`, increasing in `s` and regular
(`interior (closure (U s)) = U s`, the regular openness of harmonic balls; Armitage-Gardiner, Sec. 1), the jump event
`{U_t ≠ ⋃_{0<s<t} U_s}` is decided by countably many coordinates `1_{d ∈ U_s}` with `d ∈ D` (a countable dense set) and
`s ∈ {t} ∪ ℚ`. Such events are measurable in the product σ-algebra on paths (B3). The naive jump event is not: its
quantifier over the points of the plane is uncountable.

Chain: `ratBallCover` (countable cover), `strictGap_jump_iff` (witness
characterisation, by compactness of closed balls), `closedBall_subset_iff_proxy` (inclusion of a closed ball through
countable coordinates), `strictGap_jump_iff_proxy`, and `measurableSet_strictGapProxyEvent` (measurability).
-/

open MeasureTheory Set Metric Filter Topology

namespace MatedCRT

/-- The countable cover `𝒦` by closed balls with centres in `D` and positive rational radii. -/
def ratBallCover (D : Set ℂ) : Set (Set ℂ) :=
  (fun x : ℂ × ℚ => closedBall x.1 (x.2 : ℝ)) '' (D ×ˢ {r : ℚ | 0 < r})

theorem ratBallCover_countable {D : Set ℂ} (hD : D.Countable) : (ratBallCover D).Countable :=
  (hD.prod (Set.to_countable _)).image _

/-- Every open set is covered by the cover `𝒦` inside it (Armitage-Gardiner, rational approximation). -/
theorem ratBallCover_cover {D : Set ℂ} (hD : Dense D) :
    ∀ V : Set ℂ, IsOpen V → ∀ x ∈ V, ∃ K ∈ ratBallCover D, x ∈ K ∧ K ⊆ V := by
  intro V hV x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV x hx
  obtain ⟨d, hdD, hdx⟩ := Metric.mem_closure_iff.1 (hD x) (ε / 2) (half_pos hε)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show dist x d < ε - dist x d by linarith)
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt dist_nonneg hr1
  refine ⟨closedBall d (r : ℝ), ⟨(d, r), ⟨hdD, by exact_mod_cast hr0⟩, rfl⟩, ?_, ?_⟩
  · rw [mem_closedBall, dist_comm]
    linarith [dist_comm d x]
  · intro y hy
    apply hball
    rw [mem_ball]
    have h1 : dist y d ≤ r := mem_closedBall.1 hy
    linarith [dist_triangle y d x, dist_comm d x]

/-- Closure of an open set through a dense set: `z ∈ cl U` iff `z` is a limit of points of `D ∩ U`. -/
theorem mem_closure_iff_of_dense {D U : Set ℂ} (hD : Dense D) (hU : IsOpen U) (z : ℂ) :
    z ∈ closure U ↔ ∀ m : ℕ, ∃ d ∈ D, d ∈ U ∧ dist z d < 1 / ((m : ℝ) + 1) := by
  constructor
  · intro hz m
    obtain ⟨w, hwU, hwz⟩ := Metric.mem_closure_iff.1 hz (1 / ((m : ℝ) + 1)) (by positivity)
    have hO : IsOpen (U ∩ ball z (1 / ((m : ℝ) + 1))) := hU.inter isOpen_ball
    obtain ⟨d, hdD, hdB⟩ := hD.exists_mem_open hO ⟨w, hwU, by rw [mem_ball, dist_comm]; exact hwz⟩
    exact ⟨d, hdD, hdB.1, by rw [dist_comm]; exact mem_ball.1 hdB.2⟩
  · intro h
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨d, _, hdU, hd⟩ := h m
    exact ⟨d, hdU, lt_trans hd hm⟩

/-- The countable-coordinate form of `closedBall p r ⊆ U`: some `1/(n+1)`-enlargement of the ball has all its points of
`D` in `cl U`, and membership in `cl U` is the countable test of `mem_closure_iff_of_dense`. It depends on `U` only through
the memberships `d' ∈ U` for `d' ∈ D`. -/
def ProxySub (D U : Set ℂ) (p : ℂ) (r : ℝ) : Prop :=
  ∃ n : ℕ, ∀ d ∈ D, dist d p < r + 1 / ((n : ℝ) + 1) →
    ∀ m : ℕ, ∃ d' ∈ D, d' ∈ U ∧ dist d d' < 1 / ((m : ℝ) + 1)

/-- For a regular open set `U` (`interior (closure U) = U`, the harmonic-ball property of `Λ_t`) and `r ≥ 0`,
`closedBall p r ⊆ U` iff the countable-coordinate proxy `ProxySub D U p r` holds. -/
theorem closedBall_subset_iff_proxy {D U : Set ℂ} (hD : Dense D) (hU : IsOpen U)
    (hreg : interior (closure U) = U) {p : ℂ} {r : ℝ} (hr : 0 ≤ r) :
    closedBall p r ⊆ U ↔ ProxySub D U p r := by
  constructor
  · intro hsub
    obtain ⟨δ, hδ, hcth⟩ := (isCompact_closedBall p r).exists_cthickening_subset_open hU hsub
    rw [cthickening_closedBall hδ.le hr] at hcth
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine ⟨n, fun d hd hdR => ?_⟩
    have hdU : d ∈ U := hcth (by rw [mem_closedBall]; linarith)
    exact (mem_closure_iff_of_dense hD hU d).1 (subset_closure hdU)
  · rintro ⟨n, hn⟩
    have hpos : 0 < r + 1 / ((n : ℝ) + 1) := add_pos_of_nonneg_of_pos hr (by positivity)
    have hOpen : IsOpen (ball p (r + 1 / ((n : ℝ) + 1))) := isOpen_ball
    have hball : ball p (r + 1 / ((n : ℝ) + 1)) ⊆ closure U := by
      intro x hx
      have hx' := hD.open_subset_closure_inter hOpen hx
      exact closure_minimal
        (fun d hd => (mem_closure_iff_of_dense hD hU d).2 (hn d hd.2 (mem_ball.1 hd.1))) isClosed_closure hx'
    have hsub2 : ball p (r + 1 / ((n : ℝ) + 1)) ⊆ U := by
      have h := interior_maximal hball hOpen
      rwa [hreg] at h
    intro y hy
    apply hsub2
    rw [mem_ball]
    have h1 : dist y p ≤ r := mem_closedBall.1 hy
    have h2 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- The witness characterisation of the jump: for an increasing family of open sets `U s` and
`t > 0`, `U_t ≠ ⋃_{0<s<t} U_s` iff some `K` of the cover `𝒦` satisfies `K ⊆ U_t` and `K ⊄ U_q` for all rational `0 < q < t`. -/
theorem strictGap_jump_iff {U : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : MonotoneOn U (Ioi 0)) (hopen : ∀ s : ℝ, 0 < s → IsOpen (U s))
    {D : Set ℂ} (hD : Dense D) :
    U t ≠ ⋃ s ∈ Ioo (0 : ℝ) t, U s ↔
      ∃ K ∈ ratBallCover D, K ⊆ U t ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ K ⊆ U (q : ℝ) := by
  have hsub : (⋃ s ∈ Ioo (0 : ℝ) t, U s) ⊆ U t := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
    have hst : U s ⊆ U t := hmono (Set.mem_Ioi.2 hs.1) (Set.mem_Ioi.2 ht) (le_of_lt hs.2)
    exact hst hxs
  constructor
  · intro hne
    have hnsub : ¬ U t ⊆ ⋃ s ∈ Ioo (0 : ℝ) t, U s := fun h => hne (Subset.antisymm h hsub)
    obtain ⟨x, hxt, hxn⟩ := not_subset.1 hnsub
    obtain ⟨K, hK, hxK, hKV⟩ := ratBallCover_cover hD (U t) (hopen t ht) x hxt
    refine ⟨K, hK, hKV, fun q hq0 hqt hKq => hxn ?_⟩
    exact mem_iUnion₂.2 ⟨(q : ℝ), ⟨hq0, hqt⟩, hKq hxK⟩
  · rintro ⟨K, hK, hKt, hnq⟩ heq
    obtain ⟨⟨p, r⟩, -, hKeq⟩ := hK
    have hKc : IsCompact K := by
      rw [← hKeq]
      exact isCompact_closedBall p _
    have hcover : K ⊆ ⋃ i : Ioo (0 : ℝ) t, U i := by
      intro x hx
      have hx' : x ∈ ⋃ s ∈ Ioo (0 : ℝ) t, U s := heq ▸ hKt hx
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx'
      exact mem_iUnion.2 ⟨⟨s, hs⟩, hxs⟩
    have : Nonempty (Ioo (0 : ℝ) t) := ⟨⟨t / 2, by constructor <;> linarith⟩⟩
    have hmon : Monotone (fun i : Ioo (0 : ℝ) t => U i) := by
      intro i j hij
      exact hmono (Set.mem_Ioi.2 i.2.1) (Set.mem_Ioi.2 j.2.1) (show (i : ℝ) ≤ (j : ℝ) from hij)
    obtain ⟨⟨i, hi⟩, hKi⟩ :=
      hKc.elim_directed_cover (fun i : Ioo (0 : ℝ) t => U i) (fun i => hopen i i.2.1) hcover hmon.directed_le
    obtain ⟨q, hiq, hqt⟩ := exists_rat_btwn hi.2
    have hq0 : (0 : ℝ) < q := lt_trans hi.1 hiq
    have hiq' : U i ⊆ U q := hmono (Set.mem_Ioi.2 hi.1) (Set.mem_Ioi.2 hq0) (le_of_lt hiq)
    exact hnq q hq0 hqt (hKi.trans hiq')

/-- The jump event in countable-coordinate form (B3): for regular increasing open families, the jump at `t` is the
existence of a cover element `closedBall p r` (centre `p ∈ D`, rational radius `r > 0`) inside `U_t` and outside every
`U_q`, `q ∈ ℚ ∩ (0,t)`. Each `K ⊆ U_s` is the proxy `ProxySub`. -/
theorem strictGap_jump_iff_proxy {U : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : MonotoneOn U (Ioi 0)) (hopen : ∀ s : ℝ, 0 < s → IsOpen (U s))
    (hreg : ∀ s : ℝ, 0 < s → interior (closure (U s)) = U s)
    {D : Set ℂ} (hD : Dense D) :
    U t ≠ ⋃ s ∈ Ioo (0 : ℝ) t, U s ↔
      ∃ p ∈ D, ∃ r : ℚ, 0 < r ∧ ProxySub D (U t) p r ∧
        ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ ProxySub D (U q) p r := by
  rw [strictGap_jump_iff ht hmono hopen hD]
  constructor
  · rintro ⟨K, hK, hKt, hnq⟩
    obtain ⟨⟨p, r⟩, ⟨hp, hr⟩, hKeq⟩ := hK
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hKc : K = closedBall p (r : ℝ) := hKeq.symm
    subst hKc
    exact ⟨p, hp, r, hr,
      (closedBall_subset_iff_proxy hD (hopen t ht) (hreg t ht) hr0.le).1 hKt,
      fun q hq0 hqt hq => hnq q hq0 hqt
        ((closedBall_subset_iff_proxy hD (hopen q hq0) (hreg q hq0) hr0.le).2 hq)⟩
  · rintro ⟨p, hp, r, hr, hsub, hnq⟩
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    refine ⟨closedBall p (r : ℝ), ⟨(p, r), ⟨hp, hr⟩, rfl⟩,
      (closedBall_subset_iff_proxy hD (hopen t ht) (hreg t ht) hr0.le).2 hsub,
      fun q hq0 hqt hK => hnq q hq0 hqt
        ((closedBall_subset_iff_proxy hD (hopen q hq0) (hreg q hq0) hr0.le).1 hK)⟩

/-- A set `{ω | c → ω ∈ S}` is measurable for a constant proposition `c` (used for the constant side conditions
`0 < q`, `q < t`, `dist < r`). -/
theorem measurableSet_imp_const {Ω : Type*} [MeasurableSpace Ω] (c : Prop) {S : Set Ω}
    (hS : MeasurableSet S) : MeasurableSet {ω : Ω | c → ω ∈ S} := by
  by_cases hc : c
  · simpa only [hc, true_implies, Set.ofPred_mem_eq] using hS
  · simp only [hc, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

/-- Measurability of the countable-coordinate proxy `ProxySub D (U ω) p r`, in an abstract measurable space: only the
memberships `d ∈ U ω` for the countably many `d ∈ D` enter (B3). -/
theorem measurableSet_proxySub {Ω : Type*} [MeasurableSpace Ω] {D : Set ℂ} (hDc : D.Countable)
    {U : Ω → Set ℂ} (hU : ∀ d ∈ D, MeasurableSet {ω | d ∈ U ω}) (p : ℂ) (r : ℝ) :
    MeasurableSet {ω | ProxySub D (U ω) p r} := by
  have : Countable D := hDc.to_subtype
  have hin : ∀ (d : ℂ) (ε : ℝ), MeasurableSet {ω | ∃ d' ∈ D, d' ∈ U ω ∧ dist d d' < ε} := by
    intro d ε
    have heq : {ω | ∃ d' ∈ D, d' ∈ U ω ∧ dist d d' < ε} =
        ⋃ d' ∈ D, ({ω | d' ∈ U ω} ∩ {_ω | dist d d' < ε}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
    rw [heq]
    exact MeasurableSet.biUnion hDc fun d' hd' => (hU d' hd').inter (MeasurableSet.const _)
  have himp : ∀ (n : ℕ) (d : D),
      MeasurableSet {ω | dist (d : ℂ) p < r + 1 / ((n : ℝ) + 1) →
        ∀ m : ℕ, ∃ d' ∈ D, d' ∈ U ω ∧ dist (d : ℂ) d' < 1 / ((m : ℝ) + 1)} := by
    intro n d
    by_cases hc : dist (d : ℂ) p < r + 1 / ((n : ℝ) + 1)
    · have heq : {ω | dist (d : ℂ) p < r + 1 / ((n : ℝ) + 1) →
          ∀ m : ℕ, ∃ d' ∈ D, d' ∈ U ω ∧ dist (d : ℂ) d' < 1 / ((m : ℝ) + 1)} =
          ⋂ m : ℕ, {ω | ∃ d' ∈ D, d' ∈ U ω ∧ dist (d : ℂ) d' < 1 / ((m : ℝ) + 1)} := by
        ext ω
        simp only [mem_ofPred_eq, mem_iInter]
        exact ⟨fun h m => h hc m, fun h _ m => h m⟩
      rw [heq]
      exact MeasurableSet.iInter fun m => hin _ _
    · have heq : {ω | dist (d : ℂ) p < r + 1 / ((n : ℝ) + 1) →
          ∀ m : ℕ, ∃ d' ∈ D, d' ∈ U ω ∧ dist (d : ℂ) d' < 1 / ((m : ℝ) + 1)} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        intro h
        exact absurd h hc
      rw [heq]
      exact MeasurableSet.univ
  have heq : {ω | ProxySub D (U ω) p r} =
      ⋃ n : ℕ, ⋂ d : D, {ω | dist (d : ℂ) p < r + 1 / ((n : ℝ) + 1) →
        ∀ m : ℕ, ∃ d' ∈ D, d' ∈ U ω ∧ dist (d : ℂ) d' < 1 / ((m : ℝ) + 1)} := by
    ext ω
    simp only [ProxySub, mem_ofPred_eq, mem_iUnion, mem_iInter, Subtype.forall]
  rw [heq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun d => himp n d

/-- The jump event in countable-coordinate form is measurable in an abstract measurable space (B3): it is a countable
Boolean combination of the memberships `d ∈ U ω s`, `d ∈ D`, `s ∈ {t} ∪ ℚ`. -/
theorem measurableSet_strictGapProxyEvent {Ω : Type*} [MeasurableSpace Ω] {D : Set ℂ} (hDc : D.Countable)
    {U : Ω → ℝ → Set ℂ} (hU : ∀ s : ℝ, ∀ d ∈ D, MeasurableSet {ω | d ∈ U ω s}) (t : ℝ) :
    MeasurableSet {ω | ∃ p ∈ D, ∃ r : ℚ, 0 < r ∧ ProxySub D (U ω t) p r ∧
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ ProxySub D (U ω q) p r} := by
  have hpt : ∀ (p : ℂ) (r : ℚ), MeasurableSet {ω | ProxySub D (U ω t) p r ∧
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ ProxySub D (U ω q) p r} := by
    intro p r
    rw [Set.ofPred_and]
    refine (measurableSet_proxySub hDc (U := fun ω => U ω t) (hU t) p r).inter ?_
    have heq : {ω | ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ ProxySub D (U ω q) p r} =
        ⋂ q : ℚ, {ω | 0 < (q : ℝ) → (q : ℝ) < t → ¬ ProxySub D (U ω q) p r} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact MeasurableSet.iInter fun q => measurableSet_imp_const _
      (measurableSet_imp_const _
        (measurableSet_proxySub hDc (U := fun ω => U ω q) (hU q) p r).compl)
  have heq2 : {ω | ∃ p ∈ D, ∃ r : ℚ, 0 < r ∧ ProxySub D (U ω t) p r ∧
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ ProxySub D (U ω q) p r} =
      ⋃ p ∈ D, ⋃ r ∈ {r : ℚ | 0 < r}, {ω | ProxySub D (U ω t) p r ∧
        ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → ¬ ProxySub D (U ω q) p r} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [heq2]
  exact MeasurableSet.biUnion hDc fun p _ =>
    MeasurableSet.biUnion (Set.to_countable _) fun r _ => hpt p r

end MatedCRT
