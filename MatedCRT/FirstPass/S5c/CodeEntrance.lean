import MatedCRT.FirstPass.S2g.LawCode

/-!
# FIRST PASS, Lemma 5.3 (three-inputs A4): the entrance event is a function of the global family code

Deterministic part. For a family `F : ℝ → Set ℂ` of open sets indexed by positive times, which is increasing,
regular open (`IsRegularOpen`, Theorem 2.3(a)) and Hausdorff continuous (Theorem 2.3(b)), the earlier clusters
`V_t = ⋃_{0 < q < t, q rational} F q` determine `F t` by `F t = int cl V_t` (Hausdorff continuity from the left).
Hence every compact-inclusion event at real time `t` is a countable Boolean combination of the rational-time
bits `(q, w) ↦ [w ∈ F q]`, which is the global family code `globalCode` (Lemma 2.6).
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Set Metric Topology HarmonicBalls

/-- The regularity of a family of harmonic balls used by the entrance argument: open, increasing, regular open, and
left approximation: every point of `F t` is a limit of points of `F s`, `s ↑ t` (the consequence of Hausdorff
continuity on `(0, ∞)`, Theorem 2.3(b), `leftApprox_of_hausdorff`; this form is stable under the scaling
`x ↦ R x`, which the Hausdorff distance is not stated for). -/
structure GoodFamily (F : ℝ → Set ℂ) : Prop where
  isOpen : ∀ t : ℝ, 0 < t → IsOpen (F t)
  monotoneOn : MonotoneOn F (Ioi 0)
  isRegularOpen : ∀ t : ℝ, 0 < t → IsRegularOpen (F t)
  leftApprox : ∀ t : ℝ, 0 < t → ∀ x ∈ F t, ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[<] t, ∃ y ∈ F s, dist x y < ε

/-- Hausdorff continuity on `(0, ∞)` gives the left approximation of `GoodFamily.leftApprox`. -/
theorem leftApprox_of_hausdorff {F : ℝ → Set ℂ} (hH : HausdorffContinuousOn F (Ioi 0)) :
    ∀ t : ℝ, 0 < t → ∀ x ∈ F t, ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[<] t, ∃ y ∈ F s, dist x y < ε := by
  intro t ht x hx ε hε
  have hev : ∀ᶠ s in 𝓝 t, s ∈ Ioi (0 : ℝ) → hausdorffEDist (F s) (F t) < ENNReal.ofReal ε :=
    eventually_nhdsWithin_iff.1 (hH t ht _ (ENNReal.ofReal_pos.2 hε))
  have hlt : ∀ᶠ s in 𝓝[<] t, s ∈ Ioi (0 : ℝ) → hausdorffEDist (F s) (F t) < ENNReal.ofReal ε :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hev
  have hpos : ∀ᶠ s in 𝓝[<] t, 0 < s := Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds ht)
  refine (hlt.and hpos).mono fun s hs => ?_
  have hd : hausdorffEDist (F s) (F t) < ENNReal.ofReal ε := hs.1 hs.2
  have hinf : infEDist x (F s) < ENNReal.ofReal ε := by
    calc infEDist x (F s) ≤ hausdorffEDist (F t) (F s) := infEDist_le_hausdorffEDist_of_mem hx
      _ = hausdorffEDist (F s) (F t) := hausdorffEDist_comm
      _ < ENNReal.ofReal ε := hd
  obtain ⟨y, hy, hxy⟩ := infEDist_lt_iff.1 hinf
  exact ⟨y, hy, edist_lt_ofReal.1 hxy⟩

/-- The rational times: `ratTime` enumerates `ℚ` (LawCode). Every rational occurs. -/
theorem ratTime_surj (q : ℚ) : ∃ i : ℕ, ratTime i = (q : ℝ) :=
  ⟨Denumerable.eqv ℚ q, congrArg (fun r : ℚ => (r : ℝ)) ((Denumerable.eqv ℚ).symm_apply_apply q)⟩

/-- The earlier clusters `V_t = ⋃_{i : 0 < ratTime i < t} F (ratTime i)` (the rational-time union). -/
def ratUnion (F : ℝ → Set ℂ) (t : ℝ) : Set ℂ :=
  ⋃ i : ℕ, ⋃ _ : 0 < ratTime i ∧ ratTime i < t, F (ratTime i)

theorem mem_ratUnion {F : ℝ → Set ℂ} {t : ℝ} {x : ℂ} :
    x ∈ ratUnion F t ↔ ∃ i : ℕ, (0 < ratTime i ∧ ratTime i < t) ∧ x ∈ F (ratTime i) := by
  simp [ratUnion]

/-- Monotonicity: each earlier cluster lies in the rational-time union. -/
theorem sub_ratUnion {F : ℝ → Set ℂ} (hF : GoodFamily F) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    F s ⊆ ratUnion F t := by
  obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn hst
  obtain ⟨i, hi⟩ := ratTime_surj q
  have hq0 : 0 < ratTime i := by rw [hi]; exact lt_trans hs hsq
  intro x hx
  refine mem_ratUnion.2 ⟨i, ⟨hq0, by rw [hi]; exact hqt⟩, ?_⟩
  have hmono : F s ⊆ F (ratTime i) :=
    hF.monotoneOn (show s ∈ Ioi 0 from hs) (show ratTime i ∈ Ioi 0 from hq0) (by rw [hi]; exact hsq.le)
  exact hmono hx

/-- The rational-time union is open. -/
theorem isOpen_ratUnion {F : ℝ → Set ℂ} (hF : GoodFamily F) (t : ℝ) : IsOpen (ratUnion F t) := by
  refine isOpen_iUnion fun i => isOpen_iUnion fun h => ?_
  exact hF.isOpen _ h.1

/-- The Hausdorff left limit: every point of `F t` is a limit of points of the earlier clusters. -/
theorem mem_closure_ratUnion {F : ℝ → Set ℂ} (hF : GoodFamily F) {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : x ∈ F t) : x ∈ closure (ratUnion F t) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hlt := hF.leftApprox t ht x hx ε hε
  have hpos : ∀ᶠ s in 𝓝[<] t, 0 < s := Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds ht)
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hlt.and hpos)
  have hlt0 : max l 0 < t := max_lt (show l < t from hl) ht
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt0
  obtain ⟨i, hi⟩ := ratTime_surj q
  have hτ0 : 0 < ratTime i := by rw [hi]; exact lt_of_le_of_lt (le_max_right _ _) hq1
  have hτl : l < ratTime i := by rw [hi]; exact lt_of_le_of_lt (le_max_left _ _) hq1
  have hτt : ratTime i < t := by rw [hi]; exact hq2
  obtain ⟨y, hy, hxy⟩ := (hsub ⟨hτl, hτt⟩).1
  exact ⟨y, mem_ratUnion.2 ⟨i, ⟨hτ0, hτt⟩, hy⟩, hxy⟩

/-- **Deterministic identity (three-inputs A4)**: `F t = int cl V_t` for every `t > 0`. -/
theorem eq_interior_closure_ratUnion {F : ℝ → Set ℂ} (hF : GoodFamily F) {t : ℝ} (ht : 0 < t) :
    F t = interior (closure (ratUnion F t)) := by
  apply Subset.antisymm
  · exact interior_maximal (fun x hx => mem_closure_ratUnion hF ht hx) (hF.isOpen t ht)
  · have hsub : ratUnion F t ⊆ F t := by
      intro x hx
      obtain ⟨i, ⟨h0, h1⟩, hi⟩ := mem_ratUnion.1 hx
      exact hF.monotoneOn (show ratTime i ∈ Ioi 0 from h0) (show t ∈ Ioi 0 from ht) h1.le hi
    calc interior (closure (ratUnion F t)) ⊆ interior (closure (F t)) := interior_mono (closure_mono hsub)
      _ = F t := hF.isRegularOpen t ht

/-- The rational points `ℚ + iℚ` (`ratPoint`, LawCode) are dense in `ℂ`. -/
theorem dense_range_ratPoint : Dense (Set.range ratPoint) := by
  rw [Metric.dense_iff]
  intro z r hr
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - r / 2 < z.re + r / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - r / 2 < z.im + r / 2 by linarith)
  have hj : ratPoint (Denumerable.eqv (ℚ × ℚ) (a, b)) = (a : ℂ) + (b : ℂ) * Complex.I :=
    congrArg (fun p : ℚ × ℚ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
      ((Denumerable.eqv (ℚ × ℚ)).symm_apply_apply (a, b))
  refine ⟨(a : ℂ) + (b : ℂ) * Complex.I, ?_, ⟨_, hj⟩⟩
  rw [Metric.mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
  have h1 : |(a : ℝ) - z.re| < r / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have h2 : |(b : ℝ) - z.im| < r / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ratCast_re, Complex.ratCast_im, mul_zero,
    sub_self, mul_one, zero_add, add_zero]
  linarith

/-- Closure membership through rational points, for an open set `G`: `p ∈ cl G` iff rational points of `G`
approximate `p` at every rational scale. -/
theorem mem_closure_iff_rat {G : Set ℂ} (hG : IsOpen G) {p : ℂ} :
    p ∈ closure G ↔ ∀ m : ℕ, 0 < ratTime m → ∃ j : ℕ, dist (ratPoint j) p < ratTime m ∧ ratPoint j ∈ G := by
  constructor
  · intro hp m hm
    obtain ⟨y, hyG, hpy⟩ := Metric.mem_closure_iff.1 hp (ratTime m / 2) (by linarith)
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hG y hyG
    have hpos : 0 < min η (ratTime m / 2) := lt_min hη (by linarith)
    obtain ⟨w, ⟨j, rfl⟩, hwU⟩ := dense_range_ratPoint.exists_mem_open Metric.isOpen_ball
      ⟨y, Metric.mem_ball_self hpos⟩
    have hd := Metric.mem_ball.1 hwU
    refine ⟨j, ?_, hball (Metric.ball_subset_ball (min_le_left _ _) hwU)⟩
    rw [dist_comm] at hpy
    have := dist_triangle (ratPoint j) y p
    have := min_le_right η (ratTime m / 2)
    linarith
  · intro h
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
    obtain ⟨i, hi⟩ := ratTime_surj q
    obtain ⟨j, hdist, hj⟩ := h i (by rw [hi]; exact hq0)
    refine ⟨ratPoint j, hj, ?_⟩
    rw [dist_comm]
    rw [hi] at hdist
    linarith

/-- Compact sets in an open set are inside a rational-point neighbourhood: a rational scale `ratTime n` with all
rational points within it of `K` lying in `O`. -/
theorem exists_rat_of_sub_open {K O : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty) (hO : IsOpen O)
    (hKO : K ⊆ O) : ∃ n : ℕ, 0 < ratTime n ∧ ∀ j : ℕ, infDist (ratPoint j) K < ratTime n → ratPoint j ∈ O := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hO hKO
  obtain ⟨q, hq0, hqδ⟩ := exists_rat_btwn hδ
  obtain ⟨n, hn⟩ := ratTime_surj q
  refine ⟨n, by rw [hn]; exact hq0, fun j hj => ?_⟩
  obtain ⟨y, hy, hdy⟩ := (Metric.infDist_lt_iff hKne).1 hj
  have hlt : ratTime n < δ := by rw [hn]; exact hqδ
  exact hsub (Metric.mem_cthickening_of_dist_le _ y δ K hy (hdy.trans hlt).le)

/-- Converse: rational points near a compact `K` inside the closure of `S` give `K ⊆ int cl S`. -/
theorem subset_interior_closure_of_rat {K S : Set ℂ} {n : ℕ} (hn : 0 < ratTime n)
    (h : ∀ j : ℕ, infDist (ratPoint j) K < ratTime n → ratPoint j ∈ closure S) :
    K ⊆ interior (closure S) := by
  have hU : IsOpen {z : ℂ | infDist z K < ratTime n} :=
    isOpen_lt (Metric.continuous_infDist_pt K) continuous_const
  have hKU : K ⊆ {z : ℂ | infDist z K < ratTime n} := fun x hx => by
    show infDist x K < ratTime n
    rw [Metric.infDist_zero_of_mem hx]
    exact hn
  have hUS : {z : ℂ | infDist z K < ratTime n} ⊆ closure S := by
    refine (dense_range_ratPoint.open_subset_closure_inter hU).trans (closure_minimal ?_ isClosed_closure)
    rintro z ⟨hzU, j, rfl⟩
    exact h j hzU
  exact hKU.trans (interior_maximal hUS hU)

/-- Compact inclusion in a regular open set is a countable rational-point test (three-inputs (2.1)). -/
theorem sub_regular_iff {K O : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty) (hO : IsOpen O)
    (hreg : interior (closure O) = O) :
    K ⊆ O ↔ ∃ n : ℕ, 0 < ratTime n ∧ ∀ j : ℕ, infDist (ratPoint j) K < ratTime n → ratPoint j ∈ O := by
  constructor
  · intro h
    exact exists_rat_of_sub_open hK hKne hO h
  · rintro ⟨n, hn, h⟩
    have := subset_interior_closure_of_rat hn (fun j hj => subset_closure (h j hj))
    rwa [hreg] at this

/-- Compact inclusion in `F t`, through the earlier clusters: `K ⊆ F t` iff rational points within `ratTime n`
of `K` lie in `cl V_t`. -/
theorem sub_entrance_iff {F : ℝ → Set ℂ} (hF : GoodFamily F) {t : ℝ} (ht : 0 < t) {K : Set ℂ}
    (hK : IsCompact K) (hKne : K.Nonempty) :
    K ⊆ F t ↔ ∃ n : ℕ, 0 < ratTime n ∧
      ∀ j : ℕ, infDist (ratPoint j) K < ratTime n → ratPoint j ∈ closure (ratUnion F t) := by
  rw [eq_interior_closure_ratUnion hF ht]
  constructor
  · intro h
    obtain ⟨n, hn, hj⟩ := exists_rat_of_sub_open hK hKne isOpen_interior h
    exact ⟨n, hn, fun j hj' => interior_subset (hj j hj')⟩
  · rintro ⟨n, hn, h⟩
    exact subset_interior_closure_of_rat hn h

/-- Compactness: a compact set inside the earlier clusters lies inside one of the rational-time clusters. -/
theorem compact_sub_ratUnion_iff {F : ℝ → Set ℂ} (hF : GoodFamily F) {t : ℝ} (ht : 0 < t) {K : Set ℂ}
    (hK : IsCompact K) :
    K ⊆ ratUnion F t ↔ ∃ i : ℕ, (0 < ratTime i ∧ ratTime i < t) ∧ K ⊆ F (ratTime i) := by
  constructor
  · intro hKV
    obtain ⟨q, hq0, hqt⟩ := exists_rat_btwn ht
    obtain ⟨i0, hi0⟩ := ratTime_surj q
    have : Nonempty {i : ℕ // 0 < ratTime i ∧ ratTime i < t} :=
      ⟨⟨i0, by rw [hi0]; exact ⟨hq0, hqt⟩⟩⟩
    have hdir : Directed (· ⊆ ·) (fun i : {i : ℕ // 0 < ratTime i ∧ ratTime i < t} => F (ratTime i.1)) := by
      intro a b
      rcases le_total (ratTime a.1) (ratTime b.1) with h | h
      · exact ⟨b, hF.monotoneOn (show (0 : ℝ) < ratTime a.1 from a.2.1) (show (0 : ℝ) < ratTime b.1 from b.2.1)
          h, subset_refl _⟩
      · exact ⟨a, subset_refl _,
          hF.monotoneOn (show (0 : ℝ) < ratTime b.1 from b.2.1) (show (0 : ℝ) < ratTime a.1 from a.2.1) h⟩
    have hcover : K ⊆ ⋃ i : {i : ℕ // 0 < ratTime i ∧ ratTime i < t}, F (ratTime i.1) := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_ratUnion.1 (hKV hx)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
    obtain ⟨i, hi⟩ := hK.elim_directed_cover (fun i : {i : ℕ // 0 < ratTime i ∧ ratTime i < t} =>
      F (ratTime i.1)) (fun i => hF.isOpen _ i.2.1) hcover hdir
    exact ⟨i.1, i.2, hi⟩
  · rintro ⟨i, hi, hKi⟩ x hx
    exact mem_ratUnion.2 ⟨i, hi, hKi hx⟩

/-- The new-entrance event of a single family at time `t` (three-inputs A2). -/
def EntranceAt (F : ℝ → Set ℂ) (t : ℝ) : Prop :=
  ∃ y ∈ F t, ∀ s ∈ Ioo (0 : ℝ) t, y ∉ F s

/-- The entrance event is a rational-ball event: a closed rational ball lies in `F t` but not in the earlier
clusters (three-inputs A4, the countable form). -/
theorem entrance_iff_ball {F : ℝ → Set ℂ} (hF : GoodFamily F) {t : ℝ} (ht : 0 < t) :
    EntranceAt F t ↔ ∃ k l : ℕ, 0 < ratTime l ∧ closedBall (ratPoint k) (ratTime l) ⊆ F t ∧
      ¬ closedBall (ratPoint k) (ratTime l) ⊆ ratUnion F t := by
  constructor
  · rintro ⟨y, hyF, hnew⟩
    have hyV : y ∉ ratUnion F t := by
      intro hy
      obtain ⟨i, ⟨h0, h1⟩, hi⟩ := mem_ratUnion.1 hy
      exact hnew (ratTime i) ⟨h0, h1⟩ hi
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hF.isOpen t ht) y hyF
    obtain ⟨w, ⟨k, rfl⟩, hwU⟩ := dense_range_ratPoint.exists_mem_open Metric.isOpen_ball
      ⟨y, Metric.mem_ball_self (by linarith : (0 : ℝ) < ε / 4)⟩
    have hd := Metric.mem_ball.1 hwU
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show dist (ratPoint k) y < ε / 2 by linarith)
    obtain ⟨l, hl⟩ := ratTime_surj q
    have hlq : ratTime l = q := hl
    refine ⟨k, l, ?_, ?_, ?_⟩
    · rw [hlq]; exact lt_of_le_of_lt dist_nonneg hq1
    · intro z hz
      apply hball
      rw [Metric.mem_ball]
      have hz' := mem_closedBall.1 hz
      have htri := dist_triangle z (ratPoint k) y
      rw [hlq] at hz'
      linarith
    · intro hsub
      apply hyV
      apply hsub
      rw [mem_closedBall, dist_comm]
      rw [hlq] at *
      linarith
  · rintro ⟨k, l, _, hsub, hnsub⟩
    obtain ⟨y, hyB, hyV⟩ := Set.not_subset.1 hnsub
    exact ⟨y, hsub hyB, fun s hs hys => hyV (sub_ratUnion hF hs.1 hs.2 hys)⟩

/-- The rational-point formula for "the closed rational ball `B̄_{k,l}` lies in `F t`", from the bits `B i j`
("rational time `i` cluster contains rational point `j`", with `0 < ratTime i` built in). -/
def InsideB (B : ℕ → ℕ → Prop) (t : ℝ) (k l : ℕ) : Prop :=
  ∃ n : ℕ, 0 < ratTime n ∧ ∀ j : ℕ, infDist (ratPoint j) (closedBall (ratPoint k) (ratTime l)) < ratTime n →
    ∀ m : ℕ, 0 < ratTime m → ∃ j' : ℕ, dist (ratPoint j') (ratPoint j) < ratTime m ∧
      ∃ i : ℕ, (0 < ratTime i ∧ ratTime i < t) ∧ B i j'

/-- The rational-point formula for "the closed rational ball `B̄_{k,l}` lies in the rational-time cluster `F (ratTime i)`". -/
def SubB (B : ℕ → ℕ → Prop) (k l i : ℕ) : Prop :=
  ∃ n : ℕ, 0 < ratTime n ∧ ∀ j : ℕ, infDist (ratPoint j) (closedBall (ratPoint k) (ratTime l)) < ratTime n → B i j

/-- The entrance event as a countable formula in the bits `B` (three-inputs A4). -/
def EntranceB (B : ℕ → ℕ → Prop) (t : ℝ) : Prop :=
  ∃ k l : ℕ, 0 < ratTime l ∧ InsideB B t k l ∧ ∀ i : ℕ, 0 < ratTime i → ratTime i < t → ¬ SubB B k l i

/-- **The entrance event is a function of the global family code (deterministic form).** For a good family `F`,
the new-entrance event at `t` is exactly the countable formula `EntranceB` in the bits
`(i, j) ↦ 0 < ratTime i ∧ ratPoint j ∈ F (ratTime i)`, which is `globalCode F` (LawCode). -/
theorem entrance_iff_B {F : ℝ → Set ℂ} (hF : GoodFamily F) {t : ℝ} (ht : 0 < t) :
    EntranceAt F t ↔ EntranceB (fun i j => 0 < ratTime i ∧ ratPoint j ∈ F (ratTime i)) t := by
  rw [entrance_iff_ball hF ht]
  constructor
  · rintro ⟨k, l, hl, hsub, hnsub⟩
    have hK : IsCompact (closedBall (ratPoint k) (ratTime l)) := isCompact_closedBall _ _
    have hKne : (closedBall (ratPoint k) (ratTime l)).Nonempty :=
      ⟨ratPoint k, mem_closedBall_self hl.le⟩
    refine ⟨k, l, hl, ?_, ?_⟩
    · obtain ⟨n, hn, hj⟩ := (sub_entrance_iff hF ht hK hKne).1 hsub
      refine ⟨n, hn, fun j hjn m hm => ?_⟩
      obtain ⟨j', hd, hV⟩ := (mem_closure_iff_rat (isOpen_ratUnion hF t)).1 (hj j hjn) m hm
      obtain ⟨i, hi, hi'⟩ := mem_ratUnion.1 hV
      exact ⟨j', hd, i, hi, hi.1, hi'⟩
    · intro i hi0 hit hS
      obtain ⟨n, hn, hj⟩ := hS
      apply hnsub
      rw [compact_sub_ratUnion_iff hF ht hK]
      exact ⟨i, ⟨hi0, hit⟩, (sub_regular_iff hK hKne (hF.isOpen _ hi0) (hF.isRegularOpen _ hi0)).2
        ⟨n, hn, fun j hjn => (hj j hjn).2⟩⟩
  · rintro ⟨k, l, hl, ⟨n, hn, hj⟩, hnot⟩
    have hK : IsCompact (closedBall (ratPoint k) (ratTime l)) := isCompact_closedBall _ _
    have hKne : (closedBall (ratPoint k) (ratTime l)).Nonempty :=
      ⟨ratPoint k, mem_closedBall_self hl.le⟩
    refine ⟨k, l, hl, ?_, ?_⟩
    · refine (sub_entrance_iff hF ht hK hKne).2 ⟨n, hn, fun j hjn => ?_⟩
      refine (mem_closure_iff_rat (isOpen_ratUnion hF t)).2 (fun m hm => ?_)
      obtain ⟨j', hd, i, hi, _, hi'⟩ := hj j hjn m hm
      exact ⟨j', hd, mem_ratUnion.2 ⟨i, hi, hi'⟩⟩
    · intro hKV
      rw [compact_sub_ratUnion_iff hF ht hK] at hKV
      obtain ⟨i, hi, hKi⟩ := hKV
      obtain ⟨n', hn', hj'⟩ := (sub_regular_iff hK hKne (hF.isOpen _ hi.1) (hF.isRegularOpen _ hi.1)).1 hKi
      exact hnot i hi.1 hi.2 ⟨n', hn', fun j hjn => ⟨hi.1, hj' j hjn⟩⟩

/-! ### Measurability of the countable formula in the code space `ℕ × ℕ → Bool` -/

section CodeMeasurable

/-- Closure rules for the σ-algebra of sets `{c | P c}` of the code space. -/
theorem good_const (p : Prop) : MeasurableSet {_c : ℕ × ℕ → Bool | p} :=
  MeasurableSet.const p

theorem good_bit (i j : ℕ) : MeasurableSet {c : ℕ × ℕ → Bool | c (i, j) = true} :=
  (measurableSet_singleton true).preimage (measurable_pi_apply (i, j))

theorem good_and {P Q : (ℕ × ℕ → Bool) → Prop} (hP : MeasurableSet {c | P c}) (hQ : MeasurableSet {c | Q c}) :
    MeasurableSet {c | P c ∧ Q c} :=
  hP.inter hQ

theorem good_not {P : (ℕ × ℕ → Bool) → Prop} (hP : MeasurableSet {c | P c}) :
    MeasurableSet {c | ¬ P c} :=
  hP.compl

theorem good_imp {P Q : (ℕ × ℕ → Bool) → Prop} (hP : MeasurableSet {c | P c}) (hQ : MeasurableSet {c | Q c}) :
    MeasurableSet {c | P c → Q c} := by
  have h : {c | P c → Q c} = {c | ¬ P c} ∪ {c | Q c} := by
    ext c
    simp only [Set.mem_union, imp_iff_not_or]; rfl
  rw [h]
  exact (good_not hP).union hQ

theorem good_exists {ι : Type} [Countable ι] {P : ι → (ℕ × ℕ → Bool) → Prop}
    (h : ∀ i, MeasurableSet {c | P i c}) : MeasurableSet {c | ∃ i, P i c} := by
  have e : {c | ∃ i, P i c} = ⋃ i, {c | P i c} := by
    ext c
    simp
  rw [e]
  exact MeasurableSet.iUnion h

theorem good_forall {ι : Type} [Countable ι] {P : ι → (ℕ × ℕ → Bool) → Prop}
    (h : ∀ i, MeasurableSet {c | P i c}) : MeasurableSet {c | ∀ i, P i c} := by
  have e : {c | ∀ i, P i c} = ⋂ i, {c | P i c} := by
    ext c
    simp
  rw [e]
  exact MeasurableSet.iInter h

/-- The sets `{c | SubB (bit c) k l i}` are measurable in the code. -/
theorem good_sub (k l i : ℕ) :
    MeasurableSet {c : ℕ × ℕ → Bool | SubB (fun i j => c (i, j) = true) k l i} := by
  refine good_exists fun n => good_and (good_const _) (good_forall fun j => good_imp (good_const _) ?_)
  exact good_bit i j

/-- The sets `{c | InsideB (bit c) t k l}` are measurable in the code. -/
theorem good_inside (t : ℝ) (k l : ℕ) :
    MeasurableSet {c : ℕ × ℕ → Bool | InsideB (fun i j => c (i, j) = true) t k l} := by
  refine good_exists fun n => good_and (good_const _) (good_forall fun j => good_imp (good_const _)
    (good_forall fun m => good_imp (good_const _) (good_exists fun j' => good_and (good_const _)
      (good_exists fun i => good_and (good_const _) (good_bit i j')))))

/-- **The entrance event is measurable in the global family code** (three-inputs A4): for each `t`, the set of
codes `c` with `EntranceB (bit c) t` is measurable in the product σ-algebra on `ℕ × ℕ → Bool`. -/
theorem measurableSet_entranceB (t : ℝ) :
    MeasurableSet {c : ℕ × ℕ → Bool | EntranceB (fun i j => c (i, j) = true) t} := by
  refine good_exists fun k => good_exists fun l => good_and (good_const _) (good_and (good_inside t k l) ?_)
  exact good_forall fun i => good_imp (good_const _) (good_imp (good_const _) (good_not (good_sub k l i)))

end CodeMeasurable

end MatedCRT.S5c
