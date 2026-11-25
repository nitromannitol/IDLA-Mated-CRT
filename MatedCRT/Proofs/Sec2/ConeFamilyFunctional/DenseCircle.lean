import MatedCRT.Defs.QuantumCone
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Circle average processes through their values at rational points

A continuous circle average process `(r, z) ↦ c_r(z)` on `(0, ∞) × ℂ` is determined by its values at the points
`(q, a + b i)` with `q, a, b ∈ ℚ`, `q > 0`. The space `DenseCircle = ℚ × ℚ × ℚ → ℝ` of such values is a countable
product of copies of `ℝ`, hence standard Borel.

* `restrictDense`: the values of a process at the rational points (Borel for the product σ-algebra).
* `extend y r z`: the upper limit of the values of `y` at the dyadic points `roundIdx n r z` above and to the left of
  `(r, z)`; for a continuous process it returns the process (`extend_restrictDense`).
* `LocUnifCont`: a Borel set of `y`, local uniform continuity on the rational points, which contains the values of every
  continuous process (`restrictDense_mem_locUnifCont`) and on which `extend y` is continuous on `(0, ∞) × ℂ`
  (`continuousOn_extend`).
* `measurable_extend`: `(y, r, z) ↦ extend y r z` is jointly Borel.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

namespace ConeFamilyFunctional

/-- Indices of the rational points `(q, a + b i)`. -/
abbrev Idx : Type := ℚ × ℚ × ℚ

/-- The point `(q, a + b i)` of the index `(q, a, b)`. -/
def idxPt (i : Idx) : ℝ × ℂ := ((i.1 : ℝ), ⟨i.2.1, i.2.2⟩)

/-- Values at the rational points. -/
abbrev DenseCircle : Type := Idx → ℝ

/-- The values of a process on `(0, ∞) × ℂ` at the rational points (`0` at the indices with `q ≤ 0`). -/
noncomputable def restrictDense (x : Ioi (0 : ℝ) × ℂ → ℝ) : DenseCircle :=
  fun i => if h : 0 < (i.1 : ℝ) then x (⟨i.1, h⟩, ⟨i.2.1, i.2.2⟩) else 0

theorem measurable_restrictDense : Measurable restrictDense := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : 0 < (i.1 : ℝ)
  · simp only [restrictDense, h, dite_true]
    exact measurable_pi_apply _
  · simp only [restrictDense, h, dite_false]
    exact measurable_const

/-- The dyadic point of level `n` above and to the left of `(r, z)`. -/
noncomputable def roundIdx (n : ℕ) (r : ℝ) (z : ℂ) : Idx :=
  ((⌈r * 2 ^ n⌉ : ℚ) / 2 ^ n, (⌊z.re * 2 ^ n⌋ : ℚ) / 2 ^ n, (⌊z.im * 2 ^ n⌋ : ℚ) / 2 ^ n)

theorem roundIdx_fst_ge (n : ℕ) (r : ℝ) (z : ℂ) : r ≤ ((roundIdx n r z).1 : ℝ) := by
  simp only [roundIdx]
  push_cast
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

theorem roundIdx_fst_le (n : ℕ) (r : ℝ) (z : ℂ) : ((roundIdx n r z).1 : ℝ) ≤ r + 1 / 2 ^ n := by
  simp only [roundIdx]
  push_cast
  rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  exact (Int.ceil_lt_add_one _).le

theorem abs_floor_div_sub_le (n : ℕ) (a : ℝ) : |((⌊a * 2 ^ n⌋ : ℚ) / 2 ^ n : ℚ) - a| ≤ 1 / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hf1 := Int.floor_le (a * 2 ^ n)
  have hf2 := Int.lt_floor_add_one (a * 2 ^ n)
  have key : (((⌊a * 2 ^ n⌋ : ℚ) / 2 ^ n : ℚ) : ℝ) - a = -((a * 2 ^ n - ⌊a * 2 ^ n⌋) / 2 ^ n) := by
    push_cast
    field_simp
    ring
  rw [key, abs_neg, abs_of_nonneg (div_nonneg (by linarith) h2.le)]
  exact div_le_div_of_nonneg_right (by linarith) h2.le

/-- The dyadic point of level `n` is within `2 / 2^n` of `(r, z)`. -/
theorem dist_idxPt_roundIdx_le (n : ℕ) (r : ℝ) (z : ℂ) : dist (idxPt (roundIdx n r z)) (r, z) ≤ 2 / 2 ^ n := by
  have h1 := roundIdx_fst_ge n r z
  have h2 := roundIdx_fst_le n r z
  have hre := abs_floor_div_sub_le n z.re
  have him := abs_floor_div_sub_le n z.im
  rw [Prod.dist_eq, max_le_iff]
  constructor
  · show |((roundIdx n r z).1 : ℝ) - r| ≤ 2 / 2 ^ n
    have h3 : (1 : ℝ) / 2 ^ n ≤ 2 / 2 ^ n := div_le_div_of_nonneg_right (by norm_num) (by positivity)
    rw [abs_le]
    constructor <;> linarith [(by positivity : (0 : ℝ) ≤ 1 / 2 ^ n)]
  · rw [Complex.dist_eq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [idxPt, roundIdx, Complex.sub_re, Complex.sub_im]
    have : (2 : ℝ) / 2 ^ n = 1 / 2 ^ n + 1 / 2 ^ n := by ring
    rw [this]
    exact add_le_add hre him

theorem tendsto_two_div_pow : Tendsto (fun n : ℕ => (2 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
  have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  rw [mul_zero] at h0
  refine h0.congr fun n => ?_
  rw [one_div, inv_pow, div_eq_mul_inv]

theorem tendsto_idxPt_roundIdx (r : ℝ) (z : ℂ) :
    Tendsto (fun n => idxPt (roundIdx n r z)) atTop (𝓝 (r, z)) := by
  have h := tendsto_two_div_pow
  exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg)
    (fun n => dist_idxPt_roundIdx_le n r z) h)

/-- The extension of the values at rational points: the upper limit of the values at the dyadic points. -/
noncomputable def extend (y : DenseCircle) (r : ℝ) (z : ℂ) : ℝ :=
  if 0 < r then limsup (fun n => y (roundIdx n r z)) atTop else 0

theorem measurable_roundIdx (n : ℕ) : Measurable fun p : ℝ × ℂ => roundIdx n p.1 p.2 := by
  have hq : ∀ f : ℝ × ℂ → ℤ, Measurable f → Measurable fun a => ((f a : ℚ) / 2 ^ n : ℚ) :=
    fun f hf => (measurable_from_top (f := fun k : ℤ => ((k : ℚ) / 2 ^ n : ℚ))).comp hf
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact hq _ (measurable_fst.mul_const _).ceil
  · exact hq _ ((Complex.measurable_re.comp measurable_snd).mul_const _).floor
  · exact hq _ ((Complex.measurable_im.comp measurable_snd).mul_const _).floor

/-- `(y, r, z) ↦ extend y r z` is jointly Borel. -/
theorem measurable_extend : Measurable fun p : DenseCircle × ℝ × ℂ => extend p.1 p.2.1 p.2.2 := by
  have hev : Measurable fun q : DenseCircle × Idx => q.1 q.2 :=
    measurable_from_prod_countable_left fun i => measurable_pi_apply i
  have hseq : ∀ n : ℕ, Measurable fun p : DenseCircle × ℝ × ℂ => p.1 (roundIdx n p.2.1 p.2.2) := fun n =>
    hev.comp (measurable_fst.prodMk ((measurable_roundIdx n).comp measurable_snd))
  refine Measurable.ite (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd))
    (Measurable.limsup hseq) measurable_const

/-- The extension of the values of a continuous process at the rational points is the process. -/
theorem extend_restrictDense {c : ℝ → ℂ → ℝ} (hc : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ))
    {r : ℝ} (hr : 0 < r) (z : ℂ) : extend (restrictDense (circleProcess c)) r z = c r z := by
  have hval : ∀ n, restrictDense (circleProcess c) (roundIdx n r z) = c (idxPt (roundIdx n r z)).1
      (idxPt (roundIdx n r z)).2 := by
    intro n
    have hpos : 0 < ((roundIdx n r z).1 : ℝ) := hr.trans_le (roundIdx_fst_ge n r z)
    simp only [restrictDense, hpos, dite_true, circleProcess, idxPt]
  have hlim : Tendsto (fun n => restrictDense (circleProcess c) (roundIdx n r z)) atTop (𝓝 (c r z)) := by
    simp only [hval]
    have hmem : ∀ n, idxPt (roundIdx n r z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) := fun n =>
      ⟨hr.trans_le (roundIdx_fst_ge n r z), mem_univ _⟩
    exact ((hc (r, z) ⟨hr, mem_univ _⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_idxPt_roundIdx r z, Eventually.of_forall hmem⟩))
  simp only [extend, hr, ↓reduceIte]
  exact hlim.limsup_eq

/-! ### Local uniform continuity on the rational points -/

/-- The compact piece `[1/(m+1), m+1] × cl B_{m+1}` of `(0, ∞) × ℂ`. -/
def piece (m : ℕ) : Set (ℝ × ℂ) := Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) ×ˢ closedBall (0 : ℂ) ((m : ℝ) + 1)

/-- Local uniform continuity of the values at the rational points of each compact piece. -/
def LocUnifCont : Set DenseCircle :=
  {y | ∀ m k : ℕ, ∃ l : ℕ, ∀ i j : Idx, idxPt i ∈ piece m → idxPt j ∈ piece m →
    dist (idxPt i) (idxPt j) < 1 / ((l : ℝ) + 1) → |y i - y j| ≤ 1 / ((k : ℝ) + 1)}

theorem measurableSet_locUnifCont : MeasurableSet LocUnifCont := by
  have hij : ∀ (i j : Idx) (P : Prop) (c : ℝ), MeasurableSet {y : DenseCircle | P → |y i - y j| ≤ c} := by
    intro i j P c
    by_cases hP : P
    · simpa [hP] using measurableSet_le ((measurable_pi_apply i).sub (measurable_pi_apply j)).abs measurable_const
    · simp [hP]
  have h := MeasurableSet.iInter fun m : ℕ => MeasurableSet.iInter fun k : ℕ => MeasurableSet.iUnion fun l : ℕ =>
    MeasurableSet.iInter fun i : Idx => MeasurableSet.iInter fun j : Idx =>
      hij i j (idxPt i ∈ piece m ∧ idxPt j ∈ piece m ∧ dist (idxPt i) (idxPt j) < 1 / ((l : ℝ) + 1))
        (1 / ((k : ℝ) + 1))
  convert h using 1
  ext y
  simp only [LocUnifCont, mem_ofPred_eq, mem_iInter, mem_iUnion]
  exact ⟨fun h m k => (h m k).imp fun l hl i j hP => hl i j hP.1 hP.2.1 hP.2.2,
    fun h m k => (h m k).imp fun l hl i j h1 h2 h3 => hl i j ⟨h1, h2, h3⟩⟩

/-- A neighbourhood of a point of `(0, ∞) × ℂ` lies in a compact piece. -/
theorem exists_ball_subset_piece {p : ℝ × ℂ} (hp : 0 < p.1) : ∃ (m : ℕ) (δ : ℝ), 0 < δ ∧ ball p δ ⊆ piece m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / p.1 + p.1 + ‖p.2‖ + 1)
  have hm0 : (0 : ℝ) < m + 1 := by positivity
  refine ⟨m, min (p.1 / 2) 1, lt_min (half_pos hp) one_pos, fun q hq => ?_⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Complex.dist_eq, lt_min_iff, lt_min_iff] at hq
  obtain ⟨⟨h1, h1'⟩, h2, h2'⟩ := hq
  have hr := abs_lt.1 h1
  have hn : ‖q.2‖ ≤ ‖p.2‖ + ‖q.2 - p.2‖ := by
    calc ‖q.2‖ = ‖p.2 + (q.2 - p.2)‖ := by rw [add_sub_cancel]
      _ ≤ ‖p.2‖ + ‖q.2 - p.2‖ := norm_add_le _ _
  have h2p : 2 / p.1 < (m : ℝ) + 1 := by have := norm_nonneg p.2; linarith
  have hinv : 1 / ((m : ℝ) + 1) < p.1 / 2 := by
    rw [div_lt_iff₀ hm0]
    rw [div_lt_iff₀ hp] at h2p
    nlinarith
  have h2pos : 0 ≤ 2 / p.1 := by positivity
  have hpn := norm_nonneg p.2
  have hr' := abs_lt.1 h1'
  refine ⟨⟨by linarith, by linarith⟩, mem_closedBall_zero_iff.2 (by linarith)⟩

/-- The dyadic points of `a` are within `dist a p + 2/2^n` of `p`. -/
theorem dist_idxPt_roundIdx_le' (n : ℕ) (a p : ℝ × ℂ) :
    dist (idxPt (roundIdx n a.1 a.2)) p ≤ dist a p + 2 / 2 ^ n :=
  (dist_triangle _ a p).trans (by rw [add_comm]; exact add_le_add_right (dist_idxPt_roundIdx_le n a.1 a.2) _)

/-- On a locally uniformly continuous `y`, the values at the dyadic points of `a` converge to `extend y a`. -/
theorem tendsto_extend {y : DenseCircle} (hy : y ∈ LocUnifCont) {a : ℝ × ℂ} (ha : 0 < a.1) :
    Tendsto (fun n => y (roundIdx n a.1 a.2)) atTop (𝓝 (extend y a.1 a.2)) := by
  obtain ⟨m, δ, hδ, hball⟩ := exists_ball_subset_piece ha
  have hcauchy : CauchySeq fun n => y (roundIdx n a.1 a.2) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨l, hl⟩ := hy m k
    have hev := (tendsto_order.1 tendsto_two_div_pow).2 (min (δ / 2) (1 / (2 * ((l : ℝ) + 1))))
      (lt_min (half_pos hδ) (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    have hN' := hN N le_rfl
    have hn' := hN n hn
    have hmem : ∀ n', N ≤ n' → idxPt (roundIdx n' a.1 a.2) ∈ piece m := fun n' hn'' => hball (by
      rw [mem_ball]
      have := dist_idxPt_roundIdx_le n' a.1 a.2
      have h3 := hN n' hn''
      linarith [min_le_left (δ / 2) (1 / (2 * ((l : ℝ) + 1)))])
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (hl _ _ (hmem n hn) (hmem N le_rfl) ?_) hk
    have h4 := dist_idxPt_roundIdx_le n a.1 a.2
    have h5 := dist_idxPt_roundIdx_le N a.1 a.2
    have h6 : (1 : ℝ) / (2 * ((l : ℝ) + 1)) + 1 / (2 * ((l : ℝ) + 1)) = 1 / ((l : ℝ) + 1) := by
      field_simp; ring
    calc dist (idxPt (roundIdx n a.1 a.2)) (idxPt (roundIdx N a.1 a.2))
        ≤ dist (idxPt (roundIdx n a.1 a.2)) (a.1, a.2) + dist (a.1, a.2) (idxPt (roundIdx N a.1 a.2)) :=
          dist_triangle _ _ _
      _ < 1 / ((l : ℝ) + 1) := by
          rw [dist_comm (a.1, a.2)]
          linarith [min_le_right (δ / 2) (1 / (2 * ((l : ℝ) + 1)))]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have he : extend y a.1 a.2 = L := by
    simp only [extend, ha, ↓reduceIte]
    exact hL.limsup_eq
  rw [he]
  exact hL

/-- **On locally uniformly continuous values the extension is continuous** on `(0, ∞) × ℂ`. -/
theorem continuousOn_extend {y : DenseCircle} (hy : y ∈ LocUnifCont) :
    ContinuousOn (fun p : ℝ × ℂ => extend y p.1 p.2) (Ioi 0 ×ˢ univ) := by
  rw [Metric.continuousOn_iff]
  intro p hp ε hε
  have hp0 : 0 < p.1 := hp.1
  obtain ⟨m, δ, hδ, hball⟩ := exists_ball_subset_piece hp0
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨l, hl⟩ := hy m k
  set η : ℝ := min (δ / 2) (1 / (4 * ((l : ℝ) + 1))) with hη
  have hη0 : 0 < η := lt_min (half_pos hδ) (by positivity)
  refine ⟨η, hη0, fun a ha hap => ?_⟩
  have ha0 : 0 < a.1 := ha.1
  have hev := (tendsto_order.1 tendsto_two_div_pow).2 η hη0
  have hbound : ∀ᶠ n in atTop, |y (roundIdx n a.1 a.2) - y (roundIdx n p.1 p.2)| ≤ 1 / ((k : ℝ) + 1) := by
    filter_upwards [hev] with n hn
    have h1 := dist_idxPt_roundIdx_le' n a p
    have h2 := dist_idxPt_roundIdx_le' n p p
    rw [dist_self, zero_add] at h2
    have hηδ : η ≤ δ / 2 := min_le_left _ _
    have hηl : η ≤ 1 / (4 * ((l : ℝ) + 1)) := min_le_right _ _
    refine hl _ _ (hball (by rw [mem_ball]; linarith)) (hball (by rw [mem_ball]; linarith)) ?_
    have h3 : (1 : ℝ) / (4 * ((l : ℝ) + 1)) * 4 = 1 / ((l : ℝ) + 1) := by field_simp
    calc dist (idxPt (roundIdx n a.1 a.2)) (idxPt (roundIdx n p.1 p.2))
        ≤ dist (idxPt (roundIdx n a.1 a.2)) p + dist p (idxPt (roundIdx n p.1 p.2)) := dist_triangle _ _ _
      _ < 1 / ((l : ℝ) + 1) := by
          rw [dist_comm p]
          have h4 : (2 : ℝ) / 2 ^ n < η := hn
          linarith
  have hlim := ((tendsto_extend hy ha0).sub (tendsto_extend hy hp0)).abs
  have hle : |extend y a.1 a.2 - extend y p.1 p.2| ≤ 1 / ((k : ℝ) + 1) := le_of_tendsto hlim hbound
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hle hk

/-- The values of a continuous process at the rational points are locally uniformly continuous. -/
theorem restrictDense_mem_locUnifCont {c : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ)) : restrictDense (circleProcess c) ∈ LocUnifCont := by
  intro m k
  have hpiece : piece m ⊆ Ioi 0 ×ˢ univ := fun q hq => ⟨lt_of_lt_of_le (by positivity) hq.1.1, mem_univ _⟩
  have hK : IsCompact (piece m) := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous (hc.mono hpiece))
    (1 / ((k : ℝ) + 1)) (by positivity)
  obtain ⟨l, hl⟩ := exists_nat_one_div_lt hδ
  refine ⟨l, fun i j hi hj hij => ?_⟩
  have hi0 : 0 < (i.1 : ℝ) := lt_of_lt_of_le (by positivity) hi.1.1
  have hj0 : 0 < (j.1 : ℝ) := lt_of_lt_of_le (by positivity) hj.1.1
  have h := hu _ hi _ hj (hij.trans hl)
  simp only [restrictDense, hi0, hj0, dite_true, circleProcess]
  rw [Real.dist_eq] at h
  exact h.le

end ConeFamilyFunctional

end MatedCRT
