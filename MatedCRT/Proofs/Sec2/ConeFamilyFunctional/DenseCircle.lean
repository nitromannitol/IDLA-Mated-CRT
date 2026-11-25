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

theorem tendsto_idxPt_roundIdx (r : ℝ) (z : ℂ) :
    Tendsto (fun n => idxPt (roundIdx n r z)) atTop (𝓝 (r, z)) := by
  have h : Tendsto (fun n : ℕ => (2 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
    rw [mul_zero] at h0
    refine h0.congr fun n => ?_
    rw [one_div, inv_pow, div_eq_mul_inv]
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

end ConeFamilyFunctional

end MatedCRT
