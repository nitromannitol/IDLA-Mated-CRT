import MatedCRT.FirstPass.S2y.LateralBilin250

/-!
# A jointly measurable version of the circle-average process in the centre (fp-S2y-decoder-250, z8; chat 250 §1.3)

For a fixed radius `ε > 0`, `z ↦ h_ε(z) = hcirc ω ε z` is a.s. continuous. Its dyadic approximations (evaluate at the
dyadic grid point of the cell containing `z`, indexed by the countable set `ℤ × ℤ`) are jointly measurable, and their
`limsup` is a jointly measurable version equal to `hcirc ω ε z` for every `z` on the continuity event. This is the
two-dimensional analogue of `CirclePairing.radialVersion` (Proofs/Measurability/ConePairing.lean).
-/

open MeasureTheory Filter Topology Set HarmonicBalls

namespace MatedCRT.LQGMeasure

/-- The grid index `(⌈Re z · 2ⁿ⌉, ⌈Im z · 2ⁿ⌉)` of `z` at level `n`. -/
noncomputable def gridIdx (n : ℕ) (z : ℂ) : ℤ × ℤ := (⌈z.re * 2 ^ n⌉, ⌈z.im * 2 ^ n⌉)

/-- The dyadic point `m / 2ⁿ` of a grid index `m`. -/
noncomputable def gridPt (n : ℕ) (m : ℤ × ℤ) : ℂ := ⟨(m.1 : ℝ) / 2 ^ n, (m.2 : ℝ) / 2 ^ n⟩

lemma measurable_gridIdx (n : ℕ) : Measurable (gridIdx n) := by
  unfold gridIdx
  exact (Int.measurable_ceil.comp (Complex.measurable_re.mul_const _)).prodMk
    (Int.measurable_ceil.comp (Complex.measurable_im.mul_const _))

/-- `|⌈x 2ⁿ⌉ / 2ⁿ - x| ≤ 2⁻ⁿ`. -/
lemma abs_ceil_div_sub_le (n : ℕ) (x : ℝ) : |(⌈x * 2 ^ n⌉ : ℝ) / 2 ^ n - x| ≤ (2⁻¹ : ℝ) ^ n := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have a1 : x * 2 ^ n ≤ (⌈x * 2 ^ n⌉ : ℝ) := Int.le_ceil _
  have a2 : (⌈x * 2 ^ n⌉ : ℝ) < x * 2 ^ n + 1 := Int.ceil_lt_add_one _
  have hq : (⌈x * 2 ^ n⌉ : ℝ) / 2 ^ n - x = ((⌈x * 2 ^ n⌉ : ℝ) - x * 2 ^ n) / 2 ^ n := by
    field_simp
  have e : (2⁻¹ : ℝ) ^ n = 1 / 2 ^ n := by rw [inv_pow, one_div]
  rw [hq, abs_div, abs_of_pos hpos, e]
  apply div_le_div_of_nonneg_right _ hpos.le
  rw [abs_le]
  constructor <;> linarith

/-- `‖gridPt n (gridIdx n z) - z‖ ≤ 2 · 2⁻ⁿ`. -/
lemma norm_gridPt_sub_le (n : ℕ) (z : ℂ) : ‖gridPt n (gridIdx n z) - z‖ ≤ 2 * (2⁻¹ : ℝ) ^ n := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hr : (gridPt n (gridIdx n z) - z).re = (⌈z.re * 2 ^ n⌉ : ℝ) / 2 ^ n - z.re := by
    simp [gridPt, gridIdx]
  have hi : (gridPt n (gridIdx n z) - z).im = (⌈z.im * 2 ^ n⌉ : ℝ) / 2 ^ n - z.im := by
    simp [gridPt, gridIdx]
  rw [hr, hi]
  linarith [abs_ceil_div_sub_le n z.re, abs_ceil_div_sub_le n z.im]

lemma tendsto_gridPt (z : ℂ) : Tendsto (fun n : ℕ => gridPt n (gridIdx n z)) atTop (𝓝 z) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hlim : Tendsto (fun n : ℕ => 2 * (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).const_mul 2
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => norm_gridPt_sub_le n z) hlim

variable {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The dyadic approximation of `z ↦ hcirc ω ε z` at level `n`. -/
noncomputable def circleApprox (hcirc : Ω → ℝ → ℂ → ℝ) (ε : ℝ) (n : ℕ) (ω : Ω) (z : ℂ) : ℝ :=
  hcirc ω ε (gridPt n (gridIdx n z))

/-- The jointly measurable version `limsup_n` of the circle-average process `z ↦ hcirc ω ε z`. -/
noncomputable def pointVersion (hcirc : Ω → ℝ → ℂ → ℝ) (ε : ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  limsup (fun n => circleApprox hcirc ε n ω z) atTop

lemma measurable_circleApprox (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) : Measurable (fun p : Ω × ℂ => circleApprox hcirc ε n p.1 p.2) := by
  have hG : Measurable (fun q : Ω × (ℤ × ℤ) => hcirc q.1 ε (gridPt n q.2)) :=
    measurable_from_prod_countable_left fun m => hmc ε (gridPt n m) hε
  exact hG.comp (measurable_fst.prodMk ((measurable_gridIdx n).comp measurable_snd))

lemma measurable_pointVersion (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun p : Ω × ℂ => pointVersion hcirc ε p.1 p.2) :=
  Measurable.limsup fun n => measurable_circleApprox hmc hε n

omit [MeasurableSpace Ω] in
/-- On the continuity event, `pointVersion` is the circle average at every point. -/
lemma pointVersion_eq {ω : Ω} {ε : ℝ} (hc : ContinuousOn (fun z : ℂ => hcirc ω ε z) univ) (z : ℂ) :
    pointVersion hcirc ε ω z = hcirc ω ε z := by
  have hcz : ContinuousAt (fun w : ℂ => hcirc ω ε w) z :=
    hc.continuousAt (isOpen_univ.mem_nhds (mem_univ z))
  have ht : Tendsto (fun n => circleApprox hcirc ε n ω z) atTop (𝓝 (hcirc ω ε z)) :=
    hcz.tendsto.comp (tendsto_gridPt z)
  exact ht.limsup_eq

omit [MeasurableSpace Ω] in
lemma continuousOn_circle_center {ω : Ω} {ε : ℝ} (hω : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2)
    (Ioi 0 ×ˢ univ)) (hε : 0 < ε) : ContinuousOn (fun z : ℂ => hcirc ω ε z) univ :=
  hω.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => ⟨hε, mem_univ _⟩)

/-- A.s. the jointly measurable version agrees with the circle average at every point. -/
lemma ae_pointVersion_eq {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) : ∀ᵐ ω ∂P, ∀ z : ℂ, pointVersion hcirc ε ω z = hcirc ω ε z := by
  filter_upwards [h.ae_continuousOn_circle] with ω hω
  exact fun z => pointVersion_eq (continuousOn_circle_center hω hε) z

end MatedCRT.LQGMeasure
