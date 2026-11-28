import MatedCRT.FirstPass.Derived.LQGMeasureChartSmooth

/-!
# Variable source radii for the smooth approximations of the LQG measure

The deterministic step "variable source radii" in the proof that the coordinate change of the LQG measure holds for all
conformal maps simultaneously at the fixed scales `2^{-k}` (`SheffieldWangDiscConformal`), from the envelope
statement of Sheffield–Wang, *Field-measure correspondence in Liouville quantum gravity almost surely commutes with
all conformal maps simultaneously* (arXiv:1605.06171v2), end of the proof of Theorem 1.2, p. 11. The field enters
only through its pairings `G`.

* `mollDilate q f`: the dilated bump `f_q(v) = q⁻² f(v/q)` ((3.3) with `ε = q`). `isMollifier_mollDilate`;
  `mollConst_mollDilate`: `C_{f_q} = C_f + log q` (substitution in (3.4), and `2π ∫₀¹ f(r) r dr = ∫ f = 1` in
  polar coordinates); `smoothExponent_mollDilate`: the exponent `h̃_s` of `f_q` (§3.2, after (3.4)) is the exponent
  `h̃_{qs}` of `f`.
* `irrational_logb_two_one_third`: `log₂ (1/3)` is irrational.
* `varScaleApprox`: the smooth approximation at the variable source radius `2^{-k} b(z)`.
* `isVagueLimitOn_varScaleApprox`: let `log₂ q` be irrational, and suppose that for every `N ≥ 1` the upper and lower
  envelopes of the smooth approximations over the scales `[2^{-(j+1)/N}, 2^{-j/N}]` (p. 11) converge vaguely in `D` to
  `u_N μ` and `l_N μ` for the bump `f`, and to `u'_N μ`, `l'_N μ` for the bump `f_q`, the four constants tending to
  `1`. Then for every continuous `b > 0` on `D` the approximations at radius `2^{-k} b(z)` converge vaguely in `D`
  to `μ`. For fixed `N`, the open cells of the two grids `N⁻¹ℤ` and `log₂ q + N⁻¹ℤ` cover the line; a finite
  partition of unity places `log₂ b` in one cell on each piece of a test function, and on that piece the density at
  radius `2^{-k} b(z)` lies between the two envelopes of index `kN + m`; then `N → ∞`.

The vague convergence `QuantumZipper.IsVagueLimitOn` is stated with Bochner integrals, which are `0` for a test
function that is not integrable, so the convergence of the envelopes does not say that the envelope measures are
locally finite (in the printed statement they are random Radon measures). The theorem therefore also assumes that the
upper envelopes of both bumps eventually give finite mass to each compact subset of `D` (without such an assumption
the conclusion can fail when `μ = 0`). `eventually_envSup_ne_top` derives this from a bound
`|G(f_ε(z - ·))| ≤ C ε^α` on compact subsets of `D`, and `isVagueLimitOn_varScaleApprox_of_bound` states the theorem
with that bound.
-/

set_option autoImplicit false

noncomputable section

open scoped Classical

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT

namespace LQGMeasureChart

/-! ## The dilated bump -/

/-- The dilated bump `f_q(v) = q⁻² f(v/q)` (Sheffield–Wang (2016), (3.3) with `ε = q`). -/
def mollDilate (q : ℝ) (f : ℂ → ℝ) (v : ℂ) : ℝ :=
  (q ^ 2)⁻¹ * f (v / q)

theorem mollDilate_one (f : ℂ → ℝ) : mollDilate 1 f = f := by
  funext v
  simp [mollDilate]

/-- Scaling the dilated bump: `(f_q)_s = f_{qs}`. -/
theorem mollScale_mollDilate (q s : ℝ) (f : ℂ → ℝ) :
    mollScale (mollDilate q f) s = mollScale f (q * s) := by
  funext v
  simp only [mollScale, mollDilate, div_div, Complex.ofReal_mul]
  rw [mul_comm (s : ℂ) (q : ℂ)]
  ring

private theorem mollifier_eq_zero {f : ℂ → ℝ} (hf : IsMollifier f) {v : ℂ} (hv : 1 ≤ ‖v‖) : f v = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => by
    have h1 := hf.tsupport_subset h
    rw [mem_ball_zero_iff] at h1
    linarith

private theorem mollifier_eq_zero_real {f : ℂ → ℝ} (hf : IsMollifier f) {t : ℝ} (ht : 1 ≤ t) :
    f t = 0 :=
  mollifier_eq_zero hf (by rw [Complex.norm_real, Real.norm_eq_abs]; exact ht.trans (le_abs_self t))

private theorem mollDilate_eq_zero {q : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) (hq0 : 0 < q) {v : ℂ}
    (hv : q ≤ ‖v‖) : mollDilate q f v = 0 := by
  have h : f (v / q) = 0 := by
    refine mollifier_eq_zero hf ?_
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hq0.le, le_div_iff₀ hq0, one_mul]
    exact hv
  simp [mollDilate, h]

/-- The dilated bump `f_q`, `0 < q < 1`, is again a bump function (smooth, nonnegative, radial, supported in the unit
disc, of integral `1`). -/
theorem isMollifier_mollDilate {q : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) (hq0 : 0 < q) (hq1 : q < 1) :
    IsMollifier (mollDilate q f) where
  contDiff := by
    show ContDiff ℝ _ (fun v => (q ^ 2)⁻¹ * f (v / q))
    exact contDiff_const.mul (hf.contDiff.comp (contDiff_id.div_const _))
  nonneg z := mul_nonneg (inv_nonneg.2 (sq_nonneg q)) (hf.nonneg _)
  radial z w hzw := by
    simp only [mollDilate]
    rw [hf.radial (z / q) (w / q) (by rw [norm_div, norm_div, hzw])]
  hasCompactSupport := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) fun v hv =>
    mollDilate_eq_zero hf hq0 (by rw [mem_closedBall_zero_iff, not_le] at hv; linarith)
  tsupport_subset := by
    refine (closure_minimal (fun v hv => ?_) isClosed_closedBall).trans (closedBall_subset_ball hq1)
    rw [mem_closedBall_zero_iff]
    by_contra h
    exact (Function.mem_support.1 hv) (mollDilate_eq_zero hf hq0 (not_le.1 h).le)
  integral_eq_one := by
    have h1 : ∀ v : ℂ, v / (q : ℂ) = q⁻¹ • v := fun v => by
      rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
    show ∫ v, (q ^ 2)⁻¹ * f (v / q) = 1
    simp only [h1]
    rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume f hq0.le,
      Complex.finrank_real_complex, hf.integral_eq_one, smul_eq_mul, mul_one,
      inv_mul_cancel₀ (pow_ne_zero 2 hq0.ne')]

/-- Polar coordinates: `2π ∫₀¹ f(r) r dr = ∫ f = 1` for a bump function. -/
private theorem mollifier_mass {f : ℂ → ℝ} (hf : IsMollifier f) :
    2 * Real.pi * ∫ t in (0 : ℝ)..1, f t * t = 1 := by
  have h1 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f r)
  beta_reduce at h1
  have h0 : ∫ z : ℂ, f (‖z‖ : ℂ) = 1 := by
    rw [← hf.integral_eq_one]
    exact integral_congr_ae (ae_of_all _ fun z => hf.radial (‖z‖ : ℂ) z (by simp))
  have hball : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have h2 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • f (y : ℂ) = ∫ t in (0 : ℝ)..1, f t * t := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      ← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
    · refine integral_congr_ae (ae_of_all _ fun y => ?_)
      show y ^ (2 - 1) • f (y : ℂ) = f y * y
      rw [smul_eq_mul, show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_comm]
    · intro y hy
      have hy1 : 1 ≤ y := not_lt.1 fun h => hy.2 ⟨hy.1, h.le⟩
      rw [mollifier_eq_zero_real hf hy1, zero_mul]
  rw [h0, Complex.finrank_real_complex, hball, h2, nsmul_eq_mul, smul_eq_mul] at h1
  push_cast at h1
  linear_combination -h1

/-- Rescaling an integral over `[0, 1]` by `0 < q ≤ 1` for an integrand vanishing on `[1, ∞)`. -/
private theorem intervalIntegral_comp_div_eq {h : ℝ → ℝ} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hh : ∀ t, 1 ≤ t → h t = 0) : ∫ y in (0 : ℝ)..1, h (y / q) = q * ∫ t in (0 : ℝ)..1, h t := by
  rw [intervalIntegral.integral_comp_div h hq0.ne', zero_div, smul_eq_mul,
    intervalIntegral.integral_of_le (one_div_pos.2 hq0).le, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      (Ioc_subset_Ioc_right (one_le_one_div hq0 hq1))
      fun t ht => hh t (not_lt.1 fun h' => ht.2 ⟨ht.1.1, h'.le⟩)]

private theorem intervalIntegrable_of_abs_le {g : ℝ → ℝ} (hg : AEStronglyMeasurable g volume) {M : ℝ}
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, |g x| ≤ M) : IntervalIntegrable g volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact Measure.integrableOn_of_bounded (by simp) hg
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => by
      rw [Real.norm_eq_abs]; exact hM x (Ioc_subset_Icc_self hx))

private theorem abs_log_max_mul_mul_le_one {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |Real.log (max s t) * s * t| ≤ 1 := by
  have hsm : s ≤ max s t := le_max_left s t
  rcases (hs.1.trans hsm).eq_or_lt with h0 | hpos
  · have hs0 : s = 0 := le_antisymm (hsm.trans h0.symm.le) hs.1
    simp [hs0]
  · have hm1 : max s t ≤ 1 := max_le hs.2 ht.2
    rw [abs_mul, abs_mul, abs_of_nonneg hs.1, abs_of_nonneg ht.1]
    calc |Real.log (max s t)| * s * t ≤ |Real.log (max s t)| * max s t * t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsm (abs_nonneg _)) ht.1
      _ ≤ |Real.log (max s t)| * max s t * 1 :=
          mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (abs_nonneg _) hpos.le)
      _ = |Real.log (max s t) * max s t| := by rw [abs_mul, abs_of_pos hpos, mul_one]
      _ ≤ 1 := (Real.abs_log_mul_self_lt _ hpos hm1).le

/-- **The constant of the dilated bump** (Sheffield–Wang (2016), (3.4)): `C_{f_q} = C_f + log q` for `0 < q ≤ 1`,
by the substitution `x = q x'`, `y = q y'` and `2π ∫₀¹ f(r) r dr = 1`. -/
theorem mollConst_mollDilate {q : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    mollConst (mollDilate q f) = mollConst f + Real.log q := by
  set F : ℝ → ℝ := fun x => f x with hFdef
  have hFc : Continuous F := hf.contDiff.continuous.comp Complex.continuous_ofReal
  have hF0 : ∀ t : ℝ, 1 ≤ t → F t = 0 := fun t ht => mollifier_eq_zero_real hf ht
  obtain ⟨B, hB⟩ := hf.contDiff.continuous.bounded_above_of_compact_support hf.hasCompactSupport
  have hFB : ∀ t, |F t| ≤ B := fun t => by
    have := hB (t : ℂ)
    rwa [Real.norm_eq_abs] at this
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB 0)
  have hmass : 2 * Real.pi * ∫ t in (0 : ℝ)..1, F t * t = 1 := mollifier_mass hf
  set L : ℝ → ℝ → ℝ := fun s t => Real.log (max s t) * F s * F t * s * t with hL
  have hLm : Measurable (Function.uncurry L) :=
    ((((Real.measurable_log.comp (measurable_fst.max measurable_snd)).mul
      (hFc.measurable.comp measurable_fst)).mul (hFc.measurable.comp measurable_snd)).mul
      measurable_fst).mul measurable_snd
  have hLb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |L s t| ≤ B * B := by
    intro s hs t ht
    have e : L s t = (Real.log (max s t) * s * t) * F s * F t := by simp only [hL]; ring
    rw [e, abs_mul, abs_mul]
    calc |Real.log (max s t) * s * t| * |F s| * |F t| ≤ 1 * B * |F t| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (abs_log_max_mul_mul_le_one hs ht) (hFB s) (abs_nonneg _) zero_le_one)
            (abs_nonneg _)
      _ ≤ 1 * B * B := mul_le_mul_of_nonneg_left (hFB t) (by rw [one_mul]; exact hB0)
      _ = B * B := by ring
  have hLint : ∀ s ∈ Icc (0 : ℝ) 1, IntervalIntegrable (L s) volume 0 1 := fun s hs =>
    intervalIntegrable_of_abs_le hLm.of_uncurry_left.aestronglyMeasurable fun t ht => hLb s hs t ht
  have hBint : IntervalIntegrable (fun s => ∫ t in (0 : ℝ)..1, L s t) volume 0 1 := by
    refine intervalIntegrable_of_abs_le (M := B * B) ?_ fun s hs => ?_
    · have e : (fun s => ∫ t in (0 : ℝ)..1, L s t) =
          fun s => ∫ t, Function.uncurry L (s, t) ∂(volume.restrict (Ioc 0 1)) :=
        funext fun s => intervalIntegral.integral_of_le zero_le_one
      rw [e]
      exact hLm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := B * B)
        (f := L s) fun t ht => by
          rw [uIoc_of_le zero_le_one] at ht
          rw [Real.norm_eq_abs]
          exact hLb s hs t (Ioc_subset_Icc_self ht)
      rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at h
      exact h
  set H : ℝ → ℝ → ℝ := fun s t => Real.log (max (q * s) (q * t)) * ((q ^ 2)⁻¹ * F s) *
    ((q ^ 2)⁻¹ * F t) * (q * s) * (q * t) with hH
  have hHs : ∀ s, 1 ≤ s → ∀ t, H s t = 0 := fun s hs t => by simp only [hH, hF0 s hs]; ring
  have hHt : ∀ s t, 1 ≤ t → H s t = 0 := fun s t ht => by simp only [hH, hF0 t ht]; ring
  have step1 : mollConst (mollDilate q f) =
      4 * Real.pi ^ 2 * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, H (x / q) (y / q) := by
    simp only [mollConst]
    congr 1
    refine intervalIntegral.integral_congr fun x _ => intervalIntegral.integral_congr fun y _ => ?_
    have hx : q * (x / q) = x := mul_div_cancel₀ x hq0.ne'
    have hy : q * (y / q) = y := mul_div_cancel₀ y hq0.ne'
    simp only [hH, hx, hy, hFdef, mollDilate, Complex.ofReal_div]
  have step2 : ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, H (x / q) (y / q) =
      ∫ x in (0 : ℝ)..1, q * ∫ t in (0 : ℝ)..1, H (x / q) t :=
    intervalIntegral.integral_congr fun x _ =>
      intervalIntegral_comp_div_eq hq0 hq1 fun t ht => hHt _ t ht
  have step3 : ∫ x in (0 : ℝ)..1, q * ∫ t in (0 : ℝ)..1, H (x / q) t =
      q * ∫ s in (0 : ℝ)..1, q * ∫ t in (0 : ℝ)..1, H s t :=
    intervalIntegral_comp_div_eq (h := fun s => q * ∫ t in (0 : ℝ)..1, H s t) hq0 hq1 fun s hs => by
      simp only [hHs s hs, intervalIntegral.integral_zero, mul_zero]
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      q * (q * H s t) = (Real.log q + Real.log (max s t)) * F s * F t * s * t := by
    intro s hs t _
    simp only [hH]
    rcases (hs.1.trans (le_max_left s t)).eq_or_lt with h0 | hpos
    · have hs0 : s = 0 := le_antisymm ((le_max_left s t).trans h0.symm.le) hs.1
      simp [hs0]
    · rw [← mul_max_of_nonneg _ _ hq0.le, Real.log_mul hq0.ne' hpos.ne']
      have hq2 : (q ^ 2)⁻¹ * q ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hq0.ne')
      calc _ = (Real.log q + Real.log (max s t)) * F s * F t * s * t * ((q ^ 2)⁻¹ * q ^ 2) ^ 2 := by
            ring
        _ = _ := by rw [hq2]; ring
  have step4 : q * ∫ s in (0 : ℝ)..1, q * ∫ t in (0 : ℝ)..1, H s t =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, (Real.log q + Real.log (max s t)) * F s * F t * s * t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    show q * (q * ∫ t in (0 : ℝ)..1, H s t) =
      ∫ t in (0 : ℝ)..1, (Real.log q + Real.log (max s t)) * F s * F t * s * t
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t ht =>
      key s hs t (by rwa [uIcc_of_le zero_le_one] at ht)
  have hA : IntervalIntegrable (fun t => F t * t) volume 0 1 :=
    (hFc.mul continuous_id').intervalIntegrable 0 1
  have step5 : ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, (Real.log q + Real.log (max s t)) * F s * F t * s * t =
      Real.log q * (∫ t in (0 : ℝ)..1, F t * t) * (∫ t in (0 : ℝ)..1, F t * t) +
        ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, L s t := by
    have inner : ∀ s ∈ uIcc (0 : ℝ) 1,
        ∫ t in (0 : ℝ)..1, (Real.log q + Real.log (max s t)) * F s * F t * s * t =
          Real.log q * (F s * s) * (∫ t in (0 : ℝ)..1, F t * t) + ∫ t in (0 : ℝ)..1, L s t := by
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      have h1 : IntervalIntegrable (fun t => Real.log q * (F s * s) * (F t * t)) volume 0 1 :=
        hA.const_mul _
      calc ∫ t in (0 : ℝ)..1, (Real.log q + Real.log (max s t)) * F s * F t * s * t
          = ∫ t in (0 : ℝ)..1, (Real.log q * (F s * s) * (F t * t) + L s t) :=
            intervalIntegral.integral_congr fun t _ => by simp only [hL]; ring
        _ = Real.log q * (F s * s) * (∫ t in (0 : ℝ)..1, F t * t) + ∫ t in (0 : ℝ)..1, L s t := by
            rw [intervalIntegral.integral_add h1 (hLint s hs), intervalIntegral.integral_const_mul]
    have h2 : IntervalIntegrable (fun s => Real.log q * (F s * s) * (∫ t in (0 : ℝ)..1, F t * t))
        volume 0 1 := (hA.const_mul _).mul_const _
    rw [intervalIntegral.integral_congr inner, intervalIntegral.integral_add h2 hBint,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  have hconst : mollConst f = 4 * Real.pi ^ 2 * ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, L s t := rfl
  rw [step1, step2, step3, step4, step5, hconst]
  linear_combination Real.log q * (2 * Real.pi * (∫ t in (0 : ℝ)..1, F t * t) + 1) * hmass

/-- **The exponent of the dilated bump**: `h̃_s` for `f_q` is `h̃_{qs}` for `f` (Sheffield–Wang (2016), §3.2, after
(3.4)), since `(f_q)_s = f_{qs}` and `C_{f_q} = C_f + log q`. -/
theorem smoothExponent_mollDilate {γ q s : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hs : s ≠ 0) (G : (ℂ → ℝ) → ℝ) (z : ℂ) :
    smoothExponent γ (mollDilate q f) G s z = smoothExponent γ f G (q * s) z := by
  simp only [smoothExponent]
  rw [mollScale_mollDilate, mollConst_mollDilate hf hq0 hq1, Real.log_mul hq0.ne' hs]
  ring

/-! ## An irrational logarithm -/

/-- `log₂ (1/3)` is irrational: `(1/3)^n = 2^m` with `n ≥ 1` is impossible (`3^n` is odd). -/
theorem irrational_logb_two_one_third : Irrational (Real.logb 2 (1 / 3)) := by
  rintro ⟨r, hr⟩
  have h2 : (2 : ℝ) ^ (r : ℝ) = 1 / 3 := by
    rw [hr]
    exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have hden : ((2 : ℝ) ^ (r : ℝ)) ^ r.den = (2 : ℝ) ^ r.num := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_intCast]
    congr 1
    exact_mod_cast Rat.mul_den_eq_num r
  rw [h2] at hden
  have hd : r.den ≠ 0 := r.den_ne_zero
  rcases le_or_gt 0 r.num with hn | hn
  · have h1 : (1 : ℝ) ≤ 2 ^ r.num := one_le_zpow₀ (by norm_num) hn
    have h3 : ((1 : ℝ) / 3) ^ r.den < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hd
    linarith
  · obtain ⟨n, hn'⟩ : ∃ n : ℕ, r.num = -((n + 1 : ℕ) : ℤ) := ⟨(-r.num - 1).toNat, by omega⟩
    rw [hn', zpow_neg, zpow_natCast, div_pow, one_pow, one_div, inv_inj] at hden
    have h3 : (3 : ℕ) ^ r.den = 2 ^ (n + 1) := by exact_mod_cast hden
    have hodd : Odd ((3 : ℕ) ^ r.den) := Odd.pow (by decide)
    rw [h3] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)

/-! ## Variable source radii -/

/-- **The smooth approximation at the variable source radius** `2^{-k} b(z)`: the density `e^{h̃_{2^{-k} b(z)}(z)}`
(Sheffield–Wang (2016), §3.2, after (3.4)) at the points `z` with `B̄_{2^{-k} b(z)}(z) ⊆ V`, and `0` elsewhere. -/
def varScaleApprox (γ : ℝ) (f : ℂ → ℝ) (V : Set ℂ) (G : (ℂ → ℝ) → ℝ) (b : ℂ → ℝ) (k : ℕ) : Measure ℂ :=
  volume.withDensity fun z =>
    if closedBall z (HarmonicBalls.dyadicScale k * b z) ⊆ V then
      ENNReal.ofReal (Real.exp (smoothExponent γ f G (HarmonicBalls.dyadicScale k * b z) z))
    else 0

/-- The open cells `(-(m+1)/N, -m/N)`, `m ∈ ℤ`, of the grid `N⁻¹ℤ` and those of the shifted grid `β + N⁻¹ℤ` cover
the line when `β` is irrational: the two grids have no common point. -/
theorem exists_mem_cell_or_mem_shifted_cell {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : Irrational β) (x : ℝ) :
    (∃ m : ℤ, x ∈ Ioo (-((m : ℝ) + 1) / N) (-(m : ℝ) / N)) ∨
      ∃ m : ℤ, x - β ∈ Ioo (-((m : ℝ) + 1) / N) (-(m : ℝ) / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ y : ℝ, (∀ n : ℤ, (n : ℝ) ≠ -y * N) →
      ∃ m : ℤ, y ∈ Ioo (-((m : ℝ) + 1) / N) (-(m : ℝ) / N) := by
    intro y hy
    refine ⟨⌊-y * N⌋, ?_, ?_⟩
    · rw [div_lt_iff₀ hNpos]
      have := Int.lt_floor_add_one (-y * N)
      linarith
    · rw [lt_div_iff₀ hNpos]
      have h3 : (⌊-y * N⌋ : ℝ) < -y * N := lt_of_le_of_ne (Int.floor_le _) (hy _)
      linarith
  by_cases h : ∀ n : ℤ, (n : ℝ) ≠ -x * N
  · exact Or.inl (key x h)
  · push Not at h
    obtain ⟨n, hn⟩ := h
    refine Or.inr (key (x - β) fun n' hn' => hβ ⟨((n' - n : ℤ) : ℚ) / N, ?_⟩)
    push_cast
    rw [div_eq_iff hNpos.ne']
    linarith

/-- On a compact set where `log₂ b - log₂ p` lies in the cell `(-(m+1)/N, -m/N)`, the density at radius `2^{-k} b`
lies, for `k` large, between the lower and upper envelopes of index `m + kN` of the bump `f_p`. -/
private theorem eventually_envelope_sandwich {γ p : ℝ} {f : ℂ → ℝ} {D : Set ℂ} {G : (ℂ → ℝ) → ℝ}
    {b : ℂ → ℝ} (hD : IsOpen D) (hp0 : 0 < p)
    (hexp : ∀ ε, 0 < ε → ∀ z, smoothExponent γ (mollDilate p f) G ε z = smoothExponent γ f G (p * ε) z)
    {N : ℕ} (hN : 1 ≤ N) (m : ℤ) {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D)
    (hb : ContinuousOn b D) (hbpos : ∀ z ∈ D, 0 < b z)
    (hcell : ∀ z ∈ K, Real.logb 2 (b z) - Real.logb 2 p ∈ Ioo (-((m : ℝ) + 1) / N) (-(m : ℝ) / N)) :
    ∀ᶠ k : ℕ in atTop,
      (envInf γ (mollDilate p f) D G N (m + (k : ℤ) * N).toNat).restrict K ≤
          (varScaleApprox γ f D G b k).restrict K ∧
        (varScaleApprox γ f D G b k).restrict K ≤
          (envSup γ (mollDilate p f) D G N (m + (k : ℤ) * N).toNat).restrict K := by
  have two_pos' : (0 : ℝ) < 2 := by norm_num
  have two_ne_one' : (2 : ℝ) ≠ 1 := by norm_num
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_cthickening_subset_open hD hKD
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hb.mono hKD)
  have hdy : Tendsto (fun k : ℕ => HarmonicBalls.dyadicScale k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : ∀ᶠ k : ℕ in atTop, |C| * HarmonicBalls.dyadicScale k < δ := by
    have h := hdy.const_mul |C|
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds hδ)
  have h2 : ∀ᶠ k : ℕ in atTop, (2 : ℝ) ^ (-(m : ℝ) / N) * HarmonicBalls.dyadicScale k < δ := by
    have h := hdy.const_mul ((2 : ℝ) ^ (-(m : ℝ) / N))
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds hδ)
  have h3 : ∀ᶠ k : ℕ in atTop, 0 ≤ m + (k : ℤ) * N := by
    filter_upwards [eventually_ge_atTop m.natAbs] with k hk
    have hkN : (k : ℤ) ≤ k * N := by exact_mod_cast Nat.le_mul_of_pos_right k hN
    generalize (k : ℤ) * N = P at hkN ⊢
    omega
  filter_upwards [h1, h2, h3] with k hk1 hk2 hk3
  set j : ℕ := (m + (k : ℤ) * N).toNat
  have hj : (j : ℝ) = m + k * N := by
    have h : ((j : ℕ) : ℤ) = m + k * N := Int.toNat_of_nonneg hk3
    exact_mod_cast h
  have hdk : 0 < HarmonicBalls.dyadicScale k := HarmonicBalls.dyadicScale_pos k
  have hdyk : HarmonicBalls.dyadicScale k = (2 : ℝ) ^ (-(k : ℝ)) := by
    rw [HarmonicBalls.dyadicScale, Real.rpow_neg two_pos'.le, Real.rpow_natCast, inv_pow]
  have htop : (2 : ℝ) ^ (-(j : ℝ) / N) = (2 : ℝ) ^ (-(m : ℝ) / N) * HarmonicBalls.dyadicScale k := by
    rw [hdyk, ← Real.rpow_add two_pos', hj]
    congr 1
    field_simp
    ring
  have hball1 : ∀ z ∈ K, closedBall z (HarmonicBalls.dyadicScale k * b z) ⊆ D := by
    intro z hz
    have hbC : b z ≤ |C| := by
      have := hC z hz
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self C))
    have hle : HarmonicBalls.dyadicScale k * b z ≤ δ :=
      calc HarmonicBalls.dyadicScale k * b z ≤ HarmonicBalls.dyadicScale k * |C| :=
            mul_le_mul_of_nonneg_left hbC hdk.le
        _ = |C| * HarmonicBalls.dyadicScale k := mul_comm _ _
        _ ≤ δ := hk1.le
    exact (closedBall_subset_closedBall hle).trans ((closedBall_subset_cthickening hz δ).trans hδD)
  have hball2 : ∀ z ∈ K, closedBall z ((2 : ℝ) ^ (-(j : ℝ) / N)) ⊆ D := by
    intro z hz
    have hle : (2 : ℝ) ^ (-(j : ℝ) / N) ≤ δ := by rw [htop]; exact hk2.le
    exact (closedBall_subset_closedBall hle).trans ((closedBall_subset_cthickening hz δ).trans hδD)
  have hmem : ∀ z ∈ K, HarmonicBalls.dyadicScale k * b z / p ∈
      Icc ((2 : ℝ) ^ (-((j : ℝ) + 1) / N)) ((2 : ℝ) ^ (-(j : ℝ) / N)) := by
    intro z hz
    have hbz : 0 < b z := hbpos z (hKD hz)
    have heq : HarmonicBalls.dyadicScale k * b z / p =
        (2 : ℝ) ^ (Real.logb 2 (b z) - Real.logb 2 p - k) := by
      rw [Real.rpow_sub two_pos', Real.rpow_sub two_pos', Real.rpow_logb two_pos' two_ne_one' hbz,
        Real.rpow_logb two_pos' two_ne_one' hp0, Real.rpow_natCast, HarmonicBalls.dyadicScale, inv_pow]
      ring
    rw [heq]
    obtain ⟨hlo, hhi⟩ := hcell z hz
    have e1 : -((j : ℝ) + 1) / N = -((m : ℝ) + 1) / N - k := by
      rw [hj]
      field_simp
      ring
    have e2 : -(j : ℝ) / N = -(m : ℝ) / N - k := by
      rw [hj]
      field_simp
      ring
    exact ⟨Real.rpow_le_rpow_of_exponent_le one_le_two (by rw [e1]; linarith),
      Real.rpow_le_rpow_of_exponent_le one_le_two (by rw [e2]; linarith)⟩
  have hval : ∀ z ∈ K, smoothExponent γ (mollDilate p f) G (HarmonicBalls.dyadicScale k * b z / p) z =
      smoothExponent γ f G (HarmonicBalls.dyadicScale k * b z) z := by
    intro z hz
    have hbz : 0 < b z := hbpos z (hKD hz)
    rw [hexp _ (div_pos (mul_pos hdk hbz) hp0) z, mul_div_cancel₀ _ hp0.ne']
  constructor
  · simp only [envInf, varScaleApprox]
    rw [restrict_withDensity hKm, restrict_withDensity hKm]
    refine withDensity_mono (ae_restrict_of_forall_mem hKm fun z hz => ?_)
    simp only [ite_eq_left (hball2 z hz), ite_eq_left (hball1 z hz)]
    exact (iInf₂_le _ (hmem z hz)).trans_eq (by rw [hval z hz])
  · simp only [envSup, varScaleApprox]
    rw [restrict_withDensity hKm, restrict_withDensity hKm]
    refine withDensity_mono (ae_restrict_of_forall_mem hKm fun z hz => ?_)
    simp only [ite_eq_left (hball2 z hz), ite_eq_left (hball1 z hz)]
    exact le_iSup₂_of_le _ (hmem z hz) (le_of_eq (by rw [hval z hz]))

private theorem lintegral_le_of_restrict_le {ν ν' : Measure ℂ} {K : Set ℂ} (h : ν.restrict K ≤ ν'.restrict K)
    {φ : ℂ → ENNReal} (hφ : Function.support φ ⊆ K) : ∫⁻ z, φ z ∂ν ≤ ∫⁻ z, φ z ∂ν' :=
  calc ∫⁻ z, φ z ∂ν = ∫⁻ z in K, φ z ∂ν := (setLIntegral_eq_of_support_subset hφ).symm
    _ ≤ ∫⁻ z in K, φ z ∂ν' := lintegral_mono' h le_rfl
    _ = ∫⁻ z, φ z ∂ν' := setLIntegral_eq_of_support_subset hφ

private theorem lintegral_ofReal_ne_top {ν : Measure ℂ} {g : ℂ → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) (hνK : ν (tsupport g) ≠ ⊤) : ∫⁻ z, ENNReal.ofReal (g z) ∂ν ≠ ⊤ := by
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  have hKm : MeasurableSet (tsupport g) := hgs.isCompact.isClosed.measurableSet
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal C ≠ ⊤) hνK) ?_
  rw [← lintegral_indicator_const hKm]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ tsupport g
  · rw [indicator_of_mem hz]
    have := hC z
    rw [Real.norm_eq_abs] at this
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans this)
  · rw [image_eq_zero_of_notMem_tsupport hz, ENNReal.ofReal_zero]
    exact zero_le

private theorem integrable_of_tsupport_subset {μ : Measure ℂ} {D : Set ℂ}
    (hμ : ∀ K, IsCompact K → K ⊆ D → μ K < ⊤) {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgD : tsupport g ⊆ D) : Integrable g μ := by
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  rw [← integrableOn_iff_integrable_of_support_subset (subset_tsupport g)]
  exact Measure.integrableOn_of_bounded (hμ _ hgs.isCompact hgD).ne hgc.aestronglyMeasurable
    (ae_of_all _ hC)

private theorem tendsto_toNat_add_mul (m : ℤ) {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun k : ℕ => (m + (k : ℤ) * N).toNat) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun T => ⟨T + m.natAbs, fun k hk => ?_⟩
  have hkN : (k : ℤ) ≤ k * N := by exact_mod_cast Nat.le_mul_of_pos_right k hN
  generalize (k : ℤ) * N = P at hkN ⊢
  omega

/-- **Fixed `N`**: for a nonnegative test function `g`, eventually the variable-radius integral of `g` is finite and
lies between `min_c L_c ∫ g dμ - δ` and `max_c U_c ∫ g dμ + δ`, where `U_c`, `L_c` are the envelope constants of the
two bumps `f_{q_c}` (finite partition of unity subordinate to the cells of the two grids). -/
private theorem eventually_integral_varScaleApprox_bounds {γ : ℝ} {f : ℂ → ℝ} {D : Set ℂ}
    {G : (ℂ → ℝ) → ℝ} {μ : Measure ℂ} {b : ℂ → ℝ} (hD : IsOpen D) {qc : Bool → ℝ} (hqc : ∀ c, 0 < qc c)
    (hexp : ∀ c, ∀ ε, 0 < ε → ∀ z,
      smoothExponent γ (mollDilate (qc c) f) G ε z = smoothExponent γ f G (qc c * ε) z)
    {N : ℕ} (hN : 1 ≤ N) {U L : Bool → ℝ} (hU : ∀ c, 0 ≤ U c) (hL : ∀ c, 0 ≤ L c)
    (hcover : ∀ x : ℝ, ∃ c : Bool, ∃ m : ℤ,
      x - Real.logb 2 (qc c) ∈ Ioo (-((m : ℝ) + 1) / N) (-(m : ℝ) / N))
    (hS : ∀ c, QuantumZipper.IsVagueLimitOn D (fun j => envSup γ (mollDilate (qc c) f) D G N j)
      (ENNReal.ofReal (U c) • μ))
    (hI : ∀ c, QuantumZipper.IsVagueLimitOn D (fun j => envInf γ (mollDilate (qc c) f) D G N j)
      (ENNReal.ofReal (L c) • μ))
    (hfin : ∀ c, ∀ K, IsCompact K → K ⊆ D → ∀ᶠ j in atTop, envSup γ (mollDilate (qc c) f) D G N j K ≠ ⊤)
    (hμ : ∀ K, IsCompact K → K ⊆ D → μ K < ⊤) (hb : ContinuousOn b D) (hbpos : ∀ z ∈ D, 0 < b z)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hgD : tsupport g ⊆ D) (hg0 : ∀ z, 0 ≤ g z)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∫⁻ z, ENNReal.ofReal (g z) ∂(varScaleApprox γ f D G b k) ≠ ⊤ ∧
      min (L false) (L true) * ∫ z, g z ∂μ - δ ≤ ∫ z, g z ∂(varScaleApprox γ f D G b k) ∧
      ∫ z, g z ∂(varScaleApprox γ f D G b k) ≤ max (U false) (U true) * ∫ z, g z ∂μ + δ := by
  have hK : IsCompact (tsupport g) := hgs.isCompact
  -- the cells of the two grids, pulled back by `log₂ b`
  set W : Bool × ℤ → Set ℂ := fun i =>
    D ∩ (fun z => Real.logb 2 (b z) - Real.logb 2 (qc i.1)) ⁻¹' Ioo (-((i.2 : ℝ) + 1) / N) (-(i.2 : ℝ) / N)
    with hWdef
  have hτ : ∀ c, ContinuousOn (fun z => Real.logb 2 (b z) - Real.logb 2 (qc c)) D := fun c =>
    ((hb.log fun z hz => (hbpos z hz).ne').div_const (Real.log 2)).sub continuousOn_const
  have hWo : ∀ i, IsOpen (W i) := fun i => by
    simp only [hWdef]
    exact (hτ i.1).isOpen_inter_preimage hD isOpen_Ioo
  have hKW : tsupport g ⊆ ⋃ i, W i := fun z hz => by
    obtain ⟨c, m, hcm⟩ := hcover (Real.logb 2 (b z))
    refine mem_iUnion.2 ⟨(c, m), ?_⟩
    simp only [hWdef, mem_inter_iff, mem_preimage]
    exact ⟨hgD hz, hcm⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover W hWo hKW
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed (fun i : t => W i.1)
    (fun i => hWo i.1) fun z hz => by
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 (ht hz)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hzi⟩
  -- the pieces of `g`
  set gi : t → ℂ → ℝ := fun i z => g z * ρ i z with hgi
  have hgi_c : ∀ i, Continuous (gi i) := fun i => hgc.mul (ρ i).continuous
  have hgi_0 : ∀ i z, 0 ≤ gi i z := fun i z => mul_nonneg (hg0 z) (ρ.nonneg i z)
  have hgi_s : ∀ i, HasCompactSupport (gi i) := fun i => hgs.mul_right (f' := ρ i)
  have hgi_t : ∀ i, tsupport (gi i) ⊆ tsupport g ∩ W i.1 := fun i =>
    subset_inter tsupport_mul_subset_left (tsupport_mul_subset_right.trans (hρ i))
  have hgi_D : ∀ i, tsupport (gi i) ⊆ D := fun i => (hgi_t i).trans (inter_subset_left.trans hgD)
  have hgi_cell : ∀ i : t, ∀ z ∈ tsupport (gi i),
      Real.logb 2 (b z) - Real.logb 2 (qc i.1.1) ∈ Ioo (-((i.1.2 : ℝ) + 1) / N) (-(i.1.2 : ℝ) / N) := by
    intro i z hz
    have h := (hgi_t i hz).2
    simp only [hWdef, mem_inter_iff, mem_preimage] at h
    exact h.2
  have hsum : ∀ z, ∑ i, gi i z = g z := by
    intro z
    by_cases hz : z ∈ tsupport g
    · have h1 := ρ.sum_eq_one hz
      rw [finsum_eq_sum_of_fintype] at h1
      simp only [hgi]
      rw [← Finset.mul_sum, h1, mul_one]
    · have h0 : g z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hgi, h0]
  have hsupp : ∀ i, Function.support (fun z => ENNReal.ofReal (gi i z)) ⊆ tsupport (gi i) := fun i z hz =>
    subset_tsupport _ (Function.mem_support.2 fun h0 =>
      (Function.mem_support.1 hz) (by simp only [h0, ENNReal.ofReal_zero]))
  -- the envelope sequences along the indices `m + kN`
  have hsand : ∀ i : t, ∀ᶠ k : ℕ in atTop,
      ((envInf γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat).restrict (tsupport (gi i)) ≤
          (varScaleApprox γ f D G b k).restrict (tsupport (gi i)) ∧
        (varScaleApprox γ f D G b k).restrict (tsupport (gi i)) ≤
          (envSup γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat).restrict (tsupport (gi i))) ∧
      ∫⁻ z, ENNReal.ofReal (gi i z) ∂(envSup γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat) ≠ ⊤ :=
    fun i => (eventually_envelope_sandwich hD (hqc i.1.1) (hexp i.1.1) hN i.1.2 (hgi_s i).isCompact (hgi_D i)
      hb hbpos (hgi_cell i)).and
      (((tendsto_toNat_add_mul i.1.2 hN).eventually (hfin i.1.1 _ (hgi_s i).isCompact (hgi_D i))).mono
        fun k hk => lintegral_ofReal_ne_top (hgi_c i) (hgi_s i) hk)
  have hB : ∀ i : t, Tendsto (fun k : ℕ => (∫⁻ z, ENNReal.ofReal (gi i z)
      ∂(envSup γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat)).toReal) atTop
      (𝓝 (U i.1.1 * ∫ z, gi i z ∂μ)) := by
    intro i
    have h := ((hS i.1.1).2.2 (gi i) (hgi_c i) (hgi_s i) (hgi_D i)).comp (tendsto_toNat_add_mul i.1.2 hN)
    rw [integral_smul_measure, ENNReal.toReal_ofReal (hU _), smul_eq_mul] at h
    refine h.congr fun k => ?_
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hgi_0 i)) (hgi_c i).aestronglyMeasurable
  have hA : ∀ i : t, Tendsto (fun k : ℕ => (∫⁻ z, ENNReal.ofReal (gi i z)
      ∂(envInf γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat)).toReal) atTop
      (𝓝 (L i.1.1 * ∫ z, gi i z ∂μ)) := by
    intro i
    have h := ((hI i.1.1).2.2 (gi i) (hgi_c i) (hgi_s i) (hgi_D i)).comp (tendsto_toNat_add_mul i.1.2 hN)
    rw [integral_smul_measure, ENNReal.toReal_ofReal (hL _), smul_eq_mul] at h
    refine h.congr fun k => ?_
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hgi_0 i)) (hgi_c i).aestronglyMeasurable
  have hBsum := tendsto_finsetSum Finset.univ fun i _ => hB i
  have hAsum := tendsto_finsetSum Finset.univ fun i _ => hA i
  -- the limits
  have hint : ∀ i, Integrable (gi i) μ := fun i =>
    integrable_of_tsupport_subset hμ (hgi_c i) (hgi_s i) (hgi_D i)
  have hIsum : ∑ i, ∫ z, gi i z ∂μ = ∫ z, g z ∂μ := by
    rw [← integral_finsetSum _ fun i _ => hint i]
    exact integral_congr_ae (ae_of_all _ hsum)
  have hUc : ∀ c, U c ≤ max (U false) (U true) := by
    intro c
    cases c
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hLc : ∀ c, min (L false) (L true) ≤ L c := by
    intro c
    cases c
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hUlim : ∑ i, U i.1.1 * ∫ z, gi i z ∂μ ≤ max (U false) (U true) * ∫ z, g z ∂μ := by
    rw [← hIsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hUc _) (integral_nonneg (hgi_0 i))
  have hLlim : min (L false) (L true) * ∫ z, g z ∂μ ≤ ∑ i, L i.1.1 * ∫ z, gi i z ∂μ := by
    rw [← hIsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hLc _) (integral_nonneg (hgi_0 i))
  have hupper := hBsum.eventually (gt_mem_nhds (lt_add_of_pos_right (∑ i, U i.1.1 * ∫ z, gi i z ∂μ) hδ))
  have hlower := hAsum.eventually (lt_mem_nhds (sub_lt_self (∑ i, L i.1.1 * ∫ z, gi i z ∂μ) hδ))
  filter_upwards [eventually_all.2 hsand, hupper, hlower] with k hk hku hkl
  have hdecomp : ∫⁻ z, ENNReal.ofReal (g z) ∂(varScaleApprox γ f D G b k) =
      ∑ i, ∫⁻ z, ENNReal.ofReal (gi i z) ∂(varScaleApprox γ f D G b k) := by
    rw [← lintegral_finsetSum (f := fun i z => ENNReal.ofReal (gi i z)) _
      fun i _ => (hgi_c i).measurable.ennreal_ofReal]
    refine lintegral_congr fun z => ?_
    rw [← hsum z, ENNReal.ofReal_sum_of_nonneg fun i _ => hgi_0 i z]
  have hup_i : ∀ i, ∫⁻ z, ENNReal.ofReal (gi i z) ∂(varScaleApprox γ f D G b k) ≤
      ∫⁻ z, ENNReal.ofReal (gi i z)
        ∂(envSup γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat) := fun i =>
    lintegral_le_of_restrict_le (hk i).1.2 (hsupp i)
  have hlo_i : ∀ i, ∫⁻ z, ENNReal.ofReal (gi i z)
        ∂(envInf γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat) ≤
      ∫⁻ z, ENNReal.ofReal (gi i z) ∂(varScaleApprox γ f D G b k) := fun i =>
    lintegral_le_of_restrict_le (hk i).1.1 (hsupp i)
  have hSfin : ∑ i, ∫⁻ z, ENNReal.ofReal (gi i z)
      ∂(envSup γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun i _ => (hk i).2
  have hle : ∫⁻ z, ENNReal.ofReal (g z) ∂(varScaleApprox γ f D G b k) ≤ ∑ i, ∫⁻ z, ENNReal.ofReal (gi i z)
      ∂(envSup γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat) := by
    rw [hdecomp]
    exact Finset.sum_le_sum fun i _ => hup_i i
  have hfin_k : ∫⁻ z, ENNReal.ofReal (g z) ∂(varScaleApprox γ f D G b k) ≠ ⊤ := ne_top_of_le_ne_top hSfin hle
  have hge : ∑ i, ∫⁻ z, ENNReal.ofReal (gi i z)
      ∂(envInf γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat) ≤
      ∫⁻ z, ENNReal.ofReal (g z) ∂(varScaleApprox γ f D G b k) := by
    rw [hdecomp]
    exact Finset.sum_le_sum fun i _ => hlo_i i
  have hIfin : ∀ i, ∫⁻ z, ENNReal.ofReal (gi i z)
      ∂(envInf γ (mollDilate (qc i.1.1) f) D G N (i.1.2 + (k : ℤ) * N).toNat) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hk i).2 ((hlo_i i).trans (hup_i i))
  have hint_k : ∫ z, g z ∂(varScaleApprox γ f D G b k) =
      (∫⁻ z, ENNReal.ofReal (g z) ∂(varScaleApprox γ f D G b k)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgc.aestronglyMeasurable
  refine ⟨hfin_k, ?_, ?_⟩
  · rw [hint_k]
    have h1 := ENNReal.toReal_mono hfin_k hge
    rw [ENNReal.toReal_sum fun i _ => hIfin i] at h1
    linarith
  · rw [hint_k]
    have h1 := ENNReal.toReal_mono hSfin hle
    rw [ENNReal.toReal_sum fun i _ => (hk i).2] at h1
    linarith

/-- **All `N`, nonnegative test functions**: the variable-radius integrals of `g` converge to `∫ g dμ`, and are
eventually finite. -/
private theorem tendsto_integral_varScaleApprox_of_nonneg {γ : ℝ} {f : ℂ → ℝ} {D : Set ℂ}
    {G : (ℂ → ℝ) → ℝ} {μ : Measure ℂ} {b : ℂ → ℝ} (hD : IsOpen D) {qc : Bool → ℝ} (hqc : ∀ c, 0 < qc c)
    (hexp : ∀ c, ∀ ε, 0 < ε → ∀ z,
      smoothExponent γ (mollDilate (qc c) f) G ε z = smoothExponent γ f G (qc c * ε) z)
    {U L : ℕ → Bool → ℝ} (hU : ∀ N c, 0 ≤ U N c) (hL : ∀ N c, 0 ≤ L N c)
    (hU1 : ∀ c, Tendsto (fun N => U N c) atTop (𝓝 1)) (hL1 : ∀ c, Tendsto (fun N => L N c) atTop (𝓝 1))
    (hcover : ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, ∃ c : Bool, ∃ m : ℤ,
      x - Real.logb 2 (qc c) ∈ Ioo (-((m : ℝ) + 1) / N) (-(m : ℝ) / N))
    (hS : ∀ N : ℕ, 1 ≤ N → ∀ c, QuantumZipper.IsVagueLimitOn D
      (fun j => envSup γ (mollDilate (qc c) f) D G N j) (ENNReal.ofReal (U N c) • μ))
    (hI : ∀ N : ℕ, 1 ≤ N → ∀ c, QuantumZipper.IsVagueLimitOn D
      (fun j => envInf γ (mollDilate (qc c) f) D G N j) (ENNReal.ofReal (L N c) • μ))
    (hfin : ∀ N : ℕ, 1 ≤ N → ∀ c, ∀ K, IsCompact K → K ⊆ D →
      ∀ᶠ j in atTop, envSup γ (mollDilate (qc c) f) D G N j K ≠ ⊤)
    (hμ : ∀ K, IsCompact K → K ⊆ D → μ K < ⊤) (hb : ContinuousOn b D) (hbpos : ∀ z ∈ D, 0 < b z)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hgD : tsupport g ⊆ D)
    (hg0 : ∀ z, 0 ≤ g z) :
    Tendsto (fun k => ∫ z, g z ∂(varScaleApprox γ f D G b k)) atTop (𝓝 (∫ z, g z ∂μ)) ∧
      ∀ᶠ k in atTop, ∫⁻ z, ENNReal.ofReal (g z) ∂(varScaleApprox γ f D G b k) ≠ ⊤ := by
  have hbounds := fun (N : ℕ) (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) =>
    eventually_integral_varScaleApprox_bounds hD hqc hexp hN (hU N) (hL N) (hcover N hN) (hS N hN) (hI N hN)
      (hfin N hN) hμ hb hbpos hgc hgs hgD hg0 hδ
  refine ⟨Metric.tendsto_nhds.2 fun ε hε => ?_, (hbounds 1 le_rfl one_pos).mono fun k hk => hk.1⟩
  have hmax : Tendsto (fun N => max (U N false) (U N true) * ∫ z, g z ∂μ) atTop (𝓝 (∫ z, g z ∂μ)) := by
    simpa using ((hU1 false).max (hU1 true)).mul_const (∫ z, g z ∂μ)
  have hmin : Tendsto (fun N => min (L N false) (L N true) * ∫ z, g z ∂μ) atTop (𝓝 (∫ z, g z ∂μ)) := by
    simpa using ((hL1 false).min (hL1 true)).mul_const (∫ z, g z ∂μ)
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨N, hN1, hNU, hNL⟩ := ((eventually_ge_atTop 1).and
    ((hmax.eventually (Metric.ball_mem_nhds _ hε3)).and (hmin.eventually (Metric.ball_mem_nhds _ hε3)))).exists
  rw [Real.dist_eq] at hNU hNL
  filter_upwards [hbounds N hN1 hε3] with k hk
  obtain ⟨-, hlo, hhi⟩ := hk
  rw [Real.dist_eq, abs_lt]
  constructor
  · have := (abs_lt.1 hNL).1
    linarith
  · have := (abs_lt.1 hNU).2
    linarith

/-- The variable-radius approximations converge vaguely in `D` to `μ`, from the envelope limits of the two bumps
indexed by `Bool` (the general form of `isVagueLimitOn_varScaleApprox`). -/
private theorem isVagueLimitOn_varScaleApprox_bool {γ : ℝ} {f : ℂ → ℝ} {D : Set ℂ}
    {G : (ℂ → ℝ) → ℝ} {μ : Measure ℂ} {b : ℂ → ℝ} (hD : IsOpen D) {qc : Bool → ℝ} (hqc : ∀ c, 0 < qc c)
    (hexp : ∀ c, ∀ ε, 0 < ε → ∀ z,
      smoothExponent γ (mollDilate (qc c) f) G ε z = smoothExponent γ f G (qc c * ε) z)
    {U L : ℕ → Bool → ℝ} (hU : ∀ N c, 0 ≤ U N c) (hL : ∀ N c, 0 ≤ L N c)
    (hU1 : ∀ c, Tendsto (fun N => U N c) atTop (𝓝 1)) (hL1 : ∀ c, Tendsto (fun N => L N c) atTop (𝓝 1))
    (hcover : ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, ∃ c : Bool, ∃ m : ℤ,
      x - Real.logb 2 (qc c) ∈ Ioo (-((m : ℝ) + 1) / N) (-(m : ℝ) / N))
    (hS : ∀ N : ℕ, 1 ≤ N → ∀ c, QuantumZipper.IsVagueLimitOn D
      (fun j => envSup γ (mollDilate (qc c) f) D G N j) (ENNReal.ofReal (U N c) • μ))
    (hI : ∀ N : ℕ, 1 ≤ N → ∀ c, QuantumZipper.IsVagueLimitOn D
      (fun j => envInf γ (mollDilate (qc c) f) D G N j) (ENNReal.ofReal (L N c) • μ))
    (hfin : ∀ N : ℕ, 1 ≤ N → ∀ c, ∀ K, IsCompact K → K ⊆ D →
      ∀ᶠ j in atTop, envSup γ (mollDilate (qc c) f) D G N j K ≠ ⊤)
    (hμc : μ Dᶜ = 0) (hμ : ∀ K, IsCompact K → K ⊆ D → μ K < ⊤) (hb : ContinuousOn b D)
    (hbpos : ∀ z ∈ D, 0 < b z) :
    QuantumZipper.IsVagueLimitOn D (varScaleApprox γ f D G b) μ := by
  refine ⟨hμc, hμ, fun g hgc hgs hgD => ?_⟩
  have key := fun (g : ℂ → ℝ) (hgc : Continuous g) (hgs : HasCompactSupport g) (hgD : tsupport g ⊆ D)
      (hg0 : ∀ z, 0 ≤ g z) =>
    tendsto_integral_varScaleApprox_of_nonneg hD hqc hexp hU hL hU1 hL1 hcover hS hI hfin hμ hb hbpos hgc hgs
      hgD hg0
  set gp : ℂ → ℝ := fun z => max (g z) 0
  set gm : ℂ → ℝ := fun z => max (-g z) 0
  have hgpc : Continuous gp := hgc.max continuous_const
  have hgmc : Continuous gm := hgc.neg.max continuous_const
  have hgps : HasCompactSupport gp := hgs.comp_left (g := fun x : ℝ => max x 0) (by simp)
  have hgms : HasCompactSupport gm := hgs.comp_left (g := fun x : ℝ => max (-x) 0) (by simp)
  have hgpD : tsupport gp ⊆ D := (tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) g).trans hgD
  have hgmD : tsupport gm ⊆ D := (tsupport_comp_subset (g := fun x : ℝ => max (-x) 0) (by simp) g).trans hgD
  obtain ⟨hp, hpfin⟩ := key gp hgpc hgps hgpD fun z => le_max_right _ _
  obtain ⟨hm, hmfin⟩ := key gm hgmc hgms hgmD fun z => le_max_right _ _
  have hsplit : ∀ ν : Measure ℂ, Integrable gp ν → Integrable gm ν →
      ∫ z, g z ∂ν = ∫ z, gp z ∂ν - ∫ z, gm z ∂ν := fun ν h1 h2 => by
    rw [← integral_sub h1 h2]
    exact integral_congr_ae (ae_of_all _ fun z => (max_zero_sub_max_neg_zero_eq_self (g z)).symm)
  have hintν : ∀ (ν : Measure ℂ) (h : ℂ → ℝ), Continuous h → (∀ z, 0 ≤ h z) →
      ∫⁻ z, ENNReal.ofReal (h z) ∂ν ≠ ⊤ → Integrable h ν := fun ν h hc h0 hfin' =>
    ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)).2 hfin'.lt_top⟩
  rw [hsplit μ (integrable_of_tsupport_subset hμ hgpc hgps hgpD)
    (integrable_of_tsupport_subset hμ hgmc hgms hgmD)]
  refine (hp.sub hm).congr' ?_
  filter_upwards [hpfin, hmfin] with k h1 h2
  exact (hsplit _ (hintν _ gp hgpc (fun z => le_max_right _ _) h1)
    (hintν _ gm hgmc (fun z => le_max_right _ _) h2)).symm

/-- **Variable source radii** (Sheffield–Wang (2016), end of the proof of Theorem 1.2, p. 11, for the two bumps
`f` and `f_q`): let `0 < q ≤ 1` with `log₂ q` irrational, and suppose that for every `N ≥ 1` the upper and lower
envelopes over the scales `[2^{-(j+1)/N}, 2^{-j/N}]` converge vaguely in the open set `D`, as `j → ∞`, to `u_N μ` and
`l_N μ` for the bump `f`, and to `u'_N μ` and `l'_N μ` for `f_q`, the four positive constants tending to `1`, and
that the upper envelopes eventually give finite mass to compact subsets of `D`. Then for every function `b` continuous
and positive on `D`, the smooth approximations at the radius `2^{-k} b(z)` converge vaguely in `D` to `μ`. -/
theorem isVagueLimitOn_varScaleApprox {γ q : ℝ} {f : ℂ → ℝ} {D : Set ℂ} {G : (ℂ → ℝ) → ℝ}
    {μ : Measure ℂ} {u l u' l' : ℕ → ℝ} (hD : IsOpen D) (hf : IsMollifier f) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hq : Irrational (Real.logb 2 q))
    (hu : ∀ N, 0 < u N) (hl : ∀ N, 0 < l N) (hu' : ∀ N, 0 < u' N) (hl' : ∀ N, 0 < l' N)
    (hu1 : Tendsto u atTop (𝓝 1)) (hl1 : Tendsto l atTop (𝓝 1))
    (hu1' : Tendsto u' atTop (𝓝 1)) (hl1' : Tendsto l' atTop (𝓝 1))
    (hsup : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D (fun j => envSup γ f D G N j)
      (ENNReal.ofReal (u N) • μ))
    (hinf : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D (fun j => envInf γ f D G N j)
      (ENNReal.ofReal (l N) • μ))
    (hsup' : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D (fun j => envSup γ (mollDilate q f) D G N j)
      (ENNReal.ofReal (u' N) • μ))
    (hinf' : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D (fun j => envInf γ (mollDilate q f) D G N j)
      (ENNReal.ofReal (l' N) • μ))
    (hfin : ∀ N : ℕ, 1 ≤ N → ∀ K, IsCompact K → K ⊆ D →
      ∀ᶠ j in atTop, envSup γ f D G N j K ≠ ⊤ ∧ envSup γ (mollDilate q f) D G N j K ≠ ⊤)
    {b : ℂ → ℝ} (hb : ContinuousOn b D) (hbpos : ∀ z ∈ D, 0 < b z) :
    QuantumZipper.IsVagueLimitOn D (varScaleApprox γ f D G b) μ := by
  have hμc : μ Dᶜ = 0 := by
    have h := (hsup 1 le_rfl).1
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h
    exact h.resolve_left (ENNReal.ofReal_pos.2 (hu 1)).ne'
  have hμ : ∀ K, IsCompact K → K ⊆ D → μ K < ⊤ := by
    intro K hK hKD
    have h := (hsup 1 le_rfl).2.1 K hK hKD
    rw [Measure.smul_apply, smul_eq_mul] at h
    refine lt_top_iff_ne_top.2 fun hK' => ?_
    rw [hK', ENNReal.mul_top (ENNReal.ofReal_pos.2 (hu 1)).ne'] at h
    exact lt_irrefl _ h
  refine isVagueLimitOn_varScaleApprox_bool (qc := fun c => cond c q 1)
    (U := fun N c => cond c (u' N) (u N)) (L := fun N c => cond c (l' N) (l N)) hD ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ hμc hμ hb hbpos
  · intro c; cases c
    · exact one_pos
    · exact hq0
  · intro c ε hε z
    cases c
    · simp [mollDilate_one]
    · exact smoothExponent_mollDilate hf hq0 hq1 hε.ne' G z
  · intro N c; cases c
    · exact (hu N).le
    · exact (hu' N).le
  · intro N c; cases c
    · exact (hl N).le
    · exact (hl' N).le
  · intro c; cases c
    · exact hu1
    · exact hu1'
  · intro c; cases c
    · exact hl1
    · exact hl1'
  · intro N hN x
    rcases exists_mem_cell_or_mem_shifted_cell hN hq x with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨false, m, by simpa using hm⟩
    · exact ⟨true, m, hm⟩
  · intro N hN c; cases c
    · simpa [mollDilate_one] using hsup N hN
    · exact hsup' N hN
  · intro N hN c; cases c
    · simpa [mollDilate_one] using hinf N hN
    · exact hinf' N hN
  · intro N hN c K hK hKD; cases c
    · exact (hfin N hN K hK hKD).mono fun j hj => by simpa [mollDilate_one] using hj.1
    · exact (hfin N hN K hK hKD).mono fun j hj => hj.2

/-! ## Finiteness of the envelopes from a bound on the pairings -/

/-- The upper envelopes of the bump `f_p`, `0 < p ≤ 1`, eventually give finite mass to a compact set `K` on which the
pairings satisfy `|G(f_ε(z - ·))| ≤ C ε^α` for `0 < ε ≤ ε₀` (for instance a local negative regularity bound of the
field). -/
theorem eventually_envSup_ne_top {γ p : ℝ} {f : ℂ → ℝ} {D : Set ℂ} {G : (ℂ → ℝ) → ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1)
    (hexp : ∀ ε, 0 < ε → ∀ z, smoothExponent γ (mollDilate p f) G ε z = smoothExponent γ f G (p * ε) z)
    {N : ℕ} (hN : 1 ≤ N) {K : Set ℂ} (hK : IsCompact K)
    (hG : ∃ C ε₀ α : ℝ, 0 < ε₀ ∧ ∀ z ∈ K, ∀ ε ∈ Ioc 0 ε₀, |G (fun w => mollScale f ε (z - w))| ≤ C * ε ^ α) :
    ∀ᶠ j in atTop, envSup γ (mollDilate p f) D G N j K ≠ ⊤ := by
  obtain ⟨C, ε₀, α, hε₀, hC⟩ := hG
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 : ℝ) / N) := by positivity
  have hr1 : (2 : ℝ) ^ (-(1 : ℝ) / N) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (div_neg_of_neg_of_pos (by norm_num) hNpos)
  have hlim : Tendsto (fun j : ℕ => (2 : ℝ) ^ (-(j : ℝ) / N)) atTop (𝓝 0) := by
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).congr fun j => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  filter_upwards [hlim.eventually (gt_mem_nhds hε₀)] with j hj
  set a : ℝ := (2 : ℝ) ^ (-((j : ℝ) + 1) / N)
  have ha0 : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hpa : 0 < p * a := mul_pos hp0 ha0
  set M : ℝ := |γ| * (|C| * ((p * a) ^ α + ε₀ ^ α)) + γ ^ 2 / 2 * (Real.log ε₀ + mollConst f) with hM
  have hbound : ∀ z ∈ K, ∀ ε ∈ Icc a ((2 : ℝ) ^ (-(j : ℝ) / N)),
      smoothExponent γ (mollDilate p f) G ε z ≤ M := by
    intro z hz ε hε
    have hε0 : 0 < ε := ha0.trans_le hε.1
    have hpε : 0 < p * ε := mul_pos hp0 hε0
    have hpεle : p * ε ≤ ε₀ :=
      (mul_le_of_le_one_left hε0.le hp1).trans (hε.2.trans hj.le)
    rw [hexp ε hε0 z]
    simp only [smoothExponent]
    have hrpow : (p * ε) ^ α ≤ (p * a) ^ α + ε₀ ^ α := by
      rcases le_or_gt 0 α with hα | hα
      · have := Real.rpow_le_rpow hpε.le hpεle hα
        have := Real.rpow_nonneg hpa.le α
        linarith
      · have := Real.rpow_le_rpow_of_nonpos hpa (mul_le_mul_of_nonneg_left hε.1 hp0.le) hα.le
        have := Real.rpow_nonneg hε₀.le α
        linarith
    have hG1 : γ * G (fun w => mollScale f (p * ε) (z - w)) ≤ |γ| * (|C| * ((p * a) ^ α + ε₀ ^ α)) := by
      calc γ * G (fun w => mollScale f (p * ε) (z - w))
          ≤ |γ * G (fun w => mollScale f (p * ε) (z - w))| := le_abs_self _
        _ = |γ| * |G (fun w => mollScale f (p * ε) (z - w))| := abs_mul _ _
        _ ≤ |γ| * (|C| * ((p * a) ^ α + ε₀ ^ α)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc |G (fun w => mollScale f (p * ε) (z - w))| ≤ C * (p * ε) ^ α := hC z hz _ ⟨hpε, hpεle⟩
            _ ≤ |C| * (p * ε) ^ α := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hpε.le α)
            _ ≤ |C| * ((p * a) ^ α + ε₀ ^ α) := mul_le_mul_of_nonneg_left hrpow (abs_nonneg C)
    have hlog : Real.log (p * ε) ≤ Real.log ε₀ := Real.log_le_log hpε hpεle
    have hγ2 : 0 ≤ γ ^ 2 / 2 := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add_right hlog (mollConst f)) hγ2
    linarith [hM]
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  simp only [envSup]
  rw [withDensity_apply _ hKm]
  refine ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal (Real.exp M) ≠ ⊤)
      (hK.measure_lt_top (μ := volume)).ne) ?_
  rw [← setLIntegral_const]
  refine setLIntegral_mono' hKm fun z hz => ?_
  split_ifs
  · exact iSup₂_le fun ε hε => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hbound z hz ε hε))
  · exact zero_le

/-- **Variable source radii from a bound on the pairings**: `isVagueLimitOn_varScaleApprox`, with the finiteness of
the upper envelopes derived from a bound `|G(f_ε(z - ·))| ≤ C ε^α` for small `ε` on each compact subset of `D`. -/
theorem isVagueLimitOn_varScaleApprox_of_bound {γ q : ℝ} {f : ℂ → ℝ} {D : Set ℂ} {G : (ℂ → ℝ) → ℝ}
    {μ : Measure ℂ} {u l u' l' : ℕ → ℝ} (hD : IsOpen D) (hf : IsMollifier f) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hq : Irrational (Real.logb 2 q))
    (hu : ∀ N, 0 < u N) (hl : ∀ N, 0 < l N) (hu' : ∀ N, 0 < u' N) (hl' : ∀ N, 0 < l' N)
    (hu1 : Tendsto u atTop (𝓝 1)) (hl1 : Tendsto l atTop (𝓝 1))
    (hu1' : Tendsto u' atTop (𝓝 1)) (hl1' : Tendsto l' atTop (𝓝 1))
    (hsup : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D (fun j => envSup γ f D G N j)
      (ENNReal.ofReal (u N) • μ))
    (hinf : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D (fun j => envInf γ f D G N j)
      (ENNReal.ofReal (l N) • μ))
    (hsup' : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D (fun j => envSup γ (mollDilate q f) D G N j)
      (ENNReal.ofReal (u' N) • μ))
    (hinf' : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D (fun j => envInf γ (mollDilate q f) D G N j)
      (ENNReal.ofReal (l' N) • μ))
    (hG : ∀ K, IsCompact K → K ⊆ D → ∃ C ε₀ α : ℝ, 0 < ε₀ ∧
      ∀ z ∈ K, ∀ ε ∈ Ioc 0 ε₀, |G (fun w => mollScale f ε (z - w))| ≤ C * ε ^ α)
    {b : ℂ → ℝ} (hb : ContinuousOn b D) (hbpos : ∀ z ∈ D, 0 < b z) :
    QuantumZipper.IsVagueLimitOn D (varScaleApprox γ f D G b) μ := by
  refine isVagueLimitOn_varScaleApprox hD hf hq0 hq1 hq hu hl hu' hl' hu1 hl1 hu1' hl1' hsup hinf hsup' hinf'
    (fun N hN K hK hKD => ?_) hb hbpos
  have h1 := eventually_envSup_ne_top (γ := γ) (D := D) (G := G) one_pos le_rfl
    (fun ε _ z => by simp [mollDilate_one]) hN hK (hG K hK hKD)
  have h2 := eventually_envSup_ne_top (γ := γ) (D := D) (G := G) hq0 hq1
    (fun ε hε z => smoothExponent_mollDilate hf hq0 hq1 hε.ne' G z) hN hK (hG K hK hKD)
  rw [mollDilate_one] at h1
  exact h1.and h2

/-- `isVagueLimitOn_varScaleApprox_of_bound` with the explicit second bump `f_{1/3}`. -/
theorem isVagueLimitOn_varScaleApprox_one_third {γ : ℝ} {f : ℂ → ℝ} {D : Set ℂ} {G : (ℂ → ℝ) → ℝ}
    {μ : Measure ℂ} {u l u' l' : ℕ → ℝ} (hD : IsOpen D) (hf : IsMollifier f)
    (hu : ∀ N, 0 < u N) (hl : ∀ N, 0 < l N) (hu' : ∀ N, 0 < u' N) (hl' : ∀ N, 0 < l' N)
    (hu1 : Tendsto u atTop (𝓝 1)) (hl1 : Tendsto l atTop (𝓝 1))
    (hu1' : Tendsto u' atTop (𝓝 1)) (hl1' : Tendsto l' atTop (𝓝 1))
    (hsup : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D (fun j => envSup γ f D G N j)
      (ENNReal.ofReal (u N) • μ))
    (hinf : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D (fun j => envInf γ f D G N j)
      (ENNReal.ofReal (l N) • μ))
    (hsup' : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D
      (fun j => envSup γ (mollDilate (1 / 3) f) D G N j) (ENNReal.ofReal (u' N) • μ))
    (hinf' : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn D
      (fun j => envInf γ (mollDilate (1 / 3) f) D G N j) (ENNReal.ofReal (l' N) • μ))
    (hG : ∀ K, IsCompact K → K ⊆ D → ∃ C ε₀ α : ℝ, 0 < ε₀ ∧
      ∀ z ∈ K, ∀ ε ∈ Ioc 0 ε₀, |G (fun w => mollScale f ε (z - w))| ≤ C * ε ^ α)
    {b : ℂ → ℝ} (hb : ContinuousOn b D) (hbpos : ∀ z ∈ D, 0 < b z) :
    QuantumZipper.IsVagueLimitOn D (varScaleApprox γ f D G b) μ :=
  isVagueLimitOn_varScaleApprox_of_bound hD hf (by norm_num) (by norm_num) irrational_logb_two_one_third
    hu hl hu' hl' hu1 hl1 hu1' hl1' hsup hinf hsup' hinf' hG hb hbpos

end LQGMeasureChart

end MatedCRT
