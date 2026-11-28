import Mathlib
import HarmonicBalls.Proofs.Potential.Fundamental

/-!
# The gradient of the logarithmic kernel on the plane

For `Γ(z) = (2π)⁻¹ log |z|`, the fundamental solution of the Laplacian on the plane
(Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, (2.12)),
`newtonGrad i x y` is `-∂_{x_i} Γ(x - y)`, the `i`-th coordinate of `(2π)⁻¹ (y - x) / |y - x|²`.

## Main results

* `MatedCRT.GFFLocalRegularity.eq_sum_integral_newtonGrad`: Green's representation formula
  (Gilbarg–Trudinger, (2.16), in the compactly supported form (2.17)) for a compactly supported smooth function `v` on the plane,
  `v y = ∑ i, ∫ newtonGrad i x y * ∂_i v(x) dx`, that is `v(y) = ∫ Γ(x - y) Δv(x) dx` integrated by parts
  once. It follows from the radial integral
  `∫ Dφ(y)(y - x) / |y - x|² dy = -2π φ(x)` (`HarmonicBalls.integral_fderiv_div_norm_sq`), which is
  this formula in polar coordinates around `x`.
* `MatedCRT.GFFLocalRegularity.memLp_newtonGrad`: `y ↦ newtonGrad i x y` is in `L^q` of every ball
  for `1 < q < 2`, because `|z|^{-q}` is integrable near `0` for `q < 2`
  (`MeasureTheory.integrableOn_ball_of_norm_le_rpow`).
* `MatedCRT.GFFLocalRegularity.eLpNorm_newtonGrad_sub_le`: the `L^q(ℂ)` norm of
  `newtonGrad i x - newtonGrad i x'` is at most `C |x - x'|^{2/q - 1}`; the kernel is homogeneous of
  degree `-1`, which gives the scaling `ρ^{2/q - 1}` (`MeasureTheory.Measure.map_addHaar_smul`), and the
  difference of the kernel at two points at distance one is `O(|y|⁻²)` at infinity, which is in `L^q`
  for `q > 1`.
* `MatedCRT.GFFLocalRegularity.continuous_newtonGrad_toLp`: continuity of `x ↦ newtonGrad i x` into
  `L^q` of a ball, from the Hölder estimate.
-/

namespace MatedCRT.GFFLocalRegularity

open MeasureTheory Metric Set
open scoped NNReal ENNReal

/-- coordinate `i` of a complex number: `0 ↦ re`, `1 ↦ im` -/
def coord (i : Fin 2) (z : ℂ) : ℝ := ![z.re, z.im] i

/-- the basis vector `i` of `ℂ` over `ℝ`: `0 ↦ 1`, `1 ↦ I` -/
noncomputable def basis (i : Fin 2) : ℂ := ![1, Complex.I] i

/-- The kernel `newtonGrad i x y = -∂_{x_i} Γ(x - y)` with `Γ(z) = (2π)⁻¹ log |z|`:
the `i`-th coordinate of `(2π)⁻¹ (y - x) / |y - x|²`. -/
noncomputable def newtonGrad (i : Fin 2) (x y : ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * coord i (y - x) / ‖y - x‖ ^ 2

/-- The kernel as a function of the difference `z = y - x`. -/
noncomputable def newtonGradKernel (i : Fin 2) (z : ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * coord i z / ‖z‖ ^ 2

/-- `newtonGrad` is the kernel `newtonGradKernel` evaluated at `y - x`. -/
theorem newtonGrad_eq (i : Fin 2) (x y : ℂ) : newtonGrad i x y = newtonGradKernel i (y - x) := rfl

/-- A coordinate of a complex number is at most its norm. -/
theorem abs_coord_le (i : Fin 2) (z : ℂ) : |coord i z| ≤ ‖z‖ := by
  fin_cases i
  · simpa [coord] using Complex.abs_re_le_norm z
  · simpa [coord] using Complex.abs_im_le_norm z

/-- The coordinate functions are continuous. -/
theorem continuous_coord (i : Fin 2) : Continuous (coord i) := by
  fin_cases i
  · exact Complex.continuous_re
  · exact Complex.continuous_im

/-- A real linear functional on `ℂ` evaluated at `z` is the sum of its values on the basis, weighted by the
coordinates of `z`. -/
theorem sum_coord_mul_apply (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    ∑ i : Fin 2, coord i z * L (basis i) = L z := by
  have hz : z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  conv_rhs => rw [hz, map_add, map_smul, map_smul]
  simp [Fin.sum_univ_two, coord, basis]

/-- The kernel is measurable. -/
theorem measurable_newtonGradKernel (i : Fin 2) : Measurable (newtonGradKernel i) := by
  unfold newtonGradKernel
  exact (measurable_const.mul (continuous_coord i).measurable).div (by fun_prop)

/-- The kernel is bounded by `(2π)⁻¹ |z|⁻¹`. -/
theorem abs_newtonGradKernel_le (i : Fin 2) (z : ℂ) :
    |newtonGradKernel i z| ≤ (2 * Real.pi)⁻¹ * ‖z‖⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [newtonGradKernel]
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold newtonGradKernel
  rw [abs_div, abs_mul, abs_of_pos (inv_pos.2 (by positivity)),
    abs_of_pos (by positivity : 0 < ‖z‖ ^ 2)]
  calc (2 * Real.pi)⁻¹ * |coord i z| / ‖z‖ ^ 2 ≤ (2 * Real.pi)⁻¹ * ‖z‖ / ‖z‖ ^ 2 := by
        gcongr; exact abs_coord_le i z
    _ = _ := by field_simp

/-- For compactly supported `C¹` `v`, `x ↦ newtonGrad i x y * ∂_i v(x)` is integrable. -/
theorem integrable_newtonGrad_mul {v : ℂ → ℝ} (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (i : Fin 2) (y : ℂ) :
    Integrable (fun x => newtonGrad i x y * fderiv ℝ v x (basis i)) := by
  have hGc : HasCompactSupport fun x => fderiv ℝ v x (basis i) := hvc.fderiv_apply ℝ _
  have hG : Continuous fun x => fderiv ℝ v x (basis i) :=
    (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨B, hB⟩ := hG.bounded_above_of_compact_support hGc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hK : IsCompact (tsupport fun x => fderiv ℝ v x (basis i)) := hGc
  have hsupp : Function.support (fun x => newtonGrad i x y * fderiv ℝ v x (basis i)) ⊆
      tsupport fun x => fderiv ℝ v x (basis i) := fun x hx =>
    subset_tsupport _ fun h => hx (by simp [h])
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  have hint : IntegrableOn (fun x : ℂ => ((2 * Real.pi)⁻¹ * B) * ‖x - y‖⁻¹)
      (tsupport fun x => fderiv ℝ v x (basis i)) :=
    ((HarmonicBalls.locallyIntegrable_inv_norm_sub y).integrableOn_isCompact hK).const_mul _
  refine hint.mono' ?_ (ae_of_all _ fun x => ?_)
  · have hm : Measurable fun x => newtonGrad i x y :=
      (measurable_newtonGradKernel i).comp (measurable_const.sub measurable_id)
    exact (hm.mul hG.measurable).aestronglyMeasurable
  · have h1 : |newtonGrad i x y| ≤ (2 * Real.pi)⁻¹ * ‖x - y‖⁻¹ := by
      rw [newtonGrad_eq, norm_sub_rev]
      exact abs_newtonGradKernel_le i _
    rw [Real.norm_eq_abs, abs_mul]
    calc |newtonGrad i x y| * |fderiv ℝ v x (basis i)|
        ≤ ((2 * Real.pi)⁻¹ * ‖x - y‖⁻¹) * B :=
          mul_le_mul h1 (hB x) (abs_nonneg _) (by positivity)
      _ = _ := by ring

/-- **Green's representation formula** (Gilbarg–Trudinger, (2.16), (2.17)): for a compactly supported smooth
`v` on the plane, `v(y) = ∑ i, ∫ newtonGrad i x y ∂_i v(x) dx`. This is `v(y) = ∫ Γ(x - y) Δv(x) dx`
with one integration by parts, `∇_x Γ(x - y) = (2π)⁻¹ (x - y) / |x - y|²`. -/
theorem eq_sum_integral_newtonGrad {v : ℂ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (y : ℂ) :
    v y = ∑ i : Fin 2, ∫ x, newtonGrad i x y * fderiv ℝ v x (basis i) := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by exact_mod_cast le_top)
  rw [← integral_finsetSum _ (fun i _ => integrable_newtonGrad_mul hv1 hvc i y)]
  have h := HarmonicBalls.integral_fderiv_div_norm_sq hv1 hvc y
  have hpt : ∀ x : ℂ, ∑ i : Fin 2, newtonGrad i x y * fderiv ℝ v x (basis i) =
      (2 * Real.pi)⁻¹ * -(fderiv ℝ v x (x - y) / ‖x - y‖ ^ 2) := by
    intro x
    have h1 : ∀ i : Fin 2, newtonGrad i x y * fderiv ℝ v x (basis i) =
        ((2 * Real.pi)⁻¹ / ‖y - x‖ ^ 2) * (coord i (y - x) * fderiv ℝ v x (basis i)) :=
      fun i => by unfold newtonGrad; ring
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum, sum_coord_mul_apply,
      ← neg_sub x y, map_neg, norm_neg]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_neg, h]
  have := Real.pi_pos.ne'
  field_simp

/-! ### Local integrability of the `q`-th power -/

/-- The coordinates are additive. -/
theorem coord_sub (i : Fin 2) (u w : ℂ) : coord i (u - w) = coord i u - coord i w := by
  fin_cases i <;> simp [coord]

/-- The `i`-th coordinate of `1 / conj z` is `coord i z / |z|²`. -/
theorem coord_conj_inv (i : Fin 2) (z : ℂ) :
    coord i ((starRingEnd ℂ z)⁻¹) = coord i z / ‖z‖ ^ 2 := by
  fin_cases i
  · simp [coord, Complex.inv_re, Complex.normSq_eq_norm_sq]
  · simp [coord, Complex.inv_im, Complex.normSq_eq_norm_sq]

/-- In complex notation `2π k(z) = 1 / conj z`. -/
theorem newtonGradKernel_eq (i : Fin 2) (z : ℂ) :
    newtonGradKernel i z = (2 * Real.pi)⁻¹ * coord i ((starRingEnd ℂ z)⁻¹) := by
  rw [coord_conj_inv, newtonGradKernel, mul_div_assoc]

/-- The difference of the kernel at two points `a`, `b` is `(2π)⁻¹ |a - b| / (|a| |b|)` at most; this is
the coordinate of `(2π)⁻¹ (1 / conj a - 1 / conj b)`. -/
theorem abs_newtonGradKernel_sub_le (i : Fin 2) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    |newtonGradKernel i a - newtonGradKernel i b| ≤
      (2 * Real.pi)⁻¹ * (‖a - b‖ / (‖a‖ * ‖b‖)) := by
  have ha' : starRingEnd ℂ a ≠ 0 := (map_ne_zero _).2 ha
  have hb' : starRingEnd ℂ b ≠ 0 := (map_ne_zero _).2 hb
  rw [newtonGradKernel_eq, newtonGradKernel_eq, ← mul_sub, ← coord_sub, abs_mul,
    abs_of_pos (inv_pos.2 (by positivity : 0 < 2 * Real.pi))]
  refine mul_le_mul_of_nonneg_left ((abs_coord_le _ _).trans ?_) (by positivity)
  rw [inv_sub_inv ha' hb', norm_div, norm_mul, Complex.norm_conj, Complex.norm_conj, ← map_sub,
    Complex.norm_conj, norm_sub_rev]

/-- `|v|^{-q}` is integrable on every disc `B_R(0)` of the plane when `q < 2`. -/
theorem integrableOn_ball_inv_norm_rpow {q : ℝ} (hq2 : q < 2) (R : ℝ) :
    IntegrableOn (fun v : ℂ => (‖v‖⁻¹) ^ q) (ball 0 R) := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := q) (by simp) (by simpa using hq2)
    (ae_of_all _ fun v => ?_)
    ((measurable_inv.comp continuous_norm.measurable).pow_const q).aestronglyMeasurable
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.inv_rpow (norm_nonneg v),
    Real.rpow_neg (norm_nonneg v), one_mul]

/-- `|v|^{-2q}` is integrable outside `B_2(0)` when `q > 1`, by `integrable_rpow_neg_one_add_norm_sq`. -/
theorem integrable_indicator_inv_norm_sq_rpow {q : ℝ} (hq1 : 1 < q) :
    Integrable (indicator (ball (0 : ℂ) 2)ᶜ fun v : ℂ => ((‖v‖ ^ 2)⁻¹) ^ q) := by
  have hint := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 2 * q)
    (by simp; linarith)
  have hint' := hint.const_mul (2 ^ q)
  refine hint'.mono' ?_ (ae_of_all _ fun v => ?_)
  · refine (Measurable.indicator ?_ measurableSet_ball.compl).aestronglyMeasurable
    fun_prop
  · by_cases hv : v ∈ (ball (0 : ℂ) 2)ᶜ
    · rw [indicator_of_mem hv]
      have h2 : 2 ≤ ‖v‖ := by simpa using hv
      have hs : 4 ≤ ‖v‖ ^ 2 := by nlinarith
      have h1 : (‖v‖ ^ 2)⁻¹ ≤ 2 * (1 + ‖v‖ ^ 2)⁻¹ := by
        calc (‖v‖ ^ 2)⁻¹ = 2 * (2 * ‖v‖ ^ 2)⁻¹ := by field_simp
          _ ≤ 2 * (1 + ‖v‖ ^ 2)⁻¹ := by gcongr; linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), show -(2 * q) / 2 = -q by ring]
      calc ((‖v‖ ^ 2)⁻¹) ^ q ≤ (2 * (1 + ‖v‖ ^ 2)⁻¹) ^ q :=
            Real.rpow_le_rpow (by positivity) h1 (by linarith)
        _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity), Real.inv_rpow (by positivity),
              Real.rpow_neg (by positivity)]
    · simp [indicator_of_notMem hv]
      positivity

/-- `|v|⁻¹ 1_{B_{1/2}(0)}` is in `L^q(ℂ)` for `1 < q < 2`. -/
theorem memLp_indicator_inv_norm {q : ℝ≥0} (hq1 : 1 < q) (hq2 : q < 2) :
    MemLp (indicator (ball (0 : ℂ) (1 / 2)) fun v : ℂ => ‖v‖⁻¹) q volume := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast zero_lt_one.trans hq1
  have hq2' : (q : ℝ) < 2 := by exact_mod_cast hq2
  refine (integrable_norm_rpow_iff ?_ (by simpa using (zero_lt_one.trans hq1).ne')
    ENNReal.coe_ne_top).1 ?_
  · exact (Measurable.indicator (measurable_inv.comp continuous_norm.measurable)
      measurableSet_ball).aestronglyMeasurable
  · have h := (integrable_indicator_iff (measurableSet_ball (x := (0 : ℂ)) (ε := 1 / 2))).2
      (integrableOn_ball_inv_norm_rpow hq2' (1 / 2))
    refine h.congr (ae_of_all _ fun v => ?_)
    by_cases hv : v ∈ ball (0 : ℂ) (1 / 2)
    · simp only [indicator_of_mem hv, ENNReal.coe_toReal,
        Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg v))]
    · simp only [indicator_of_notMem hv, norm_zero, ENNReal.coe_toReal, Real.zero_rpow hq0.ne']

/-- `|v|⁻² 1_{B_2(0)ᶜ}` is in `L^q(ℂ)` for `q > 1`. -/
theorem memLp_indicator_inv_norm_sq {q : ℝ≥0} (hq1 : 1 < q) :
    MemLp (indicator (ball (0 : ℂ) 2)ᶜ fun v : ℂ => (‖v‖ ^ 2)⁻¹) q volume := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast zero_lt_one.trans hq1
  have hq1' : (1 : ℝ) < q := by exact_mod_cast hq1
  refine (integrable_norm_rpow_iff ?_ (by simpa using (zero_lt_one.trans hq1).ne')
    ENNReal.coe_ne_top).1 ?_
  · exact (Measurable.indicator (by fun_prop) measurableSet_ball.compl).aestronglyMeasurable
  · refine (integrable_indicator_inv_norm_sq_rpow hq1').congr (ae_of_all _ fun v => ?_)
    by_cases hv : v ∈ (ball (0 : ℂ) 2)ᶜ
    · simp [indicator_of_mem hv]
    · simp [indicator_of_notMem hv, Real.zero_rpow hq0.ne']

/-- The indicator function of `B_2(0)` is in `L^q(ℂ)`. -/
theorem memLp_indicator_one {q : ℝ≥0} :
    MemLp (indicator (ball (0 : ℂ) 2) fun _ : ℂ => (1 : ℝ)) q volume :=
  memLp_indicator_const _ measurableSet_ball 1 (Or.inr measure_ball_lt_top.ne)

/-- **The kernel is in `L^q` of every ball.** For `1 < q < 2`, `y ↦ newtonGrad i x y` is in
`L^q` of every ball, since `|z|^{-q}` is integrable near `0` for `q < 2`. -/
theorem memLp_newtonGrad {q : ℝ≥0} {c : ℂ} {r : ℝ} (hq1 : 1 < q) (hq2 : q < 2) (i : Fin 2)
    (x : ℂ) : MemLp (fun y => newtonGrad i x y) q (volume.restrict (ball c r)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast zero_lt_one.trans hq1
  have hq2' : (q : ℝ) < 2 := by exact_mod_cast hq2
  have hmeas : Measurable fun y => newtonGrad i x y :=
    (measurable_newtonGradKernel i).comp (measurable_id.sub_const x)
  refine (integrable_norm_rpow_iff hmeas.aestronglyMeasurable
    (by simpa using (zero_lt_one.trans hq1).ne') ENNReal.coe_ne_top).1 ?_
  simp only [ENNReal.coe_toReal]
  have hball : ∀ R : ℝ, IntegrableOn (fun z : ℂ => ‖newtonGradKernel i z‖ ^ (q : ℝ)) (ball 0 R) := by
    intro R
    refine ((integrableOn_ball_inv_norm_rpow hq2' R).const_mul (((2 * Real.pi)⁻¹) ^ (q : ℝ))).mono'
      (((measurable_newtonGradKernel i).norm.pow_const _).aestronglyMeasurable)
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.mul_rpow (by positivity)
      (by positivity)]
    exact Real.rpow_le_rpow (norm_nonneg _)
      (by rw [Real.norm_eq_abs]; exact abs_newtonGradKernel_le i z) hq0.le
  have hloc := HarmonicBalls.locallyIntegrable_comp_sub_of_integrableOn_ball hball x
  exact (hloc.integrableOn_isCompact (isCompact_closedBall c r)).mono_set ball_subset_closedBall

/-- The quantity `|w|⁻¹ |w - e|⁻¹`, for a unit vector `e`, is dominated by a sum of four functions that are
in `L^q` independently of `e`. -/
theorem inv_mul_inv_le {e : ℂ} (he : ‖e‖ = 1) (w : ℂ) :
    ‖w‖⁻¹ * ‖w - e‖⁻¹ ≤
      2 * indicator (ball (0 : ℂ) (1 / 2)) (fun v : ℂ => ‖v‖⁻¹) w +
      2 * indicator (ball (0 : ℂ) (1 / 2)) (fun v : ℂ => ‖v‖⁻¹) (w - e) +
      4 * indicator (ball (0 : ℂ) 2) (fun _ : ℂ => (1 : ℝ)) w +
      2 * indicator (ball (0 : ℂ) 2)ᶜ (fun v : ℂ => (‖v‖ ^ 2)⁻¹) w := by
  have hs0 := norm_nonneg w
  have ht0 := norm_nonneg (w - e)
  have h1 : 1 ≤ ‖w‖ + ‖w - e‖ := by
    have := norm_sub_le w (w - e)
    simpa [he] using this
  have h2 : ‖w‖ ≤ ‖w - e‖ + 1 := by
    calc ‖w‖ = ‖(w - e) + e‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - e‖ + ‖e‖ := norm_add_le _ _
      _ = _ := by rw [he]
  have h3 : ‖w - e‖ ≤ ‖w‖ + 1 := by
    have := norm_sub_le w e
    rwa [he] at this
  have nA : 0 ≤ indicator (ball (0 : ℂ) (1 / 2)) (fun v : ℂ => ‖v‖⁻¹) w :=
    indicator_nonneg (fun v _ => by positivity) w
  have nB : 0 ≤ indicator (ball (0 : ℂ) (1 / 2)) (fun v : ℂ => ‖v‖⁻¹) (w - e) :=
    indicator_nonneg (fun v _ => by positivity) _
  have nC : 0 ≤ indicator (ball (0 : ℂ) 2) (fun _ : ℂ => (1 : ℝ)) w :=
    indicator_nonneg (fun v _ => zero_le_one) w
  have nD : 0 ≤ indicator (ball (0 : ℂ) 2)ᶜ (fun v : ℂ => (‖v‖ ^ 2)⁻¹) w :=
    indicator_nonneg (fun v _ => by positivity) w
  rcases lt_or_ge ‖w‖ (1 / 2) with hs | hs
  · have hw : w ∈ ball (0 : ℂ) (1 / 2) := by simpa using hs
    rw [indicator_of_mem hw] at *
    have : ‖w - e‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hm : ‖w‖⁻¹ * ‖w - e‖⁻¹ ≤ ‖w‖⁻¹ * 2 := mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  rcases lt_or_ge ‖w - e‖ (1 / 2) with ht | ht
  · have hw : w - e ∈ ball (0 : ℂ) (1 / 2) := by simpa using ht
    rw [indicator_of_mem hw] at *
    have : ‖w‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hm : ‖w‖⁻¹ * ‖w - e‖⁻¹ ≤ 2 * ‖w - e‖⁻¹ := mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  rcases lt_or_ge ‖w‖ 2 with hs2 | hs2
  · have hw : w ∈ ball (0 : ℂ) 2 := by simpa using hs2
    rw [indicator_of_mem hw] at *
    have ha : ‖w‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hb : ‖w - e‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hm : ‖w‖⁻¹ * ‖w - e‖⁻¹ ≤ 2 * 2 :=
      mul_le_mul ha hb (by positivity) (by norm_num)
    linarith
  · have hw : w ∈ (ball (0 : ℂ) 2)ᶜ := by simpa using hs2
    rw [indicator_of_mem hw] at *
    have hm : ‖w‖⁻¹ * ‖w - e‖⁻¹ ≤ 2 * (‖w‖ ^ 2)⁻¹ := by
      rw [← mul_inv]
      calc (‖w‖ * ‖w - e‖)⁻¹ ≤ (‖w‖ * (‖w‖ / 2))⁻¹ :=
            inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hs0)
        _ = 2 * (‖w‖ ^ 2)⁻¹ := by field_simp
    linarith

/-- **Uniform bound for unit vectors.** For `1 < q < 2` there is a finite `M` with
`‖k_i(w) - k_i(w - e)‖_{L^q(ℂ)} ≤ M` for every coordinate `i` and every unit vector `e`. -/
theorem exists_eLpNorm_newtonGradKernel_sub_le {q : ℝ≥0} (hq1 : 1 < q) (hq2 : q < 2) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ (i : Fin 2) (e : ℂ), ‖e‖ = 1 →
      eLpNorm (fun w => newtonGradKernel i w - newtonGradKernel i (w - e)) q volume ≤ M := by
  have hq : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq1.le
  set f₁ : ℂ → ℝ := indicator (ball (0 : ℂ) (1 / 2)) fun v : ℂ => ‖v‖⁻¹ with hf₁
  set f₂ : ℂ → ℝ := indicator (ball (0 : ℂ) 2)ᶜ fun v : ℂ => (‖v‖ ^ 2)⁻¹ with hf₂
  set f₃ : ℂ → ℝ := indicator (ball (0 : ℂ) 2) fun _ : ℂ => (1 : ℝ) with hf₃
  have m₁ : MemLp f₁ q volume := memLp_indicator_inv_norm hq1 hq2
  have m₂ : MemLp f₂ q volume := memLp_indicator_inv_norm_sq hq1
  have m₃ : MemLp f₃ q volume := memLp_indicator_one
  refine ⟨‖(2 : ℝ)‖ₑ * eLpNorm f₁ q volume + ‖(2 : ℝ)‖ₑ * eLpNorm f₁ q volume +
    ‖(4 : ℝ)‖ₑ * eLpNorm f₃ q volume + ‖(2 : ℝ)‖ₑ * eLpNorm f₂ q volume, ?_, ?_⟩
  · refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
      exact ENNReal.mul_ne_top (by simp) (by first | exact m₁.eLpNorm_ne_top | exact m₂.eLpNorm_ne_top | exact m₃.eLpNorm_ne_top)
  intro i e he
  have hae : ∀ᵐ w : ℂ, w ≠ 0 := by
    rw [ae_iff]; simp
  have hae' : ∀ᵐ w : ℂ, w - e ≠ 0 := by
    have := (measurePreserving_sub_right (volume : Measure ℂ) e).quasiMeasurePreserving.ae hae
    exact this
  have hmeas : AEStronglyMeasurable
      (fun w => newtonGradKernel i w - newtonGradKernel i (w - e)) volume :=
    ((measurable_newtonGradKernel i).sub
      ((measurable_newtonGradKernel i).comp (measurable_id.sub_const e))).aestronglyMeasurable
  have hg : eLpNorm (fun w => newtonGradKernel i w - newtonGradKernel i (w - e)) q volume ≤
      eLpNorm ((2 : ℝ) • f₁ + (2 : ℝ) • (fun w => f₁ (w - e)) + (4 : ℝ) • f₃ + (2 : ℝ) • f₂) q
        volume := by
    refine eLpNorm_mono_ae hmeas ?_
    filter_upwards [hae, hae'] with w hw hwe
    have hb := abs_newtonGradKernel_sub_le i hw hwe
    have hk := inv_mul_inv_le he w
    have hpi : (2 * Real.pi)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]; linarith [Real.pi_gt_three]
    have hsub : ‖w - (w - e)‖ = 1 := by simpa using he
    rw [hsub] at hb
    have hs := norm_pos_iff.2 hw
    have ht := norm_pos_iff.2 hwe
    have h1 : (2 * Real.pi)⁻¹ * (1 / (‖w‖ * ‖w - e‖)) ≤ ‖w‖⁻¹ * ‖w - e‖⁻¹ := by
      calc (2 * Real.pi)⁻¹ * (1 / (‖w‖ * ‖w - e‖)) ≤ 1 * (1 / (‖w‖ * ‖w - e‖)) :=
            mul_le_mul_of_nonneg_right hpi (by positivity)
        _ = _ := by rw [one_mul, one_div, mul_inv]
    have hnn : 0 ≤ ((2 : ℝ) • f₁ + (2 : ℝ) • (fun w => f₁ (w - e)) + (4 : ℝ) • f₃ + (2 : ℝ) • f₂) w := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf₁, hf₂, hf₃]
      have a1 : 0 ≤ indicator (ball (0 : ℂ) (1 / 2)) (fun v : ℂ => ‖v‖⁻¹) w :=
        indicator_nonneg (fun v _ => by positivity) w
      have a2 : 0 ≤ indicator (ball (0 : ℂ) (1 / 2)) (fun v : ℂ => ‖v‖⁻¹) (w - e) :=
        indicator_nonneg (fun v _ => by positivity) _
      have a3 : 0 ≤ indicator (ball (0 : ℂ) 2) (fun _ : ℂ => (1 : ℝ)) w :=
        indicator_nonneg (fun v _ => zero_le_one) w
      have a4 : 0 ≤ indicator (ball (0 : ℂ) 2)ᶜ (fun v : ℂ => (‖v‖ ^ 2)⁻¹) w :=
        indicator_nonneg (fun v _ => by positivity) w
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    have : |newtonGradKernel i w - newtonGradKernel i (w - e)| ≤ _ := hb
    refine this.trans (h1.trans ?_)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf₁, hf₂, hf₃] using hk
  refine hg.trans ?_
  have hshift : eLpNorm (fun w => f₁ (w - e)) q volume = eLpNorm f₁ q volume :=
    eLpNorm_comp_measurePreserving (g := f₁) m₁.aestronglyMeasurable
      (measurePreserving_sub_right (volume : Measure ℂ) e)
  calc _ ≤ eLpNorm ((2 : ℝ) • f₁ + (2 : ℝ) • (fun w => f₁ (w - e)) + (4 : ℝ) • f₃) q volume +
        eLpNorm ((2 : ℝ) • f₂) q volume := eLpNorm_add_le hq
    _ ≤ (eLpNorm ((2 : ℝ) • f₁ + (2 : ℝ) • (fun w => f₁ (w - e))) q volume +
        eLpNorm ((4 : ℝ) • f₃) q volume) + eLpNorm ((2 : ℝ) • f₂) q volume := by
        gcongr; exact eLpNorm_add_le hq
    _ ≤ ((eLpNorm ((2 : ℝ) • f₁) q volume + eLpNorm ((2 : ℝ) • (fun w => f₁ (w - e))) q volume) +
        eLpNorm ((4 : ℝ) • f₃) q volume) + eLpNorm ((2 : ℝ) • f₂) q volume := by
        gcongr; exact eLpNorm_add_le hq
    _ = _ := by
        rw [eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_const_smul, hshift]

/-! ### Scaling and the Hölder estimate -/

/-- The coordinates are homogeneous. -/
theorem coord_smul (i : Fin 2) (ρ : ℝ) (z : ℂ) : coord i (ρ • z) = ρ * coord i z := by
  fin_cases i <;> simp [coord]

/-- The kernel is homogeneous of degree `-1`. -/
theorem newtonGradKernel_smul (i : Fin 2) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    newtonGradKernel i (ρ • z) = ρ⁻¹ * newtonGradKernel i z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [newtonGradKernel, coord]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  rw [newtonGradKernel, newtonGradKernel, coord_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hρ]
  field_simp

/-- **Scaling.** The `L^q(ℂ)` norm of `k_i(w) - k_i(w - ρ e)` is `ρ^{2/q - 1}` times the norm for `ρ = 1`,
by the change of variables `u = ρ w` (`MeasureTheory.Measure.map_addHaar_smul`) and homogeneity. -/
theorem eLpNorm_newtonGradKernel_sub_smul {q : ℝ≥0} (hq1 : 1 < q) (i : Fin 2) {ρ : ℝ} (hρ : 0 < ρ)
    (e : ℂ) :
    eLpNorm (fun u => newtonGradKernel i u - newtonGradKernel i (u - ρ • e)) q volume =
      ENNReal.ofReal (ρ ^ ((2 : ℝ) / q - 1)) *
        eLpNorm (fun w => newtonGradKernel i w - newtonGradKernel i (w - e)) q volume := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast zero_lt_one.trans hq1
  set fd : ℂ → ℝ := fun u => newtonGradKernel i u - newtonGradKernel i (u - ρ • e) with hfd
  have hfdm : Measurable fd :=
    (measurable_newtonGradKernel i).sub
      ((measurable_newtonGradKernel i).comp (measurable_id.sub_const _))
  have hcomp : fd ∘ (fun w : ℂ => ρ • w) =
      ρ⁻¹ • fun w => newtonGradKernel i w - newtonGradKernel i (w - e) := by
    funext w
    simp only [hfd, Function.comp, Pi.smul_apply, smul_eq_mul]
    rw [← smul_sub, newtonGradKernel_smul i hρ, newtonGradKernel_smul i hρ]
    ring
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hρ.ne'
  rw [Complex.finrank_real_complex] at hmap
  have hpos : (0 : ℝ) < |(ρ ^ 2)⁻¹| := by positivity
  have h1 : eLpNorm fd q (Measure.map (fun w : ℂ => ρ • w) volume) =
      ENNReal.ofReal ρ⁻¹ * eLpNorm (fun w => newtonGradKernel i w - newtonGradKernel i (w - e)) q
        volume := by
    rw [eLpNorm_map_measure hfdm.aestronglyMeasurable (measurable_const_smul ρ).aemeasurable,
      hcomp, eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_nonneg.2 hρ.le)]
  rw [hmap, eLpNorm_smul_measure_of_ne_zero (by simpa using hρ.ne')] at h1
  have hA : ((ρ ^ 2)⁻¹) ^ (1 / (q : ℝ)) = ρ ^ (-(2 / (q : ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hρ.le, ← Real.rpow_mul hρ.le]
    congr 1
    push_cast
    ring
  have hexp : ((1 : ℝ≥0∞) / q).toReal = 1 / (q : ℝ) := by simp
  rw [hexp, abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity)
    (by positivity), hA] at h1
  have hmul : ENNReal.ofReal (ρ ^ (-(2 / (q : ℝ)))) * ENNReal.ofReal (ρ ^ ((2 : ℝ) / q - 1)) =
      ENNReal.ofReal ρ⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hρ, show -(2 / (q : ℝ)) + (2 / q - 1) = -1
      by ring, Real.rpow_neg_one]
  have hne0 : ENNReal.ofReal (ρ ^ (-(2 / (q : ℝ)))) ≠ 0 := by
    simpa using Real.rpow_pos_of_pos hρ _
  rw [← hmul, mul_assoc] at h1
  exact ((ENNReal.mul_right_inj hne0 ENNReal.ofReal_ne_top).1 h1.symm).symm

/-- **Hölder estimate in `L^q`.** For `1 < q < 2` there is `C` with
`‖newtonGrad i x - newtonGrad i x'‖_{L^q(ℂ)} ≤ C |x - x'|^{2/q - 1}`. -/
theorem eLpNorm_newtonGrad_sub_le {q : ℝ≥0} (hq1 : 1 < q) (hq2 : q < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 2) (x x' : ℂ),
      eLpNorm (fun y => newtonGrad i x y - newtonGrad i x' y) q volume ≤
        ENNReal.ofReal (C * ‖x - x'‖ ^ ((2 : ℝ) / q - 1)) := by
  obtain ⟨M, hM, hMb⟩ := exists_eLpNorm_newtonGradKernel_sub_le hq1 hq2
  refine ⟨M.toReal, ENNReal.toReal_nonneg, fun i x x' => ?_⟩
  by_cases hxx : x = x'
  · subst hxx
    simp
  have hρ : 0 < ‖x - x'‖ := norm_pos_iff.2 (sub_ne_zero.2 hxx)
  set ρ := ‖x - x'‖ with hρdef
  set e : ℂ := ρ⁻¹ • (x' - x) with hedef
  have he : ‖e‖ = 1 := by
    rw [hedef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hρ, norm_sub_rev]
    exact inv_mul_cancel₀ hρ.ne'
  have hd : ρ • e = x' - x := by rw [hedef, smul_inv_smul₀ hρ.ne']
  have hfun : (fun y => newtonGrad i x y - newtonGrad i x' y) =
      (fun u => newtonGradKernel i u - newtonGradKernel i (u - ρ • e)) ∘ (fun y => y - x) := by
    funext y
    simp only [Function.comp, hd, newtonGrad_eq]
    congr 2
    abel
  have hmeas : AEStronglyMeasurable
      (fun u => newtonGradKernel i u - newtonGradKernel i (u - ρ • e)) volume :=
    ((measurable_newtonGradKernel i).sub
      ((measurable_newtonGradKernel i).comp (measurable_id.sub_const _))).aestronglyMeasurable
  rw [hfun, eLpNorm_comp_measurePreserving hmeas (measurePreserving_sub_right volume x),
    eLpNorm_newtonGradKernel_sub_smul hq1 i hρ e, mul_comm M.toReal,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hM]
  gcongr
  exact hMb i e he

/-- **Continuity into `L^q` of a ball.** For `1 < q < 2`, the map
`x ↦ newtonGrad i x ∈ L^q(B(c, r))` is continuous (indeed Hölder continuous of exponent `2/q - 1`). -/
theorem continuous_newtonGrad_toLp {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))] (hq1 : 1 < q) (hq2 : q < 2) (i : Fin 2) (c : ℂ)
    (r : ℝ) :
    Continuous (fun x : ℂ =>
      (memLp_newtonGrad (c := c) (r := r) hq1 hq2 i x).toLp (fun y => newtonGrad i x y) :
        ℂ → Lp ℝ q (volume.restrict (Metric.ball c r))) := by
  obtain ⟨C, hC0, hC⟩ := eLpNorm_newtonGrad_sub_le hq1 hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast zero_lt_one.trans hq1
  have hq2' : (q : ℝ) < 2 := by exact_mod_cast hq2
  have hθ : 0 < (2 : ℝ) / q - 1 := by
    rw [sub_pos, lt_div_iff₀ hq0]; linarith
  refine HolderWith.continuous (C := C.toNNReal) (r := ((2 : ℝ) / q - 1).toNNReal) ?_
    (Real.toNNReal_pos.2 hθ)
  intro x x'
  rw [Lp.edist_def]
  have hae := ((memLp_newtonGrad (c := c) (r := r) hq1 hq2 i x).coeFn_toLp).sub
    ((memLp_newtonGrad (c := c) (r := r) hq1 hq2 i x').coeFn_toLp)
  rw [eLpNorm_congr_ae hae]
  calc eLpNorm ((fun y => newtonGrad i x y) - fun y => newtonGrad i x' y) q
        (volume.restrict (ball c r))
      ≤ eLpNorm ((fun y => newtonGrad i x y) - fun y => newtonGrad i x' y) q volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ ENNReal.ofReal (C * ‖x - x'‖ ^ ((2 : ℝ) / q - 1)) := hC i x x'
    _ = (C.toNNReal : ℝ≥0∞) * edist x x' ^ ((((2 : ℝ) / q - 1).toNNReal : ℝ≥0) : ℝ) := by
        rw [ENNReal.ofReal_mul hC0, edist_dist, dist_eq_norm, Real.coe_toNNReal _ hθ.le,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hθ.le]
        rfl

end MatedCRT.GFFLocalRegularity
