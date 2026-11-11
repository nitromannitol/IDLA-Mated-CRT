import MatedCRT.FirstPass.S2y.LateralBilin250

/-!
# FIRST PASS S2y, RadialProcL4Ae250: almost sure fourth-moment integrability of the radial version
(task fp-S2y-radial-l4, worker q2; chat 250 sec. 1.3; the second almost sure input of z8's R5)

For a whole-plane GFF `(hC, hcirc)` (`IsWholePlaneGFF`) under a probability measure `P`, almost surely
`s ↦ |radialVersion hcirc ω s| ^ 4` is integrable on `(0, n]` for every `n : ℕ`.

Route (Duplantier-Sheffield circle averages; Tonelli for the jointly measurable `radialVersion`):
* for `s > 0` the circle average `h_s(0)` is a centred Gaussian variable of variance `radialCov s s`
  (`MatedCRT.Field.wpSpace_gaussian` and `variance_eq_sub`), so `E|h_s(0)|^4 = C4 · radialCov s s ^ 2`
  with the universal constant `C4 = E|N(0,1)|^4 < ∞` (scaling of `gaussianReal`);
* `|radialCov s s| ≤ 3 |log s|` and `(log s)^2 ≤ 16 (s^{1/2} + s^{-1/2})` make `s ↦ 144 (s^{1/2} + s^{-1/2})`
  an integrable majorant of `radialCov s s ^ 2` on `(0, n]`;
* `radialVersion hcirc ω s = h_s(0)` almost surely for each `s > 0` (`radialVersion_ae_eq`), so Tonelli gives
  `∫⁻ ω, ∫⁻_{(0,n]} |radialVersion|^4 ds dP < ∞`, hence the almost sure finiteness of the inner integral.

Nothing beyond `IsWholePlaneGFF` and `IsProbabilityMeasure P` is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Set Real HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.LQGMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- `|radialCov r r| ≤ 3 |log r|` (Duplantier-Sheffield, Section 3.1): the computation of
`integral_abs_circle_zero_le`, isolated. -/
lemma abs_radialCov_diag_le (r : ℝ) :
    |MatedCRT.Field.ConeRadial.radialCov r r| ≤ 3 * |Real.log r| := by
  have hm : |Real.log (max r 1)| ≤ |Real.log r| := by
    have := abs_log_max_le r 1
    rwa [Real.log_one, abs_zero, add_zero] at this
  have e : MatedCRT.Field.ConeRadial.radialCov r r =
      Real.log (max r 1) + Real.log (max r 1) - Real.log r := by
    unfold MatedCRT.Field.ConeRadial.radialCov; rw [max_self]
  rw [e]
  calc |Real.log (max r 1) + Real.log (max r 1) - Real.log r|
      ≤ |Real.log (max r 1) + Real.log (max r 1)| + |Real.log r| := abs_sub _ _
    _ ≤ (|Real.log (max r 1)| + |Real.log (max r 1)|) + |Real.log r| := by
        gcongr; exact abs_add_le _ _
    _ ≤ 3 * |Real.log r| := by linarith

/-- `(log x)^2 ≤ 16 (x^{1/2} + x^{-1/2})` for `x > 0`, from `log x ≤ 4 x^{1/4}` and `-log x ≤ 4 x^{-1/4}`
(`Real.log_le_rpow_div`). -/
lemma sq_log_le_rpow {x : ℝ} (hx : 0 < x) :
    (Real.log x) ^ 2 ≤ 16 * (x ^ (1 / 2 : ℝ) + x ^ (-(1 / 2) : ℝ)) := by
  have hu : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hx.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hl : -Real.log x ≤ 4 * x ^ (-(1 / 4) : ℝ) := by
    have h := Real.log_le_rpow_div (inv_nonneg.2 hx.le) (by norm_num : (0 : ℝ) < 1 / 4)
    rw [Real.log_inv, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le] at h
    linarith
  have ha : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have hb : (x ^ (-(1 / 4) : ℝ)) ^ 2 = x ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have ha0 : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx.le _
  have hb0 : 0 ≤ x ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg hx.le _
  rw [← ha, ← hb]
  rcases le_total 0 (Real.log x) with h0 | h0
  · nlinarith [mul_nonneg h0 (sub_nonneg.2 hu), mul_nonneg ha0 ha0, mul_nonneg hb0 hb0]
  · nlinarith [mul_nonneg (neg_nonneg.2 h0) (sub_nonneg.2 hl), mul_nonneg ha0 ha0, mul_nonneg hb0 hb0]

/-- `radialCov s s ^ 2 ≤ 144 (s^{1/2} + s^{-1/2})` for `s > 0`. -/
lemma sq_radialCov_diag_le {s : ℝ} (hs : 0 < s) :
    (MatedCRT.Field.ConeRadial.radialCov s s) ^ 2 ≤ 144 * (s ^ (1 / 2 : ℝ) + s ^ (-(1 / 2) : ℝ)) := by
  have h1 := abs_radialCov_diag_le s
  have h2 : |MatedCRT.Field.ConeRadial.radialCov s s| ^ 2 ≤ (3 * |Real.log s|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [sq_abs, mul_pow, sq_abs] at h2
  nlinarith [sq_log_le_rpow hs]

/-- The power majorant `144 (s^{1/2} + s^{-1/2})` is integrable on `(0, n]`. -/
lemma integrableOn_rpow_majorant (n : ℕ) :
    IntegrableOn (fun s : ℝ => 144 * (s ^ (1 / 2 : ℝ) + s ^ (-(1 / 2) : ℝ))) (Ioc 0 (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : IntervalIntegrable (fun s : ℝ => s ^ (1 / 2 : ℝ)) volume 0 n :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 : IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 2) : ℝ)) volume 0 n :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  exact (((intervalIntegrable_iff_integrableOn_Ioc_of_le hn).1 h1).add
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hn).1 h2)).const_mul 144

/-- The fourth absolute moment of the standard Gaussian is finite. -/
lemma lintegral_abs_pow_four_std_lt_top :
    ∫⁻ y, ENNReal.ofReal (|y| ^ 4) ∂(gaussianReal 0 1) < ∞ := by
  have hm : MemLp id ((4 : ℕ) : ℝ≥0∞) (gaussianReal (0 : ℝ) (1 : ℝ≥0)) :=
    memLp_id_gaussianReal' _ (by simp)
  have hi : Integrable (fun y : ℝ => ‖id y‖ ^ 4) (gaussianReal 0 1) := hm.integrable_norm_pow'
  have hi' : Integrable (fun y : ℝ => |y| ^ 4) (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs] using hi
  exact hi'.lintegral_lt_top

/-- Scaling of the Gaussian fourth moment: `E|X|^4 = v^2 · E|N(0,1)|^4` for `X ∼ N(0, v)`. -/
lemma lintegral_abs_pow_four_gaussianReal (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ 4) ∂(gaussianReal 0 v) =
      ENNReal.ofReal ((v : ℝ) ^ 2) * ∫⁻ y, ENNReal.ofReal (|y| ^ 4) ∂(gaussianReal 0 1) := by
  set c : ℝ := Real.sqrt (v : ℝ) with hcdef
  have hc2 : c ^ 2 = (v : ℝ) := Real.sq_sqrt v.2
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (fun y => c * y) := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    exact NNReal.eq (by simp [hc2])
  rw [hmap, lintegral_map (((continuous_abs.measurable).pow_const 4).ennreal_ofReal) (measurable_const_mul c)]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg (v : ℝ))]
  congr 1
  have h1 : |c * y| ^ 2 = (v : ℝ) * |y| ^ 2 := by
    rw [sq_abs, sq_abs, mul_pow, hc2]
  calc |c * y| ^ 4 = (|c * y| ^ 2) ^ 2 := by ring
    _ = (v : ℝ) ^ 2 * |y| ^ 4 := by rw [h1]; ring

/-- For `s > 0` the circle average `h_s(0)` is a centred Gaussian of variance `radialCov s s`. -/
lemma circle_zero_law (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P] {s : ℝ} (hs : 0 < s) :
    ∃ v : ℝ≥0, (v : ℝ) = MatedCRT.Field.ConeRadial.radialCov s s ∧
      P.map (fun ω => hcirc ω s 0) = gaussianReal 0 v := by
  have hmem : (fun ω => hcirc ω s 0) ∈ MatedCRT.Field.wpSpace hC hcirc :=
    Submodule.subset_span ⟨⟨GFFObservable.circle s 0, hs⟩, rfl⟩
  obtain ⟨hmeas, v, hv⟩ := MatedCRT.Field.wpSpace_gaussian h _ hmem
  refine ⟨v, ?_, hv⟩
  have hvar : Var[fun ω => hcirc ω s 0; P] = v :=
    MatedCRT.Field.GaussClosure.variance_of_map_eq hmeas hv
  have hL2 := memLp_circle_zero h hs
  have e1 : ∫ ω, ((fun ω => hcirc ω s 0) ^ 2) ω ∂P = MatedCRT.Field.ConeRadial.radialCov s s :=
    integral_sq_circle_zero h hs
  have e2 : ∫ ω, (fun ω => hcirc ω s 0) ω ∂P = 0 := integral_circle_zero h hs
  rw [← hvar, variance_eq_sub hL2, e1, e2]
  ring

/-- For `s > 0`, `E|radialVersion s|^4 = C4 · radialCov s s ^ 2` (`C4 = E|N(0,1)|^4`). -/
lemma lintegral_radialVersion_pow_four (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {s : ℝ} (hs : 0 < s) :
    ∫⁻ ω, ENNReal.ofReal (|MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) ∂P =
      ENNReal.ofReal ((MatedCRT.Field.ConeRadial.radialCov s s) ^ 2) *
        ∫⁻ y, ENNReal.ofReal (|y| ^ 4) ∂(gaussianReal 0 1) := by
  obtain ⟨v, hvr, hmap⟩ := circle_zero_law h hs
  have hY : Measurable (fun ω => hcirc ω s 0) := h.measurable_circle s 0 hs
  have hae : (fun ω => ENNReal.ofReal (|MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4)) =ᵐ[P]
      fun ω => ENNReal.ofReal (|hcirc ω s 0| ^ 4) := by
    filter_upwards [radialVersion_ae_eq h hs] with ω hω
    rw [hω]
  rw [lintegral_congr_ae hae, ← lintegral_map (((continuous_abs.measurable).pow_const 4).ennreal_ofReal) hY,
    hmap, lintegral_abs_pow_four_gaussianReal, hvr]

/-- **Almost sure fourth-moment integrability of the radial version.** For a whole-plane GFF under a
probability measure, almost surely `s ↦ |radialVersion hcirc ω s| ^ 4` is integrable on `(0, n]` for every
`n : ℕ`. -/
theorem ae_integrableOn_radialVersion_pow_four [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      IntegrableOn (fun s => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) (Set.Ioc 0 (n : ℝ)) := by
  have hX : Measurable (fun p : Ω × ℝ => MatedCRT.CirclePairing.radialVersion hcirc p.1 p.2) :=
    MatedCRT.CirclePairing.measurable_radialVersion h.measurable_circle
  have hFm : Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal (|MatedCRT.CirclePairing.radialVersion hcirc p.1 p.2| ^ 4)) :=
    (((continuous_abs.measurable).comp hX).pow_const 4).ennreal_ofReal
  have hC4 := lintegral_abs_pow_four_std_lt_top
  have key : ∀ n : ℕ, ∫⁻ ω, (∫⁻ s in Ioc 0 (n : ℝ),
      ENNReal.ofReal (|MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4)) ∂P < ∞ := by
    intro n
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    have hmaj : ∫⁻ s in Ioc 0 (n : ℝ),
        ENNReal.ofReal (144 * (s ^ (1 / 2 : ℝ) + s ^ (-(1 / 2) : ℝ))) < ∞ :=
      (integrableOn_rpow_majorant n).lintegral_lt_top
    calc ∫⁻ s in Ioc 0 (n : ℝ), ∫⁻ ω,
          ENNReal.ofReal (|MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) ∂P
        ≤ ∫⁻ s in Ioc 0 (n : ℝ), ENNReal.ofReal (144 * (s ^ (1 / 2 : ℝ) + s ^ (-(1 / 2) : ℝ))) *
            ∫⁻ y, ENNReal.ofReal (|y| ^ 4) ∂(gaussianReal 0 1) := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
          rw [lintegral_radialVersion_pow_four h hs.1]
          gcongr; exact sq_radialCov_diag_le hs.1
      _ = (∫⁻ s in Ioc 0 (n : ℝ), ENNReal.ofReal (144 * (s ^ (1 / 2 : ℝ) + s ^ (-(1 / 2) : ℝ)))) *
            ∫⁻ y, ENNReal.ofReal (|y| ^ 4) ∂(gaussianReal 0 1) :=
          lintegral_mul_const' _ _ hC4.ne
      _ < ∞ := ENNReal.mul_lt_top hmaj hC4
  have hae : ∀ᵐ ω ∂P, ∀ n : ℕ, (∫⁻ s in Ioc 0 (n : ℝ),
      ENNReal.ofReal (|MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4)) < ∞ := by
    refine ae_all_iff.2 fun n => ?_
    exact ae_lt_top hFm.lintegral_prod_right' (key n).ne
  filter_upwards [hae] with ω hω
  intro n
  have hmeas : Measurable (fun s : ℝ => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) :=
    ((continuous_abs.measurable).comp (hX.comp measurable_prodMk_left)).pow_const 4
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hlt := hω n
  unfold HasFiniteIntegral
  refine lt_of_eq_of_lt (lintegral_congr fun s => ?_) hlt
  rw [Real.enorm_eq_ofReal (pow_nonneg (abs_nonneg _) 4)]

end MatedCRT.LQGMeasure
