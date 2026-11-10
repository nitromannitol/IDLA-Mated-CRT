import MatedCRT.FirstPass.S4S6c.OpenAnnulus68

/-!
# The good-annulus bound `hF` and the integrability `hint` of LEMMA68 on the open annulus (q2, task fp-S4S6c-envscaling-6-7-6-8)

Let `A = A_{R,2R}(z)` (`openAnnulus z R`) and let `IsGoodAnnulusEvent μ c₀ C R z` (Defs/Setting.lean:333) hold.
For a centre `w ∈ A` the event bounds the lintegral `∫⁻_A ofReal(log(R/|u-w|)+1) dμ` by the supremum over `v ∈ A`,
hence by `ofReal C · ⨅_{w' ∈ A} μ(B_{c₀R}(w'))`, and the infimum is at most its value at any `x ∈ A`. So:

* `lintegral_le_of_goodAnnulus`: `∫⁻_A ofReal(log(R/|u-w|)+1) dμ ≤ ofReal C · μ(B_{c₀R}(x))`;
* `hF_of_goodAnnulus`: `∫_A (log(R/|u-w|)+1) dμ ≤ C · mr` with `mr = μ(B_{c₀R}(x)).toReal` (LEMMA68 eq (9) form);
* `hint_of_goodAnnulus`: the integrand is integrable on `A`: on `A` we have `|u - w| ≤ 4R`, so the integrand is bounded
  below by `-log 4`, and its positive part has finite lintegral; `μ A ≠ ⊤` is an input.

Terminology: Armitage-Gardiner potential kernel `log(1/|u - v|)` (here `log(R/|u-v|)`); Duplantier-Sheffield annulus;
LQG measure `μ`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace MatedCRT

/-- The lintegral form of the good-annulus event: for `w ∈ A_{R,2R}(z)` and `x ∈ A_{R,2R}(z)`,
`∫⁻_A ofReal(log(R/|u-w|)+1) dμ ≤ ofReal C · μ(B_{c₀R}(x))`. -/
theorem lintegral_le_of_goodAnnulus {μ : Measure ℂ} {c0 C R : ℝ} {z x w : ℂ}
    (hgood : IsGoodAnnulusEvent μ c0 C R z) (hx : x ∈ openAnnulus z R) (hw : w ∈ openAnnulus z R) :
    ∫⁻ u in openAnnulus z R, ENNReal.ofReal (Real.log (R / ‖u - w‖) + 1) ∂μ
      ≤ ENNReal.ofReal C * μ (ball x (c0 * R)) := by
  unfold IsGoodAnnulusEvent at hgood
  have h1 : ∫⁻ u in openAnnulus z R, ENNReal.ofReal (Real.log (R / ‖u - w‖) + 1) ∂μ
      ≤ ⨆ v ∈ openAnnulus z R, ∫⁻ u in openAnnulus z R, ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ :=
    le_iSup₂ (f := fun v _ => ∫⁻ u in openAnnulus z R, ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ) w hw
  have h2 : ⨅ v ∈ openAnnulus z R, μ (ball v (c0 * R)) ≤ μ (ball x (c0 * R)) :=
    iInf₂_le x hx
  calc ∫⁻ u in openAnnulus z R, ENNReal.ofReal (Real.log (R / ‖u - w‖) + 1) ∂μ
      ≤ ⨆ v ∈ openAnnulus z R, ∫⁻ u in openAnnulus z R, ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ := h1
    _ ≤ ENNReal.ofReal C * ⨅ v ∈ openAnnulus z R, μ (ball v (c0 * R)) := hgood
    _ ≤ ENNReal.ofReal C * μ (ball x (c0 * R)) := by gcongr

/-- Real form: if `∫⁻_S ofReal f ≤ ofReal K` with `K ≥ 0`, then `∫_S f ≤ K`. -/
theorem integral_le_of_lintegral_le {μ : Measure ℂ} {S : Set ℂ} {f : ℂ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∫⁻ u in S, ENNReal.ofReal (f u) ∂μ ≤ ENNReal.ofReal K) :
    ∫ u in S, f u ∂μ ≤ K := by
  by_cases hf : Integrable f (μ.restrict S)
  · have h1 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf
    have h2 : (∫⁻ u in S, ENNReal.ofReal (f u) ∂μ).toReal ≤ K := by
      have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rwa [ENNReal.toReal_ofReal hK] at h'
    have h3 : 0 ≤ (∫⁻ u in S, ENNReal.ofReal (-f u) ∂μ).toReal := ENNReal.toReal_nonneg
    linarith
  · rw [integral_undef hf]
    exact hK

/-- Integrability from a lower bound and a finite positive-part lintegral on a set of finite measure. -/
theorem integrableOn_of_lintegral_ne_top {μ : Measure ℂ} {S : Set ℂ} {f : ℂ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hmeas : Measurable f) (hS : MeasurableSet S) (hμS : μ S ≠ ⊤)
    (hbelow : ∀ u ∈ S, -c ≤ f u) (hfin : ∫⁻ u in S, ENNReal.ofReal (f u) ∂μ ≠ ⊤) :
    IntegrableOn f S μ := by
  have : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hμS⟩
  have hg : Integrable (fun u => (ENNReal.ofReal (f u)).toReal + c) (μ.restrict S) :=
    (integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hmeas).aemeasurable hfin).add
      (integrable_const c)
  refine Integrable.mono' hg hmeas.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem hS ?_
  intro u hu
  have hb := hbelow u hu
  show ‖f u‖ ≤ (ENNReal.ofReal (f u)).toReal + c
  rw [ENNReal.toReal_ofReal', Real.norm_eq_abs, abs_le]
  constructor <;> linarith [le_max_left (f u) 0, le_max_right (f u) 0]

/-- The logarithmic kernel `u ↦ log(R/|u-v|) + 1` is measurable. -/
theorem measurable_logKernel_goodAnnulus (R : ℝ) (v : ℂ) :
    Measurable (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) := by
  fun_prop

/-- On the open annulus `A_{R,2R}(z)`, `|u - w| ≤ 4R`. -/
theorem norm_sub_le_four_mul_of_mem {R : ℝ} {z u w : ℂ} (hu : u ∈ openAnnulus z R)
    (hw : w ∈ openAnnulus z R) : ‖u - w‖ ≤ 4 * R := by
  rw [mem_openAnnulus] at hu hw
  have h := norm_sub_le (u - z) (w - z)
  rw [show (u - z) - (w - z) = u - w by ring] at h
  linarith [hu.2, hw.2]

/-- The logarithmic kernel is bounded below by `-log 4` at distances `0 ≤ d ≤ 4R`. -/
theorem neg_log_four_le_logKernel {R : ℝ} {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 4 * R) :
    -Real.log 4 ≤ Real.log (R / d) + 1 := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rcases hd0.eq_or_lt with h | h
  · rw [← h, div_zero, Real.log_zero]
    linarith
  · have h14 : (1 / 4 : ℝ) ≤ R / d := by
      rw [le_div_iff₀ h]
      linarith
    have h' := Real.log_le_log (by norm_num) h14
    rw [one_div, Real.log_inv] at h'
    linarith

/-- **`hF` of LEMMA68 on the open annulus** (eq (9) form, write-up B5). For a centre `w` of `A = A_{R,2R}(z)`,
`∫_A (log(R/|u-w|)+1) dμ ≤ C · mr` with `mr = μ(B_{c₀R}(x)).toReal` for any `x ∈ A`. -/
theorem hF_of_goodAnnulus {μ : Measure ℂ} {c0 C R : ℝ} {z x : ℂ} (hC : 0 ≤ C)
    (hx : x ∈ openAnnulus z R) (hgood : IsGoodAnnulusEvent μ c0 C R z)
    (hmfin : μ (ball x (c0 * R)) ≠ ⊤) :
    ∀ w ∈ openAnnulus z R, ∫ u in openAnnulus z R, (Real.log (R / ‖u - w‖) + 1) ∂μ
      ≤ C * (μ (ball x (c0 * R))).toReal := by
  intro w hw
  refine integral_le_of_lintegral_le (mul_nonneg hC ENNReal.toReal_nonneg) ?_
  have hK : ENNReal.ofReal (C * (μ (ball x (c0 * R))).toReal)
      = ENNReal.ofReal C * μ (ball x (c0 * R)) := by
    rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hmfin]
  exact (lintegral_le_of_goodAnnulus hgood hx hw).trans hK.symm.le

/-- **`hint` of LEMMA68 on the open annulus**: the logarithmic kernel with a centre in `A_{R,2R}(z)` is integrable
on `A_{R,2R}(z)` (given `μ(A) ≠ ⊤`, the good-annulus event at `x`, and `μ(B_{c₀R}(x)) ≠ ⊤`). -/
theorem hint_of_goodAnnulus {μ : Measure ℂ} {c0 C R : ℝ} {z x : ℂ}
    (hx : x ∈ openAnnulus z R) (hgood : IsGoodAnnulusEvent μ c0 C R z)
    (hmfin : μ (ball x (c0 * R)) ≠ ⊤) (hμA : μ (openAnnulus z R) ≠ ⊤) :
    ∀ v ∈ openAnnulus z R, IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) (openAnnulus z R) μ := by
  intro v hv
  refine integrableOn_of_lintegral_ne_top (c := Real.log 4) (Real.log_nonneg (by norm_num))
    (measurable_logKernel_goodAnnulus R v) (isOpen_openAnnulus z R).measurableSet hμA ?_ ?_
  · intro u hu
    exact neg_log_four_le_logKernel (norm_nonneg _) (norm_sub_le_four_mul_of_mem hu hv)
  · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmfin)
      (lintegral_le_of_goodAnnulus hgood hx hv)

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.hF_of_goodAnnulus
#print axioms MatedCRT.hint_of_goodAnnulus
