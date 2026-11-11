import MatedCRT.Defs.QuantumCone
import HarmonicBalls.Proofs.GFF.MeasurableContinuousCircleVersion

/-!
# Radial integrals and lateral pairings of the whole-plane GFF

For a whole-plane Gaussian free field `(hC, hcirc)` (`HarmonicBalls.IsWholePlaneGFF`, normalized so that
`h^ℂ_1(0) = 0`), the radial integral `∫ φ(x) h_{|x|}(0) dx` of a test function `φ` and the lateral pairing
`hC φ - ∫ φ(x) h_{|x|}(0) dx` (the field minus its radial part, `MatedCRT.lateralEval`).

This file proves:
* the circle-average covariance identities for the kernel `HarmonicBalls.wholePlaneCov`
  (Duplantier-Sheffield 2011, Section 3.1; mean value property of `log |· - z|`);
* a measurable version of the circle-average process on `ℂ \ {0}`, and the almost sure identification of the
  radial integral with a measurable functional of that version.

References: Duplantier-Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
arXiv:0808.1560, Section 3.1; Armitage-Gardiner, *Classical Potential Theory*, Section 3.1 (logarithmic potential
of a circle).
-/

noncomputable section

namespace MatedCRT.WholePlaneGFFLateral

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- Average of `w ↦ log ‖w - z‖` over `∂B_r(0)`: the logarithmic mean value property, `log max(r, |z|)`. -/
lemma circleAverage_log_norm_sub_eq {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Real.circleAverage (fun w : ℂ => Real.log ‖w - z‖) 0 r = Real.log (max r ‖z‖) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (c := (0 : ℂ)) (a := z) hr.ne'
  rw [h, zero_sub, norm_neg]
  rcases le_total ‖z‖ r with hz | hz
  · rw [max_eq_left hz]
    have hle : r⁻¹ * ‖z‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ hr, mul_one]; exact hz
    have hpos : Real.posLog (r⁻¹ * ‖z‖) = 0 := by
      unfold Real.posLog
      exact max_eq_left (Real.log_nonpos (by positivity) hle)
    rw [hpos, add_zero]
  · rw [max_eq_right hz]
    have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hr hz
    have h1 : 1 ≤ r⁻¹ * ‖z‖ := by
      rw [inv_mul_eq_div, one_le_div hr]; exact hz
    have hpos : Real.posLog (r⁻¹ * ‖z‖) = Real.log (r⁻¹ * ‖z‖) := by
      unfold Real.posLog
      exact max_eq_right (Real.log_nonneg h1)
    rw [hpos, Real.log_mul (inv_ne_zero hr.ne') hz0.ne', Real.log_inv]
    ring

/-- The circle average of the covariance kernel `wholePlaneCov z ·` over `∂B_r(0)`, for every `z ∈ ℂ`
(Duplantier-Sheffield 2011, Section 3.1; the mean value property of `log |· - z|`). The point `w = z` of the
circle, where `wholePlaneCov` takes the junk value `0`, is a single point of the codiscrete filter and does not
contribute. -/
lemma circleAverage_wholePlaneCov {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r =
      Real.log (max ‖z‖ 1) + Real.log (max r 1) - Real.log (max r ‖z‖) := by
  have hA : max ‖z‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hB : max r 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hgood : (Metric.sphere (0 : ℂ) |r| \ {z}) ∈ codiscreteWithin (Metric.sphere (0 : ℂ) |r|) := by
    rw [codiscreteWithin_iff_locallyFiniteComplementWithin]
    intro x _
    refine ⟨univ, univ_mem, (Set.finite_singleton z).subset ?_⟩
    rintro y ⟨-, hyS, hy⟩
    exact Set.mem_singleton_iff.mp (not_not.mp fun hne => hy ⟨hyS, hne⟩)
  have hcod : (fun w : ℂ => wholePlaneCov z w) =ᶠ[codiscreteWithin (Metric.sphere (0 : ℂ) |r|)]
      (fun w : ℂ => Real.log (max ‖z‖ 1) + Real.log (max r 1) - Real.log ‖w - z‖) := by
    filter_upwards [hgood] with w hw
    obtain ⟨hwS, hwz⟩ := hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hwS
    have hwz' : ‖z - w‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      exact fun h => hwz (Set.mem_singleton_iff.mpr h.symm)
    unfold wholePlaneCov
    rw [hwS, Real.log_div (mul_ne_zero hA hB) hwz', Real.log_mul hA hB, norm_sub_rev]
  have h1 : CircleIntegrable (fun _ : ℂ => Real.log (max ‖z‖ 1) + Real.log (max r 1)) 0 r := by
    unfold CircleIntegrable
    exact intervalIntegrable_const
  have h2 : CircleIntegrable (fun w : ℂ => Real.log ‖w - z‖) 0 r :=
    circleIntegrable_log_norm_sub_const (c := (0 : ℂ)) (a := z) r
  rw [Real.circleAverage_congr_codiscreteWithin hcod hr.ne']
  have key := Real.circleAverage_fun_sub h1 h2
  beta_reduce at key
  rw [key, Real.circleAverage_const, circleAverage_log_norm_sub_eq hr z]

/-- Circle averages of `z ↦ circleAverage (wholePlaneCov z ·) 0 r` over `∂B_s(0)` for `s ≠ r`:
the circle-circle covariance `log max(s,1) + log max(r,1) - log max(r,s)` (Duplantier-Sheffield 2011, eq. (3.2)). -/
lemma circleAverage_circleAverage_wholePlaneCov {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Real.circleAverage (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r) 0 s =
      Real.log (max s 1) + Real.log (max r 1) - Real.log (max r s) := by
  have hc : EqOn (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r)
      (fun _ : ℂ => Real.log (max s 1) + Real.log (max r 1) - Real.log (max r s))
      (Metric.sphere (0 : ℂ) |s|) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hs] at hz
    dsimp only
    rw [circleAverage_wholePlaneCov hr z, hz]
  rw [Real.circleAverage_congr_sphere hc, Real.circleAverage_const]

/-- The pairing covariance with a circle average, as the smear of the observable (Harmonic-Balls `wholePlaneGFFCov`). -/
lemma wholePlaneGFFCov_pairing_circle (φ : ℂ → ℝ) (r : ℝ) :
    wholePlaneGFFCov (.pairing φ) (.circle r 0) =
      ∫ x, φ x * Real.circleAverage (fun w : ℂ => wholePlaneCov x w) 0 r := rfl

/-- The circle-circle covariance as an iterated circle average (Harmonic-Balls `wholePlaneGFFCov`). -/
lemma wholePlaneGFFCov_circle_circle (s r : ℝ) :
    wholePlaneGFFCov (.circle s 0) (.circle r 0) =
      Real.circleAverage (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r) 0 s := rfl

/-- The point `(max(|x|,·), 0)` of the circle-parameter space at which the measurable version is evaluated;
it equals `(|x|, 0)` for `x ≠ 0`. -/
def radialPoint (x : ℂ) : CircleParameter :=
  (⟨if x = 0 then 1 else ‖x‖, by
    split_ifs with h
    · norm_num
    · exact norm_pos_iff.2 h⟩, 0)

lemma measurable_radialPoint : Measurable radialPoint := by
  refine Measurable.prodMk ?_ measurable_const
  refine Measurable.subtype_mk ?_
  exact Measurable.ite (measurableSet_singleton (0 : ℂ)) measurable_const measurable_norm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable version of the circle-average process: on the almost sure event where all circle averages are
continuous, the version `F` agrees with `hcirc` at every point of `(0,∞) × ℂ` (continuity and countable density). -/
lemma exists_ae_circle_version {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) :
    ∃ F : Ω → C(CircleParameter, ℝ), Measurable F ∧
      ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2 := by
  obtain ⟨F, hFm, -, hF⟩ := h.exists_measurable_continuous_circle_version
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense CircleParameter
  refine ⟨F, hFm, ?_⟩
  have hD : ∀ᵐ ω ∂P, ∀ p ∈ D, F ω p = hcirc ω (p.1 : ℝ) p.2 :=
    (ae_ball_iff hDc).2 fun p _ => hF p
  filter_upwards [hD, h.ae_continuousOn_circle] with ω hω hcont
  have hfun : Continuous (fun p : CircleParameter => hcirc ω (p.1 : ℝ) p.2) := by
    have hmap : Continuous (fun p : CircleParameter => ((p.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact hcont.comp_continuous hmap (fun p => ⟨p.1.2, mem_univ _⟩)
  have heq := Continuous.ext_on hDd (F ω).continuous hfun (fun p hp => hω p hp)
  intro p
  exact congrFun heq p

/-- Joint measurability and measurability in `ω` of the radial functional `ω ↦ ∫ φ(x) F(ω)(|x|,0) dx`. -/
lemma measurable_radialIntegral_version {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    {φ : ℂ → ℝ} (hφ : Measurable φ) :
    Measurable fun ω => ∫ x, φ x * F ω (radialPoint x) := by
  have hjoint : Measurable (fun q : Ω × ℂ => φ q.2 * F q.1 (radialPoint q.2)) := by
    refine Measurable.mul (hφ.comp measurable_snd) ?_
    exact (measurable_circle_version_joint hF).comp
      (measurable_fst.prodMk (measurable_radialPoint.comp measurable_snd))
  exact (hjoint.stronglyMeasurable.integral_prod_right (ν := volume)).measurable

/-- Almost surely, the radial integral of `hcirc` is the radial integral of the measurable version. -/
lemma ae_radialIntegral_eq {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ}
    {F : Ω → C(CircleParameter, ℝ)} (hF : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    (φ : ℂ → ℝ) :
    ∀ᵐ ω ∂P, ∫ x, φ x * hcirc ω ‖x‖ 0 = ∫ x, φ x * F ω (radialPoint x) := by
  filter_upwards [hF] with ω hω
  apply integral_congr_ae
  have h0 : ∀ᵐ x : ℂ ∂(volume : Measure ℂ), x ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with x hx
  congr 1
  rw [hω (radialPoint x)]
  simp [radialPoint, hx]

/-! ### Second moments and the covariance of circle averages and pairings -/

section Covariances

variable {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Circle averages of positive radius are square integrable (Gaussian observables). -/
lemma memLp_two_circle (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    MemLp (fun ω => hcirc ω r z) 2 P :=
  (h.isGaussianProcess.hasGaussianLaw_eval ⟨.circle r z, hr⟩).memLp_two

/-- Pairings with test functions are square integrable (Gaussian observables). -/
lemma memLp_two_pairing (h : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) : MemLp (fun ω => hC ω φ) 2 P :=
  (h.isGaussianProcess.hasGaussianLaw_eval ⟨.pairing φ, hφ⟩).memLp_two

/-- For a centred second variable, the covariance is the mean of the product. -/
lemma covariance_eq_integral_of_mean_zero {X Y : Ω → ℝ} (hY : ∫ ω, Y ω ∂P = 0)
    (hYi : Integrable Y P) (hXY : Integrable (fun ω => X ω * Y ω) P) :
    covariance X Y P = ∫ ω, X ω * Y ω ∂P := by
  unfold covariance
  have hpt : ∀ ω, (X ω - ∫ ω, X ω ∂P) * (Y ω - ∫ ω, Y ω ∂P) =
      X ω * Y ω - (∫ ω, X ω ∂P) * Y ω := by
    intro ω
    rw [hY]
    ring
  simp_rw [hpt]
  rw [integral_sub hXY (hYi.const_mul _), integral_const_mul, hY, mul_zero, sub_zero]

/-- The covariance of two circle averages at `0` is the circle-circle kernel
(Duplantier-Sheffield 2011, eq. (3.2); Armitage-Gardiner, mean value property of `log|·-z|`). -/
lemma integral_circle_mul_circle [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∫ ω, hcirc ω s 0 * hcirc ω r 0 ∂P =
      Real.circleAverage (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r) 0 s := by
  have hc : covariance (fun ω => hcirc ω s 0) (fun ω => hcirc ω r 0) P =
      Real.circleAverage (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r) 0 s :=
    h.covariance_eq (.circle s 0) (.circle r 0) hs hr
  have hY : ∫ ω, hcirc ω r 0 ∂P = 0 := h.integral_eq_zero (.circle r 0) hr
  have hYi : Integrable (fun ω => hcirc ω r 0) P :=
    (memLp_two_circle h hr 0).integrable one_le_two
  have hXY : Integrable (fun ω => hcirc ω s 0 * hcirc ω r 0) P :=
    (memLp_two_circle h hs 0).integrable_mul (memLp_two_circle h hr 0)
  rw [covariance_eq_integral_of_mean_zero hY hYi hXY] at hc
  exact hc

/-- The covariance of a pairing with a circle average is the integral of the kernel against the test function. -/
lemma integral_pairing_mul_circle [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) {r : ℝ} (hr : 0 < r) :
    ∫ ω, hC ω φ * hcirc ω r 0 ∂P =
      ∫ x, φ x * Real.circleAverage (fun w : ℂ => wholePlaneCov x w) 0 r := by
  have hc : covariance (fun ω => hC ω φ) (fun ω => hcirc ω r 0) P =
      ∫ x, φ x * Real.circleAverage (fun w : ℂ => wholePlaneCov x w) 0 r :=
    h.covariance_eq (.pairing φ) (.circle r 0) hφ hr
  have hY : ∫ ω, hcirc ω r 0 ∂P = 0 := h.integral_eq_zero (.circle r 0) hr
  have hYi : Integrable (fun ω => hcirc ω r 0) P :=
    (memLp_two_circle h hr 0).integrable one_le_two
  have hXY : Integrable (fun ω => hC ω φ * hcirc ω r 0) P :=
    (memLp_two_pairing h hφ).integrable_mul (memLp_two_circle h hr 0)
  rw [covariance_eq_integral_of_mean_zero hY hYi hXY] at hc
  exact hc

end Covariances

/-! ### Logarithmic integrability near the origin -/

/-- `|log t| ≤ 2 (1 + R) t^{-1/2}` on `(0, R]` (elementary: `log u ≤ u - 1`). -/
lemma abs_log_le_rpow_neg_half {t R : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    |Real.log t| ≤ 2 * (1 + R) * t ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hrp : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
  rw [hrp, abs_le]
  have hlog : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [Real.log_sqrt ht.le]; ring
  have hup : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hs
  have hlo : Real.log (Real.sqrt t)⁻¹ ≤ (Real.sqrt t)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.2 hs)
  rw [Real.log_inv] at hlo
  have hsR : Real.sqrt t ≤ R * (Real.sqrt t)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hs]
    nlinarith
  have hinv_pos : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 hs
  constructor
  · nlinarith
  · nlinarith

/-- `x ↦ φ x * log ‖x‖` is integrable for a test function `φ` (logarithmic singularity at `0`). -/
lemma integrable_test_mul_log_norm {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Integrable (fun x : ℂ => φ x * Real.log ‖x‖) := by
  obtain ⟨hc, hcs, -⟩ := hφ
  obtain ⟨R, hR⟩ := isBounded_iff_subset_closedBall (0 : ℂ) |>.1 hcs.isCompact.isBounded
  obtain ⟨M, hM⟩ := hc.continuous.bounded_above_of_compact_support hcs
  have hsub : tsupport φ ⊆ ball (0 : ℂ) (R + 1) := hR.trans (closedBall_subset_ball (by linarith))
  have hsupp : Function.support (fun x : ℂ => φ x * Real.log ‖x‖) ⊆ ball (0 : ℂ) (R + 1) := by
    intro x hx
    apply hsub
    apply subset_tsupport
    intro h0
    apply hx
    simp [h0]
  have hd : 1 ≤ Module.finrank ℝ ℂ := by simp
  have hα : (1 / 2 : ℝ) < (Module.finrank ℝ ℂ : ℝ) := by simp; norm_num
  have hmeas : AEStronglyMeasurable (fun x : ℂ => φ x * Real.log ‖x‖) volume :=
    (hc.continuous.measurable.mul (Real.measurable_log.comp measurable_norm)).aestronglyMeasurable
  have hdecay : ∀ᵐ x ∂(volume.restrict (ball (0 : ℂ) (R + 1))),
      ‖φ x * Real.log ‖x‖‖ ≤ (M * (2 * (1 + |R + 1|))) * ‖x‖ ^ (-(1 / 2 : ℝ)) := by
    refine ae_of_all _ fun x => ?_
    rcases eq_or_ne ‖x‖ 0 with h0 | h0
    · have : x = 0 := norm_eq_zero.1 h0
      subst this
      simp
    · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      by_cases hx : ‖x‖ ≤ R + 1
      · rw [norm_mul, Real.norm_eq_abs]
        have h1 := abs_log_le_rpow_neg_half hxpos hx
        have h2 : ‖φ x‖ ≤ M := hM x
        have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
        have h3 : 0 ≤ ‖x‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
        calc ‖φ x‖ * |Real.log ‖x‖| ≤ M * (2 * (1 + (R + 1)) * ‖x‖ ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul h2 h1 (abs_nonneg _) ((norm_nonneg _).trans h2)
          _ = (M * (2 * (1 + (R + 1)))) * ‖x‖ ^ (-(1 / 2 : ℝ)) := by ring
          _ ≤ (M * (2 * (1 + |R + 1|))) * ‖x‖ ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (by linarith [le_abs_self (R + 1)]) hM0) h3
      · have hout : x ∉ tsupport φ := fun hxt => hx (by
          have := hR hxt
          rw [mem_closedBall, dist_zero_right] at this
          linarith)
        have : φ x = 0 := image_eq_zero_of_notMem_tsupport hout
        have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
        simp only [this, zero_mul, norm_zero]
        exact mul_nonneg (mul_nonneg hM0 (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
  have hloc : IntegrableOn (fun x : ℂ => φ x * Real.log ‖x‖) (ball (0 : ℂ) (R + 1)) :=
    integrableOn_ball_of_norm_le_rpow hd hα hdecay hmeas
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hloc

/-! ### Joint integrability of the radial integral against a circle average -/

/-- The diagonal circle-circle covariance `2 log max(|x|,1) - log |x|` is nonnegative. -/
lemma diag_nonneg (x : ℂ) : 0 ≤ 2 * Real.log (max ‖x‖ 1) - Real.log ‖x‖ := by
  rcases le_total ‖x‖ 1 with h | h
  · rw [max_eq_right h, Real.log_one]
    have : Real.log ‖x‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) h
    linarith
  · rw [max_eq_left h]
    have : 0 ≤ Real.log ‖x‖ := Real.log_nonneg h
    linarith

/-- `|φ(x)| (2 log max(|x|,1) - log |x|)` is integrable for a test function `φ`. -/
lemma integrable_abs_test_mul_diag {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Integrable (fun x : ℂ => |φ x| * (2 * Real.log (max ‖x‖ 1) - Real.log ‖x‖)) := by
  have hcont : Continuous (fun x : ℂ => φ x * Real.log (max ‖x‖ 1)) := by
    refine hφ.1.continuous.mul (Continuous.log (continuous_norm.max continuous_const) fun x => ?_)
    exact (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have h1 : Integrable (fun x : ℂ => φ x * Real.log (max ‖x‖ 1)) :=
    hcont.integrable_of_hasCompactSupport (hφ.2.1.mul_right)
  have h2 := (h1.const_mul 2).sub (integrable_test_mul_log_norm hφ)
  have h3 : Integrable (fun x : ℂ => φ x * (2 * Real.log (max ‖x‖ 1) - Real.log ‖x‖)) :=
    h2.congr (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)
  refine (h3.abs).congr (ae_of_all _ fun x => ?_)
  simp only
  rw [abs_mul, abs_of_nonneg (diag_nonneg x)]

section Radial

variable {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Square integrability of the radial functional at every point of the circle parameter space. -/
lemma memLp_two_radialPoint (h : IsWholePlaneGFF P hC hcirc)
    {F : Ω → C(CircleParameter, ℝ)} (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    (y : ℂ) : MemLp (fun ω => F ω (radialPoint y)) 2 P :=
  (memLp_two_circle h (radialPoint y).1.2 0).ae_eq (by
    filter_upwards [hFae] with ω hω
    exact (hω (radialPoint y)).symm)

/-- The radial product `(ω, x) ↦ φ(x) h_{|x|}(0) h_r(0)` is integrable for the product of `P` and Lebesgue
measure. It is dominated by `|φ(x)| (h_{|x|}(0)² + h_r(0)²)`, whose integral over `ω` is
`|φ(x)| (2 log max(|x|,1) - log |x| + 2 log max(r,1) - log r)` by the diagonal circle-circle covariance. -/
lemma integrable_radial_mul [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc)
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ : MemLp Z 2 P) {c : ℝ} (hc : ∫ ω, Z ω ^ 2 ∂P = c) :
    Integrable (fun q : Ω × ℂ => φ q.2 * F q.1 (radialPoint q.2) * Z q.1) (P.prod volume) := by
  have hmF : Measurable (fun q : Ω × ℂ => F q.1 (radialPoint q.2)) :=
    (measurable_circle_version_joint hF).comp
      (measurable_fst.prodMk (measurable_radialPoint.comp measurable_snd))
  have hmY : Measurable (fun q : Ω × ℂ => Z q.1) := hZm.comp measurable_fst
  have hmφ : Measurable (fun q : Ω × ℂ => φ q.2) := hφ.1.continuous.measurable.comp measurable_snd
  set G : Ω × ℂ → ℝ := fun q => |φ q.2| * ((F q.1 (radialPoint q.2)) ^ 2 + (Z q.1) ^ 2)
    with hG
  have hGmeas : Measurable G := (hmφ.abs).mul ((hmF.pow_const 2).add (hmY.pow_const 2))
  have hGnn : ∀ q, 0 ≤ G q := fun q =>
    mul_nonneg (abs_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hGint : Integrable G (P.prod volume) := by
    rw [integrable_prod_iff' hGmeas.aestronglyMeasurable]
    constructor
    · refine ae_of_all _ fun y => ?_
      show Integrable (fun ω => |φ y| * ((F ω (radialPoint y)) ^ 2 + (Z ω) ^ 2)) P
      exact (((memLp_two_radialPoint h hFae y).integrable_sq.add hZ.integrable_sq).const_mul _)
    · have hφabs : Integrable (fun y : ℂ => |φ y|) :=
        (Continuous.integrable_of_hasCompactSupport hφ.1.continuous hφ.2.1).abs
      have hsum := (integrable_abs_test_mul_diag hφ).add (hφabs.mul_const c)
      have h0 : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ 0 := by
        rw [ae_iff]; simp
      have key : ∀ᵐ y ∂(volume : Measure ℂ), ∫ ω, ‖G (ω, y)‖ ∂P =
          |φ y| * ((2 * Real.log (max ‖y‖ 1) - Real.log ‖y‖) + c) := by
        filter_upwards [h0] with y hy
        have hs : 0 < ‖y‖ := norm_pos_iff.2 hy
        have hsy : ((radialPoint y).1 : ℝ) = ‖y‖ := by simp [radialPoint, hy]
        have hnorm : ∀ ω, ‖G (ω, y)‖ = |φ y| * ((F ω (radialPoint y)) ^ 2 + (Z ω) ^ 2) := by
          intro ω
          rw [Real.norm_of_nonneg (hGnn _)]
        have hFsq : ∫ ω, (F ω (radialPoint y)) ^ 2 ∂P = 2 * Real.log (max ‖y‖ 1) - Real.log ‖y‖ := by
          have : ∫ ω, (F ω (radialPoint y)) ^ 2 ∂P = ∫ ω, hcirc ω ‖y‖ 0 * hcirc ω ‖y‖ 0 ∂P := by
            refine integral_congr_ae ?_
            filter_upwards [hFae] with ω hω
            rw [hω (radialPoint y), hsy, sq]
            rfl
          rw [this, integral_circle_mul_circle h hs hs, circleAverage_circleAverage_wholePlaneCov hs hs,
            max_self]
          ring
        have hint : ∫ ω, ‖G (ω, y)‖ ∂P = |φ y| * (∫ ω, (F ω (radialPoint y)) ^ 2 ∂P
            + ∫ ω, Z ω ^ 2 ∂P) := by
          simp_rw [hnorm]
          rw [integral_const_mul, integral_add ((memLp_two_radialPoint h hFae y).integrable_sq)
            hZ.integrable_sq]
        rw [hint, hFsq, hc]
      refine hsum.congr (key.mono fun y hy => ?_)
      simp only [Pi.add_apply]
      rw [hy]
      ring
  have hmeasf : AEStronglyMeasurable (fun q : Ω × ℂ => φ q.2 * F q.1 (radialPoint q.2) * Z q.1)
      (P.prod volume) :=
    (((hmφ.mul hmF).mul hmY)).aestronglyMeasurable
  refine Integrable.mono' (hGint.div_const 2) hmeasf (ae_of_all _ fun q => ?_)
  obtain ⟨ω, x⟩ := q
  simp only [hG]
  have hFY : |F ω (radialPoint x)| * |Z ω| ≤ (F ω (radialPoint x) ^ 2 + Z ω ^ 2) / 2 := by
    nlinarith [sq_abs (F ω (radialPoint x)), sq_abs (Z ω),
      sq_nonneg (|F ω (radialPoint x)| - |Z ω|)]
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc |φ x| * |F ω (radialPoint x)| * |Z ω|
      = |φ x| * (|F ω (radialPoint x)| * |Z ω|) := by ring
    _ ≤ |φ x| * ((F ω (radialPoint x) ^ 2 + Z ω ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hFY (abs_nonneg _)
    _ = |φ x| * (F ω (radialPoint x) ^ 2 + Z ω ^ 2) / 2 := by ring


/-- The radial product with a circle average `h_r(0)`: the case `Z = h_r(0)` of `integrable_radial_mul`. -/
lemma integrable_radial_mul_circle [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc)
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun q : Ω × ℂ => φ q.2 * F q.1 (radialPoint q.2) * hcirc q.1 r 0) (P.prod volume) := by
  have hYsq : ∫ ω, (hcirc ω r 0) ^ 2 ∂P = 2 * Real.log (max r 1) - Real.log r := by
    have : ∫ ω, (hcirc ω r 0) ^ 2 ∂P = ∫ ω, hcirc ω r 0 * hcirc ω r 0 ∂P := by
      simp only [sq]
    rw [this, integral_circle_mul_circle h hr hr, circleAverage_circleAverage_wholePlaneCov hr hr,
      max_self]
    ring
  exact integrable_radial_mul h hF hFae hφ (h.measurable_circle r 0 hr) (memLp_two_circle h hr 0) hYsq

/-- **N1 (zero cross-covariance of the lateral part).** For a test function `φ` supported in `B_1` and a circle
average `h_r(0)` of positive radius, the lateral pairing `hC φ - ∫ φ(x) h_{|x|}(0) dx` is uncorrelated with
`h_r(0)` (Duplantier-Sheffield 2011, Section 3.1; the covariance of `h_{|x|}(0)` with `h_r(0)` is the circle-circle
kernel `log max(|x|,1) + log max(r,1) - log max(r,|x|)`, integrated against `φ`). -/
theorem covariance_lateral_pairing_circle [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc)
    {φ : ℂ → ℝ} (hφ : IsTestFunction (Metric.ball (0 : ℂ) 1) φ) {r : ℝ} (hr : 0 < r) :
    covariance (fun ω => hC ω φ - ∫ x, φ x * hcirc ω ‖x‖ 0) (fun ω => hcirc ω r 0) P = 0 := by
  have hφU : IsTestFunction Set.univ φ := ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
  obtain ⟨F, hF, hFae⟩ := exists_ae_circle_version h
  have hLae : ∀ᵐ ω ∂P, (∫ x, φ x * hcirc ω ‖x‖ 0) = ∫ x, φ x * F ω (radialPoint x) :=
    ae_radialIntegral_eq hFae φ
  have hY : ∫ ω, hcirc ω r 0 ∂P = 0 := h.integral_eq_zero (.circle r 0) hr
  have hYi : Integrable (fun ω => hcirc ω r 0) P := (memLp_two_circle h hr 0).integrable one_le_two
  have hI3 := integrable_radial_mul_circle h hF hFae hφU hr
  have h1 : Integrable (fun ω => hC ω φ * hcirc ω r 0) P :=
    (memLp_two_pairing h hφU).integrable_mul (memLp_two_circle h hr 0)
  have hLY' : Integrable (fun ω => (∫ x, φ x * F ω (radialPoint x)) * hcirc ω r 0) P := by
    refine hI3.integral_prod_left.congr (ae_of_all _ fun ω => ?_)
    dsimp only
    rw [integral_mul_const]
  have h2 : Integrable (fun ω => (∫ x, φ x * hcirc ω ‖x‖ 0) * hcirc ω r 0) P :=
    hLY'.congr (by filter_upwards [hLae] with ω hω; rw [hω])
  have hXY : Integrable (fun ω => (hC ω φ - ∫ x, φ x * hcirc ω ‖x‖ 0) * hcirc ω r 0) P :=
    (h1.sub h2).congr (ae_of_all _ fun ω => by simp only [Pi.sub_apply]; ring)
  rw [covariance_eq_integral_of_mean_zero hY hYi hXY]
  have e1 : ∫ ω, (hC ω φ - ∫ x, φ x * hcirc ω ‖x‖ 0) * hcirc ω r 0 ∂P =
      ∫ ω, hC ω φ * hcirc ω r 0 ∂P - ∫ ω, (∫ x, φ x * hcirc ω ‖x‖ 0) * hcirc ω r 0 ∂P := by
    rw [← integral_sub h1 h2]
    congr 1
    ext ω
    ring
  have e2 : ∫ ω, (∫ x, φ x * hcirc ω ‖x‖ 0) * hcirc ω r 0 ∂P =
      ∫ ω, (∫ x, φ x * F ω (radialPoint x)) * hcirc ω r 0 ∂P :=
    integral_congr_ae (by filter_upwards [hLae] with ω hω; rw [hω])
  have step1 : ∀ ω, (∫ x, φ x * F ω (radialPoint x)) * hcirc ω r 0 =
      ∫ x, φ x * F ω (radialPoint x) * hcirc ω r 0 := fun ω => (integral_mul_const _ _).symm
  have e3 : ∫ ω, (∫ x, φ x * F ω (radialPoint x)) * hcirc ω r 0 ∂P =
      ∫ x, φ x * ∫ ω, F ω (radialPoint x) * hcirc ω r 0 ∂P := by
    simp only [step1]
    rw [integral_integral_swap (f := fun ω x => φ x * F ω (radialPoint x) * hcirc ω r 0) hI3]
    congr 1
    ext x
    rw [← integral_const_mul]
    congr 1
    ext ω
    ring
  have e4 : ∀ x : ℂ, x ≠ 0 → ∫ ω, F ω (radialPoint x) * hcirc ω r 0 ∂P =
      Real.circleAverage (fun w : ℂ => wholePlaneCov x w) 0 r := by
    intro x hx
    have hs : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hrp : ((radialPoint x).1 : ℝ) = ‖x‖ := by simp [radialPoint, hx]
    have hswap : ∫ ω, F ω (radialPoint x) * hcirc ω r 0 ∂P = ∫ ω, hcirc ω ‖x‖ 0 * hcirc ω r 0 ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hFae] with ω hω
      have := hω (radialPoint x)
      rw [hrp] at this
      exact congrArg (· * hcirc ω r 0) this
    rw [hswap, integral_circle_mul_circle h hs hr, circleAverage_circleAverage_wholePlaneCov hr hs,
      circleAverage_wholePlaneCov hr x]
  have h0 : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ 0 := by
    rw [ae_iff]; simp
  have e5 : ∫ x, φ x * ∫ ω, F ω (radialPoint x) * hcirc ω r 0 ∂P =
      ∫ x, φ x * Real.circleAverage (fun w : ℂ => wholePlaneCov x w) 0 r := by
    refine integral_congr_ae (h0.mono fun x hx => ?_)
    dsimp only
    rw [e4 x hx]
  rw [e1, e2, e3, e5, integral_pairing_mul_circle h hφU hr, sub_self]

end Radial

end MatedCRT.WholePlaneGFFLateral
