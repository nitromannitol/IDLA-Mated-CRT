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

/-- The circle average of the covariance kernel `wholePlaneCov z ·` over `∂B_r(0)`, for `|z| ≠ r`. -/
lemma circleAverage_wholePlaneCov_of_ne {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≠ r) :
    Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r =
      Real.log (max ‖z‖ 1) + Real.log (max r 1) - Real.log (max r ‖z‖) := by
  have hA : max ‖z‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hB : max r 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hcongr : EqOn (fun w : ℂ => wholePlaneCov z w)
      (fun w : ℂ => Real.log (max ‖z‖ 1) + Real.log (max r 1) - Real.log ‖w - z‖)
      (Metric.sphere (0 : ℂ) |r|) := by
    intro w hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hw
    have hwz : ‖z - w‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      rintro rfl
      exact hz hw
    unfold wholePlaneCov
    dsimp only
    rw [hw, Real.log_div (mul_ne_zero hA hB) hwz, Real.log_mul hA hB, norm_sub_rev]
  have hint : ∀ f : ℂ → ℝ, Continuous f → True := fun _ _ => trivial
  have h1 : CircleIntegrable (fun _ : ℂ => Real.log (max ‖z‖ 1) + Real.log (max r 1)) 0 r := by
    unfold CircleIntegrable
    exact intervalIntegrable_const
  have h2 : CircleIntegrable (fun w : ℂ => Real.log ‖w - z‖) 0 r := by
    unfold CircleIntegrable
    apply Continuous.intervalIntegrable
    apply Continuous.log
    · exact ((continuous_circleMap _ _).sub continuous_const).norm
    · intro θ
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro hθ
      apply hz
      rw [← hθ, norm_circleMap_zero, abs_of_pos hr]
  rw [Real.circleAverage_congr_sphere hcongr]
  have key := Real.circleAverage_fun_sub h1 h2
  beta_reduce at key
  rw [key, Real.circleAverage_const, circleAverage_log_norm_sub_eq hr z]

/-- Circle averages of `z ↦ circleAverage (wholePlaneCov z ·) 0 r` over `∂B_s(0)` for `s ≠ r`:
the circle-circle covariance `log max(s,1) + log max(r,1) - log max(r,s)` (Duplantier-Sheffield 2011, eq. (3.2)). -/
lemma circleAverage_circleAverage_wholePlaneCov {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≠ r) :
    Real.circleAverage (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r) 0 s =
      Real.log (max s 1) + Real.log (max r 1) - Real.log (max r s) := by
  have hc : EqOn (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r)
      (fun _ : ℂ => Real.log (max s 1) + Real.log (max r 1) - Real.log (max r s))
      (Metric.sphere (0 : ℂ) |s|) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hs] at hz
    dsimp only
    rw [circleAverage_wholePlaneCov_of_ne hr (by rw [hz]; exact hsr), hz]
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

end MatedCRT.WholePlaneGFFLateral
