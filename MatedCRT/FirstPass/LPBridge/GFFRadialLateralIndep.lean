import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestriction
import MatedCRT.FirstPass.LPBridge.WholePlaneGFFLateral
import MatedCRT.FirstPass.LPBridge.LateralGaussian
import MatedCRT.Proofs.Field.ConeGaussianClosure

/-!
# The radial and lateral parts of a whole-plane GFF are independent

Statement: `MatedCRT.ConeMeanZeroRestriction.GFFRadialLateralIndep` (the whole-plane analogue of the independence
in Definition 2.1 of the paper; Duplantier-Sheffield, Berestycki-Powell). The proof is in Lean only.

Strategy. Write `X_s = h_s(0)` for the radial circle averages and `G(x) = h_{|x|}(0)`. A lateral observable is
`L_o = o - Rad_o`, with `Rad_o = ∫ φ(x) G(x) dx` (pairings) or `Rad_o = avg_{∂B_r(z)} G` (circles). The radial
family and the lateral family are jointly Gaussian (each `Rad_o` lies in the `L²`-closure of the Gaussian space of
observables) and uncorrelated, hence independent (`IsGaussianProcess.indepFun_of_covariance_eq_zero`).
The covariances are computed from Newton's identity `circleAverage_wholePlaneCov`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped ENNReal NNReal
open HarmonicBalls MatedCRT.WholePlaneGFFLateral

namespace MatedCRT.ConeMeanZeroRestriction

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The covariance `Cov(h(x), h_s(0))` of the whole-plane GFF averaged over the circle `∂B_s(0)`:
`log max(|x|,1) + log max(s,1) - log max(s,|x|)` (Newton's identity for the logarithm). -/
def cW (x : ℂ) (s : ℝ) : ℝ := Real.log (max ‖x‖ 1) + Real.log (max s 1) - Real.log (max s ‖x‖)

lemma circleAverage_wholePlaneCov' {s : ℝ} (hs : 0 < s) (x : ℂ) :
    Real.circleAverage (fun w : ℂ => wholePlaneCov x w) 0 s = cW x s :=
  circleAverage_wholePlaneCov hs x

lemma wholePlaneGFFCov_circle_circle_eq {t s : ℝ} (hs : 0 < s) :
    wholePlaneGFFCov (.circle t 0) (.circle s 0) = Real.circleAverage (fun x : ℂ => cW x s) 0 t := by
  unfold wholePlaneGFFCov
  simp only [GFFObservable.smear]
  congr 1
  funext x
  exact circleAverage_wholePlaneCov' hs x

lemma wholePlaneGFFCov_pairing_circle_eq (φ : ℂ → ℝ) {s : ℝ} (hs : 0 < s) :
    wholePlaneGFFCov (.pairing φ) (.circle s 0) = ∫ x, φ x * cW x s := by
  unfold wholePlaneGFFCov
  simp only [GFFObservable.smear]
  congr 1
  funext x
  rw [circleAverage_wholePlaneCov' hs x]

lemma wholePlaneGFFCov_circle_circle_centre_eq (z : ℂ) {r s : ℝ} (hs : 0 < s) :
    wholePlaneGFFCov (.circle r z) (.circle s 0) = Real.circleAverage (fun x : ℂ => cW x s) z r := by
  unfold wholePlaneGFFCov
  simp only [GFFObservable.smear]
  congr 1
  funext x
  rw [circleAverage_wholePlaneCov' hs x]

/-- `cW` depends only on the modulus of its first argument. -/
lemma circleAverage_cW_sphere {t : ℝ} (ht : 0 < t) (x : ℂ) (s : ℝ) (hx : ‖x‖ = t) :
    Real.circleAverage (fun y : ℂ => cW y s) 0 t = cW x s := by
  have hf : Set.EqOn (fun y : ℂ => cW y s) (fun _ => cW x s) (Metric.sphere (0 : ℂ) |t|) := by
    intro y hy
    rw [Metric.mem_sphere, dist_zero_right, abs_of_pos ht] at hy
    show cW y s = cW x s
    unfold cW
    rw [hy, hx]
  rw [Real.circleAverage_congr_sphere hf, Real.circleAverage_const]

/-- Radial covariances: `Cov(h_t(0), h_s(0)) = avg_{∂B_t(0)} cW · s`. -/
lemma covariance_radial_radial (h : IsWholePlaneGFF P hC hcirc) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    covariance (fun ω => hcirc ω t 0) (fun ω => hcirc ω s 0) P =
      Real.circleAverage (fun x : ℂ => cW x s) 0 t := by
  have := h.covariance_eq (.circle t 0) (.circle s 0) ht hs
  rw [← wholePlaneGFFCov_circle_circle_eq hs]
  exact this

end

end MatedCRT.ConeMeanZeroRestriction

namespace MatedCRT.ConeMeanZeroRestriction

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

lemma covariance_symm' (X Y : Ω → ℝ) (P : Measure Ω) :
    covariance X Y P = covariance Y X P := by
  simp only [covariance, mul_comm]

/-- Expectation of a product with a centred circle average: `E[h_s(0) h_t(0)] = avg_{∂B_t(0)} cW · s`. -/
lemma integral_circle_mul_circle_centred (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    ∫ ω, hcirc ω s 0 * hcirc ω t 0 ∂P = Real.circleAverage (fun x : ℂ => cW x s) 0 t := by
  have hX : MemLp (fun ω => hcirc ω s 0) 2 P := memLp_two_circle h hs 0
  have hY : MemLp (fun ω => hcirc ω t 0) 2 P := memLp_two_circle h ht 0
  have hYc : ∫ ω, hcirc ω t 0 ∂P = 0 := h.integral_eq_zero (.circle t 0) ht
  have hcov : covariance (fun ω => hcirc ω s 0) (fun ω => hcirc ω t 0) P =
      ∫ ω, hcirc ω s 0 * hcirc ω t 0 ∂P :=
    covariance_eq_integral_of_mean_zero hYc (hY.integrable one_le_two) (hX.integrable_mul hY)
  rw [← hcov, covariance_symm', covariance_radial_radial h ht hs]

lemma radialPoint_fst_of_ne {x : ℂ} (hx : x ≠ 0) : ((radialPoint x).1 : ℝ) = ‖x‖ := by
  simp [MatedCRT.WholePlaneGFFLateral.radialPoint, hx]

lemma radialPoint_snd (x : ℂ) : (radialPoint x).2 = 0 := rfl

/-- Pointwise covariance of a radial circle average with the radial part at `x ≠ 0`. -/
lemma integral_mul_radialPoint (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {x : ℂ} (hx : x ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∫ ω, hcirc ω s 0 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x) ∂P = cW x s := by
  have hae : (fun ω => hcirc ω s 0 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) =ᵐ[P]
      (fun ω => hcirc ω s 0 * hcirc ω ‖x‖ 0) := by
    filter_upwards [hFae] with ω hω
    rw [hω (MatedCRT.WholePlaneGFFLateral.radialPoint x), radialPoint_fst_of_ne hx, radialPoint_snd]
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [integral_congr_ae hae, integral_circle_mul_circle_centred h hpos hs,
    circleAverage_cW_sphere hpos x s rfl]

/-- Fubini for the radial pairing: `E[h_s(0) ∫ φ(x) h_{|x|}(0) dx] = ∫ φ(x) cW x s dx`. -/
lemma integral_circle_mul_radialIntegral (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {s : ℝ} (hs : 0 < s) :
    ∫ ω, hcirc ω s 0 * (∫ x, φ x * hcirc ω ‖x‖ 0) ∂P = ∫ x, φ x * cW x s := by
  have hZm : Measurable (fun ω => hcirc ω s 0) := h.measurable_circle s 0 hs
  have hZ : MemLp (fun ω => hcirc ω s 0) 2 P := memLp_two_circle h hs 0
  have hint := MatedCRT.WholePlaneGFFLateral.integrable_radial_mul h hF hFae hφ hZm hZ rfl
  have step1 : (fun ω => hcirc ω s 0 * ∫ x, φ x * hcirc ω ‖x‖ 0) =ᵐ[P]
      (fun ω => hcirc ω s 0 * ∫ x, φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) := by
    filter_upwards [MatedCRT.WholePlaneGFFLateral.ae_radialIntegral_eq hFae φ] with ω hω
    rw [hω]
  rw [integral_congr_ae step1]
  have hI : Integrable (Function.uncurry fun (ω : Ω) (x : ℂ) =>
      hcirc ω s 0 * (φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x))) (P.prod volume) := by
    refine hint.congr (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry]
    ring
  have hconst : ∀ ω, hcirc ω s 0 * ∫ x, φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x) =
      ∫ x, hcirc ω s 0 * (φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) := fun ω =>
    (integral_const_mul _ _).symm
  simp_rw [hconst]
  rw [integral_integral_swap hI]
  have hae0 : ({(0 : ℂ)}ᶜ : Set ℂ) ∈ ae (volume : Measure ℂ) := compl_mem_ae_iff.2 (measure_singleton 0)
  refine integral_congr_ae ?_
  filter_upwards [hae0] with x hx
  have hx0 : x ≠ 0 := Set.mem_compl_singleton_iff.1 hx
  have hmul : ∀ ω, hcirc ω s 0 * (φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) =
      φ x * (hcirc ω s 0 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) := fun ω => by ring
  simp_rw [hmul]
  rw [integral_const_mul, integral_mul_radialPoint h hFae hx0 hs]

lemma two_log_max_sub_log {u : ℝ} (hu : 0 < u) :
    2 * Real.log (max u 1) - Real.log u = |Real.log u| := by
  rcases le_total u 1 with h | h
  · rw [max_eq_right h, Real.log_one, abs_of_nonpos (Real.log_nonpos hu.le h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (Real.log_nonneg h)]
    ring

/-- The second moment of a radial circle average: `E[h_{|x|}(0)²] = |log |x||` for `x ≠ 0`. -/
lemma integral_sq_radialPoint (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {x : ℂ} (hx : x ≠ 0) :
    ∫ ω, F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x) ^ 2 ∂P = |Real.log ‖x‖| := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hae : (fun ω => F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x) ^ 2) =ᵐ[P]
      (fun ω => hcirc ω ‖x‖ 0 * hcirc ω ‖x‖ 0) := by
    filter_upwards [hFae] with ω hω
    rw [hω (MatedCRT.WholePlaneGFFLateral.radialPoint x), radialPoint_fst_of_ne hx, radialPoint_snd, sq]
  rw [integral_congr_ae hae, integral_circle_mul_circle_centred h hpos hpos,
    circleAverage_cW_sphere hpos x ‖x‖ rfl]
  unfold cW
  rw [max_self]
  linarith [two_log_max_sub_log hpos]

/-- The zero set of `θ ↦ z + r e^{iθ}` is countable, hence null for Lebesgue measure. -/
lemma circleMap_ne_zero_ae {z : ℂ} {r : ℝ} (hr : 0 < r) :
    ∀ᵐ θ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))), circleMap z r θ ≠ 0 := by
  have hcount : Set.Countable {θ : ℝ | circleMap z r θ = 0} := by
    by_cases hne : ∃ θ₁ : ℝ, circleMap z r θ₁ = 0
    · obtain ⟨θ₁, h₁⟩ := hne
      refine (Set.countable_range (fun n : ℤ => θ₁ + (n : ℝ) * (2 * π))).mono ?_
      intro θ hθ
      have hθ' : circleMap z r θ = 0 := hθ
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have he : Complex.exp (θ * Complex.I) = Complex.exp (θ₁ * Complex.I) := by
        unfold circleMap at hθ' h₁
        apply mul_left_cancel₀ hr'
        linear_combination hθ' - h₁
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
      refine ⟨n, ?_⟩
      have hc : (θ : ℂ) = (θ₁ : ℂ) + (n : ℂ) * (2 * π) := by
        apply mul_right_cancel₀ Complex.I_ne_zero
        linear_combination hn
      exact_mod_cast hc.symm
    · exact Set.Countable.mono (fun θ hθ => absurd ⟨θ, hθ⟩ hne) Set.countable_empty
  exact ae_restrict_of_ae (ae_iff.2 (by simpa only [not_not] using hcount.measure_zero volume))

/-- The logarithm of the modulus of a circle has integrable absolute value (Mathlib's circle integrability). -/
lemma integrable_abs_log_circleMap (z : ℂ) (r : ℝ) :
    Integrable (fun θ : ℝ => |Real.log ‖circleMap z r θ‖|)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))) := by
  have h1 : CircleIntegrable (fun w : ℂ => Real.log ‖w - 0‖) z r :=
    circleIntegrable_log_norm_sub_const (a := 0) (c := z) r
  have h2 : IntervalIntegrable (fun θ : ℝ => Real.log ‖circleMap z r θ‖) volume 0 (2 * π) := by
    simpa [CircleIntegrable] using h1
  have h3 : Integrable (fun θ : ℝ => Real.log ‖circleMap z r θ‖)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 h2
  exact h3.abs

lemma abs_mul_le_sq_add_sq_div_two (a b : ℝ) : ‖a * b‖ ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [Real.norm_eq_abs, abs_mul]
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs, sq_abs] at h
  linarith

/-- Integrability of `(ω, θ) ↦ Z(ω) · F(ω, radial point of e^{iθ}-circle)` against `P ⊗ dθ` on `(0, 2π]`
for an `L²` variable `Z`: the radial factor has `E[F²] = |log|z+re^{iθ}||`, which is circle integrable. -/
lemma integrable_mul_radialPoint_circle (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {Z : Ω → ℝ} (hZm : Measurable Z) (hZ : MemLp Z 2 P) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun q : Ω × ℝ =>
        Z q.1 * F q.1 (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r q.2)))
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))) := by
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hmeasF : Measurable (fun q : Ω × ℝ =>
      F q.1 (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r q.2))) :=
    (measurable_circle_version_joint hF).comp (measurable_fst.prodMk
      (MatedCRT.WholePlaneGFFLateral.measurable_radialPoint.comp
        ((continuous_circleMap z r).measurable.comp measurable_snd)))
  have hF2 : Integrable (fun q : Ω × ℝ =>
      F q.1 (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r q.2)) ^ 2)
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))) := by
    rw [integrable_prod_iff' (hmeasF.pow_const 2).aestronglyMeasurable]
    constructor
    · filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
      have hZθ : MemLp (fun ω => hcirc ω ‖circleMap z r θ‖ 0) 2 P :=
        memLp_two_circle h (norm_pos_iff.2 hθ) 0
      refine Integrable.congr hZθ.integrable_sq ?_
      filter_upwards [hFae] with ω hω
      rw [hω, radialPoint_fst_of_ne hθ, radialPoint_snd]
    · refine (integrable_abs_log_circleMap z r).congr ?_
      filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
      have := integral_sq_radialPoint h hFae hθ
      simp only [Real.norm_eq_abs, abs_pow, sq_abs]
      exact this.symm
  have hZ2 : Integrable (fun q : Ω × ℝ => Z q.1 ^ 2)
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))) := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))) := integrable_const 1
    have hprod := hZ.integrable_sq.mul_prod h1
    simpa using hprod
  refine Integrable.mono' ((hZ2.add hF2).div_const 2) ?_ (ae_of_all _ fun q => ?_)
  · exact (hZm.comp measurable_fst |>.mul hmeasF).aestronglyMeasurable
  · exact abs_mul_le_sq_add_sq_div_two _ _

/-- Fubini for the radial circle average: `E[h_s(0) · avg_{∂B_r(z)} h_{|·|}(0)] = avg_{∂B_r(z)} cW · s`. -/
lemma integral_circle_mul_circleAverage (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {z : ℂ} {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 < s) :
    ∫ ω, hcirc ω s 0 * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r ∂P =
      Real.circleAverage (fun x : ℂ => cW x s) z r := by
  have hZm : Measurable (fun ω => hcirc ω s 0) := h.measurable_circle s 0 hs
  have hZ : MemLp (fun ω => hcirc ω s 0) 2 P := memLp_two_circle h hs 0
  have hint := integrable_mul_radialPoint_circle h hF hFae hZm hZ z hr
  have hI : Integrable (Function.uncurry fun (ω : Ω) (θ : ℝ) =>
      hcirc ω s 0 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)))
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))) := by
    refine hint.congr (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry]
  have step1 : ∀ᵐ ω ∂P, (∫ θ in Set.Ioc (0 : ℝ) (2 * π), hcirc ω ‖circleMap z r θ‖ 0) =
      ∫ θ in Set.Ioc (0 : ℝ) (2 * π),
        F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)) := by
    filter_upwards [hFae] with ω hω
    apply integral_congr_ae
    filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
    rw [hω, radialPoint_fst_of_ne hθ, radialPoint_snd]
  have step3 : (∫ θ in Set.Ioc (0 : ℝ) (2 * π),
      (∫ ω, hcirc ω s 0 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)) ∂P)) =
      ∫ θ in Set.Ioc (0 : ℝ) (2 * π), cW (circleMap z r θ) s := by
    apply integral_congr_ae
    filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
    exact integral_mul_radialPoint h hFae hθ hs
  simp only [Real.circleAverage, smul_eq_mul, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  calc ∫ ω, hcirc ω s 0 * ((2 * π)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * π), hcirc ω ‖circleMap z r θ‖ 0) ∂P
      = ∫ ω, (2 * π)⁻¹ * (∫ θ in Set.Ioc (0 : ℝ) (2 * π),
          hcirc ω s 0 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ))) ∂P := by
        apply integral_congr_ae
        filter_upwards [step1] with ω hω
        rw [hω, integral_const_mul]
        ring
    _ = (2 * π)⁻¹ * ∫ ω, (∫ θ in Set.Ioc (0 : ℝ) (2 * π),
          hcirc ω s 0 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ))) ∂P := by
        rw [integral_const_mul]
    _ = (2 * π)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * π),
          (∫ ω, hcirc ω s 0 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)) ∂P) := by
        rw [integral_integral_swap hI]
    _ = (2 * π)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * π), cW (circleMap z r θ) s := by rw [step3]

end

/-! ## Covariances of the radial circle averages with the lateral observables -/

section RadialLateralCov

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Admissible observables of a whole-plane GFF are square integrable. -/
lemma memLp_two_observable (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    (o : GFFObservable) (ho : o.IsAdmissible) :
    MemLp (fun ω => o.eval (hC ω) (hcirc ω)) 2 P :=
  (h.isGaussianProcess.hasGaussianLaw_eval ⟨o, ho⟩).memLp_two

/-- The covariance of two admissible observables, as the expectation of their product. -/
lemma integral_mul_observable (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    (o o' : GFFObservable) (ho : o.IsAdmissible) (ho' : o'.IsAdmissible) :
    ∫ ω, o.eval (hC ω) (hcirc ω) * o'.eval (hC ω) (hcirc ω) ∂P = wholePlaneGFFCov o o' := by
  have hX := memLp_two_observable h o ho
  have hY := memLp_two_observable h o' ho'
  rw [← h.covariance_eq o o' ho ho']
  exact (covariance_eq_integral_of_mean_zero (h.integral_eq_zero o' ho') (hY.integrable one_le_two)
    (hX.integrable_mul hY)).symm

lemma integral_pairing_mul_circle_cW (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {s : ℝ} (hs : 0 < s) :
    ∫ ω, hC ω φ * hcirc ω s 0 ∂P = ∫ x, φ x * cW x s :=
  (integral_mul_observable h (GFFObservable.pairing φ) (GFFObservable.circle s 0) hφ hs).trans
    (wholePlaneGFFCov_pairing_circle_eq φ hs)

lemma integral_circle_mul_circle_centre (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z : ℂ) :
    ∫ ω, hcirc ω r z * hcirc ω s 0 ∂P = Real.circleAverage (fun x : ℂ => cW x s) z r :=
  (integral_mul_observable h (GFFObservable.circle r z) (GFFObservable.circle s 0) hr hs).trans
    (wholePlaneGFFCov_circle_circle_centre_eq z hs)

lemma integrable_circle_mul_radialIntegral (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun ω => hcirc ω s 0 * ∫ x, φ x * hcirc ω ‖x‖ 0) P := by
  have hZm : Measurable (fun ω => hcirc ω s 0) := h.measurable_circle s 0 hs
  have hZ : MemLp (fun ω => hcirc ω s 0) 2 P :=
    memLp_two_observable h (GFFObservable.circle s 0) hs
  have hint := MatedCRT.WholePlaneGFFLateral.integrable_radial_mul h hF hFae hφ hZm hZ rfl
  refine hint.integral_prod_left.congr ?_
  filter_upwards [MatedCRT.WholePlaneGFFLateral.ae_radialIntegral_eq hFae φ] with ω hω
  rw [integral_mul_const, ← hω]
  ring

lemma integrable_circle_mul_circleAverage (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {z : ℂ} {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 < s) :
    Integrable (fun ω => hcirc ω s 0 * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) P := by
  have hZm : Measurable (fun ω => hcirc ω s 0) := h.measurable_circle s 0 hs
  have hZ : MemLp (fun ω => hcirc ω s 0) 2 P :=
    memLp_two_observable h (GFFObservable.circle s 0) hs
  have hint := integrable_mul_radialPoint_circle h hF hFae hZm hZ z hr
  refine (hint.integral_prod_left.const_mul (2 * π)⁻¹).congr ?_
  filter_upwards [hFae] with ω hω
  have step1 : ∫ θ in Set.Ioc (0 : ℝ) (2 * π), hcirc ω ‖circleMap z r θ‖ 0 =
      ∫ θ in Set.Ioc (0 : ℝ) (2 * π),
        F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)) := by
    apply integral_congr_ae
    filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
    rw [hω, radialPoint_fst_of_ne hθ, radialPoint_snd]
  simp only [Real.circleAverage, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [integral_const_mul, ← step1]
  ring

lemma covariance_circle_pairing_lateral (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {s : ℝ} (hs : 0 < s) :
    covariance (fun ω => hcirc ω s 0) (fun ω => hC ω φ - ∫ x, φ x * hcirc ω ‖x‖ 0) P = 0 := by
  have hX : MemLp (fun ω => hcirc ω s 0) 2 P :=
    memLp_two_observable h (GFFObservable.circle s 0) hs
  have hmean : ∫ ω, hcirc ω s 0 ∂P = 0 := h.integral_eq_zero (GFFObservable.circle s 0) hs
  have hA : MemLp (fun ω => hC ω φ) 2 P := memLp_two_observable h (GFFObservable.pairing φ) hφ
  have hB := integrable_circle_mul_radialIntegral h hF hFae hφ hs
  have hAX : Integrable (fun ω => hC ω φ * hcirc ω s 0) P := hA.integrable_mul hX
  have hfun : (fun ω => (hC ω φ - ∫ x, φ x * hcirc ω ‖x‖ 0) * hcirc ω s 0) =
      fun ω => hC ω φ * hcirc ω s 0 - hcirc ω s 0 * ∫ x, φ x * hcirc ω ‖x‖ 0 := by
    funext ω
    ring
  have hint : Integrable (fun ω => (hC ω φ - ∫ x, φ x * hcirc ω ‖x‖ 0) * hcirc ω s 0) P := by
    rw [hfun]
    exact hAX.sub hB
  rw [covariance_symm', covariance_eq_integral_of_mean_zero hmean (hX.integrable one_le_two) hint,
    hfun, integral_sub hAX hB, integral_pairing_mul_circle_cW h hφ hs,
    integral_circle_mul_radialIntegral h hF hFae hφ hs, sub_self]

lemma covariance_circle_circle_lateral (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 < s) (z : ℂ) :
    covariance (fun ω => hcirc ω s 0)
      (fun ω => hcirc ω r z - Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) P = 0 := by
  have hX : MemLp (fun ω => hcirc ω s 0) 2 P :=
    memLp_two_observable h (GFFObservable.circle s 0) hs
  have hmean : ∫ ω, hcirc ω s 0 ∂P = 0 := h.integral_eq_zero (GFFObservable.circle s 0) hs
  have hC' : MemLp (fun ω => hcirc ω r z) 2 P :=
    memLp_two_observable h (GFFObservable.circle r z) hr
  have hCX : Integrable (fun ω => hcirc ω r z * hcirc ω s 0) P := hC'.integrable_mul hX
  have hAX := integrable_circle_mul_circleAverage h hF hFae hr hs (z := z)
  have hfun : (fun ω => (hcirc ω r z - Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) *
      hcirc ω s 0) = fun ω => hcirc ω r z * hcirc ω s 0 -
        hcirc ω s 0 * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r := by
    funext ω
    ring
  have hint : Integrable (fun ω => (hcirc ω r z - Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) *
      hcirc ω s 0) P := by
    rw [hfun]
    exact hCX.sub hAX
  rw [covariance_symm', covariance_eq_integral_of_mean_zero hmean (hX.integrable one_le_two) hint,
    hfun, integral_sub hCX hAX, integral_circle_mul_circle_centre h hr hs z,
    integral_circle_mul_circleAverage h hF hFae hr hs, sub_self]

/-- The covariance of a radial circle average `h_s(0)` with every admissible lateral observable vanishes:
the radial and lateral parts of a whole-plane GFF are uncorrelated (Duplantier-Sheffield, Section 3). -/
lemma covariance_circle_lateralEval (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {s : ℝ} (hs : 0 < s) (o : GFFObservable.Admissible) :
    covariance (fun ω => hcirc ω s 0) (fun ω => lateralEval (hC ω) (hcirc ω) o.1) P = 0 := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact covariance_circle_pairing_lateral h hF hFae ho hs
  | circle r z => exact covariance_circle_circle_lateral h hF hFae ho hs z

end RadialLateralCov

end MatedCRT.ConeMeanZeroRestriction
