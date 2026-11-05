import MatedCRT.Proofs.Field.Translation

/-!
# Covariances of the radial part of the whole-plane GFF (eq:gff)

For the whole-plane GFF `h^ℂ` (`HarmonicBalls.IsWholePlaneGFF`, kernel `G(x, y) = log (max(|x|,1) max(|y|,1) / |x-y|)`)
the circle average of `G(x, ·)` over `∂B_r(0)` depends on `|x|` only (`circleAverage_wholePlaneCov`):
`(1 / 2π) ∫ G(x, r e^{iθ}) dθ = K(r, |x|)`, `K(r, ρ) = log max(ρ, 1) + log max(r, 1) - log max(r, ρ)` (`radialCov`), by
Jensen's formula for `log |· - x|` (`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`). Hence:
* `Cov(h_r(0), (h, o)) = o.smear (x ↦ K(r, |x|))` for every admissible observable `o` (`covariance_circle_zero`);
* `Cov(h_r(0), h_ρ(0)) = K(r, ρ)` (`covariance_radial`), and `K(e^{-t}, e^{-t'}) = min(t, t')` for `t, t' ≥ 0`
  (`radialCov_exp_neg`): the radial process `t ↦ h_{e^{-t}}(0)`, `t ≥ 0`, has the covariance of a standard Brownian motion.
-/

namespace MatedCRT.Field.ConeRadial

open MeasureTheory ProbabilityTheory Set Filter Topology
open HarmonicBalls (IsTestFunction IsWholePlaneGFF GFFObservable wholePlaneGFFCov wholePlaneCov)

/-- `K(r, ρ) = log max(ρ, 1) + log max(r, 1) - log max(r, ρ)`: the covariance of `h_r(0)` with the field at a point of
modulus `ρ`. -/
noncomputable def radialCov (r ρ : ℝ) : ℝ := Real.log (max ρ 1) + Real.log (max r 1) - Real.log (max r ρ)

lemma log_add_posLog {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 ≤ a) :
    Real.log r + (r⁻¹ * a).posLog = Real.log (max r a) := by
  rw [Real.posLog_def, Pi.sup_apply, Pi.zero_apply]
  rcases le_or_gt a r with h | h
  · rw [max_eq_left h]
    have : Real.log (r⁻¹ * a) ≤ 0 :=
      Real.log_nonpos (by positivity) (by rw [inv_mul_le_iff₀ hr]; linarith)
    rw [sup_of_le_left this, add_zero]
  · have ha0 : 0 < a := hr.trans h
    rw [max_eq_right h.le, Real.log_mul (inv_ne_zero hr.ne') ha0.ne', Real.log_inv]
    have : 0 ≤ -Real.log r + Real.log a := by linarith [Real.log_lt_log hr h]
    rw [sup_of_le_right this]
    ring

/-- The angles at which the circle `∂B_r(0)` passes through a given point form a countable set. -/
lemma countable_circleMap_eq {r : ℝ} (hr : r ≠ 0) (x : ℂ) : {θ : ℝ | circleMap 0 r θ = x}.Countable := by
  rcases Set.eq_empty_or_nonempty {θ : ℝ | circleMap 0 r θ = x} with he | ⟨θ₀, hθ₀⟩
  · rw [he]
    exact Set.countable_empty
  refine (Set.countable_range fun n : ℤ => θ₀ + n * (2 * Real.pi)).mono fun θ hθ => ?_
  have h : circleMap 0 r θ = circleMap 0 r θ₀ := (hθ : circleMap 0 r θ = x).trans (hθ₀ : circleMap 0 r θ₀ = x).symm
  simp only [circleMap, zero_add] at h
  have h' : Complex.exp (θ * Complex.I) = Complex.exp (θ₀ * Complex.I) :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr) h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h'
  refine ⟨n, ?_⟩
  have him := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat] at him
  simp only at him ⊢
  linarith

/-- **The circle average of the whole-plane kernel.** `(1 / 2π) ∫ G(x, r e^{iθ}) dθ = K(r, |x|)`. -/
lemma circleAverage_wholePlaneCov {r : ℝ} (hr : 0 < r) (x : ℂ) :
    Real.circleAverage (fun y => wholePlaneCov x y) 0 r = radialCov r ‖x‖ := by
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc 0 (2 * Real.pi) →
      wholePlaneCov x (circleMap 0 r θ) =
        ((fun _ => logMaxOne x + Real.log (max r 1)) - (fun y => Real.log ‖y - x‖) : ℂ → ℝ)
          (circleMap 0 r θ) := by
    have h0 := (countable_circleMap_eq hr.ne' x).measure_zero (volume : Measure ℝ)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with θ hθ _
    have hne : x ≠ circleMap 0 r θ := fun h => hθ h.symm
    rw [wholePlaneCov_eq hne, norm_sub_rev x]
    simp only [Pi.sub_apply, logMaxOne, norm_circleMap_zero, abs_of_pos hr]
  rw [Real.circleAverage_def, intervalIntegral.integral_congr_ae hae, ← Real.circleAverage_def,
    Real.circleAverage_sub (circleIntegrable_const _ _ _) (circleIntegrable_log_norm_sub_const r),
    Real.circleAverage_const, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne', zero_sub,
    norm_neg, log_add_posLog hr (norm_nonneg x), radialCov, logMaxOne]

/-- The circle average of `x ↦ K(r, |x|)` over `∂B_ρ(0)` is `K(r, ρ)`. -/
lemma circleAverage_radialCov (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage (fun x => radialCov r ‖x‖) 0 ρ = radialCov r ρ := by
  rw [Real.circleAverage_congr_sphere (f₂ := fun _ => radialCov r ρ) fun x hx => ?_, Real.circleAverage_const]
  rw [mem_sphere_zero_iff_norm, abs_of_pos hρ] at hx
  simp only [hx]

/-- `K(e^{-t}, e^{-t'}) = min(t, t')` for `t, t' ≥ 0`. -/
lemma radialCov_exp_neg {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    radialCov (Real.exp (-t)) (Real.exp (-t')) = min t t' := by
  have h1 : ∀ a : ℝ, 0 ≤ a → max (Real.exp (-a)) 1 = 1 := fun a ha =>
    max_eq_right (Real.exp_le_one_iff.2 (by linarith))
  rw [radialCov, h1 t' ht', h1 t ht, Real.log_one, zero_add, zero_sub]
  rcases le_total t t' with h | h
  · rw [max_eq_left (Real.exp_le_exp.2 (by linarith)), Real.log_exp, min_eq_left h, neg_neg]
  · rw [max_eq_right (Real.exp_le_exp.2 (by linarith)), Real.log_exp, min_eq_right h, neg_neg]

/-- `u ↦ K(r, e^{-u})` is continuous. -/
lemma continuous_radialCov_exp_neg {r : ℝ} (hr : 0 < r) : Continuous fun u : ℝ => radialCov r (Real.exp (-u)) := by
  have hpos1 : ∀ a : ℝ, max a 1 ≠ 0 := fun a => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have he : Continuous fun u : ℝ => Real.exp (-u) := Real.continuous_exp.comp continuous_neg
  refine ((Real.continuousOn_log.comp_continuous (he.max continuous_const) fun u => hpos1 _).add
    continuous_const).sub (Real.continuousOn_log.comp_continuous (continuous_const.max he) fun u => ?_)
  exact (lt_of_lt_of_le hr (le_max_left _ _)).ne'

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **`Cov(h_r(0), (h, o)) = o.smear (x ↦ K(r, |x|))`.** -/
theorem covariance_circle_zero (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (o : GFFObservable)
    (ho : o.IsAdmissible) :
    cov[fun ω => hcirc ω r 0, fun ω => o.eval (hC ω) (hcirc ω); P] = o.smear fun x => radialCov r ‖x‖ := by
  rw [covariance_comm]
  refine (h.covariance_eq o (.circle r 0) ho hr).trans ?_
  show o.smear (fun x => Real.circleAverage (fun y => wholePlaneCov x y) 0 r) = _
  congr 1
  funext x
  exact circleAverage_wholePlaneCov hr x

/-- **`Cov(h_r(0), h_ρ(0)) = K(r, ρ)`.** -/
theorem covariance_radial (h : IsWholePlaneGFF P hC hcirc) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    cov[fun ω => hcirc ω r 0, fun ω => hcirc ω ρ 0; P] = radialCov r ρ :=
  (covariance_circle_zero h hr (.circle ρ 0) hρ).trans (circleAverage_radialCov r hρ)

end MatedCRT.Field.ConeRadial
