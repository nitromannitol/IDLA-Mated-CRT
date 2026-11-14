import HarmonicBalls.Proofs.Sec11.FixedSquareFrontierNull
import HarmonicBalls.FirstPass.Phase2.GFFExistsConstructed

/-!
# Tilted exponential moment of a circle average inside a larger centred circle

Let `h^ℂ` be the whole-plane Gaussian free field normalized by `h^ℂ_1(0) = 0`, with circle averages
`h^ℂ_r(z)`. For a circle `∂B_ε(y)` contained in the closed disc `closedBall 0 s` with `s ≤ 1`
(`‖y‖ + ε ≤ s`), the covariance kernel `log (max |u| 1 · max |v| 1 / |u - v|)` gives
`Cov(h^ℂ_ε(y), h^ℂ_s(0)) = -log s`, `Var h^ℂ_ε(y) = -log ε` and `Var h^ℂ_s(0) = -log s`, so

* `Var(h^ℂ_ε(y) - h^ℂ_s(0)) = log s - log ε` (`variance_circle_sub_centredCircle`);
* `E exp(γ (h^ℂ_ε(y) - h^ℂ_s(0))) = (s / ε)^{γ²/2}` (`lintegral_exp_circle_sub_centredCircle`);
* `E[ε^{γ²/2} exp(γ h^ℂ_ε(y)) exp(-γ h^ℂ_s(0))] = s^{γ²/2}` (`lintegral_density_mul_exp_neg_centredCircle`).

The last identity is the first moment of the circle-average approximation of the γ-LQG measure tilted by the
circle average at the scale `s` of a dyadic annulus about the origin: it is the Gaussian input of the bound on the
LQG mass of annuli about a `γ`-log singularity (Duplantier-Sheffield 2011, Section 3.1, for the circle-average
covariance).
-/

open MeasureTheory ProbabilityTheory Metric Set Filter HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- A circle average of a function equal to `log (max |·| 1)` vanishes over a circle inside the closed unit disc. -/
lemma circleAverage_logMax_eq_zero {f : ℂ → ℝ} (hf : ∀ x, f x = Real.log (max ‖x‖ 1)) {y : ℂ} {ε : ℝ}
    (hε : 0 < ε) (h1 : ‖y‖ + ε ≤ 1) : Real.circleAverage f y ε = 0 := by
  rw [Real.circleAverage_congr_sphere (f₂ := fun _ => (0 : ℝ)), Real.circleAverage_const]
  intro x hx
  rw [mem_sphere, dist_eq_norm, abs_of_pos hε] at hx
  have hxy := norm_sub_norm_le x y
  have hx1 : ‖x‖ ≤ 1 := by linarith
  simp only [hf, max_eq_right hx1, Real.log_one]

/-- The covariance of a circle average with a larger centred circle average: for `‖y‖ + ε ≤ s ≤ 1`,
`wholePlaneGFFCov (∂B_ε(y)) (∂B_s(0)) = -log s`. -/
lemma wholePlaneGFFCov_circle_centredCircle {ε s : ℝ} (hε : 0 < ε) (hs1 : s ≤ 1) {y : ℂ}
    (hys : ‖y‖ + ε ≤ s) :
    wholePlaneGFFCov (GFFObservable.circle ε y) (GFFObservable.circle s 0) = -Real.log s := by
  have hs : 0 < s := by linarith [norm_nonneg y]
  rw [wholePlaneGFFCov_circle_circle_eq hs,
    circleAverage_logMax_eq_zero (f := logMaxAbs) (fun x => rfl) hε (hys.trans hs1),
    circleAverage_logMax_eq_zero (f := logMaxAbs) (fun x => rfl) hs (by simpa using hs1)]
  have hA : Real.circleAverage (fun x : ℂ => Real.log (max s ‖x - 0‖)) y ε = Real.log s := by
    rw [Real.circleAverage_congr_sphere (f₂ := fun _ => Real.log s), Real.circleAverage_const]
    intro x hx
    rw [mem_sphere, dist_eq_norm, abs_of_pos hε] at hx
    have hxy := norm_sub_norm_le x y
    have hxs : ‖x - 0‖ ≤ s := by rw [sub_zero]; linarith
    simp only [max_eq_left hxs]
  rw [hA]
  ring

/-- **Variance of a non-concentric circle-average increment**: for `‖y‖ + ε ≤ s ≤ 1`,
`Var(h^ℂ_ε(y) - h^ℂ_s(0)) = log s - log ε`. -/
theorem variance_circle_sub_centredCircle {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P' hC' hc)
    {ε s : ℝ} (hε : 0 < ε) (hs1 : s ≤ 1) {y : ℂ} (hys : ‖y‖ + ε ≤ s) :
    Var[fun ω => hc ω ε y - hc ω s 0; P'] = Real.log s - Real.log ε := by
  have : IsProbabilityMeasure P' := hG.isProbabilityMeasure
  have hs : 0 < s := by linarith [norm_nonneg y]
  have hrlp : MemLp (fun ω => hc ω ε y) 2 P' := (hG.hasGaussianLaw_circle hε y).memLp (by simp)
  have hslp : MemLp (fun ω => hc ω s 0) 2 P' := (hG.hasGaussianLaw_circle hs 0).memLp (by simp)
  have hrr := hG.covariance_eq (.circle ε y) (.circle ε y) hε hε
  have hss := hG.covariance_eq (.circle s 0) (.circle s 0) hs hs
  have hrs := hG.covariance_eq (.circle ε y) (.circle s 0) hε hs
  simp only [GFFObservable.eval] at hrr hss hrs
  change variance ((fun ω => hc ω ε y) - (fun ω => hc ω s 0)) P' = _
  rw [variance_sub hrlp hslp, ← covariance_self hrlp.aemeasurable,
    ← covariance_self hslp.aemeasurable, hrr, hss, hrs,
    wholePlaneGFFCov_concentric_circles_general hε hε,
    wholePlaneGFFCov_concentric_circles_general hs hs,
    wholePlaneGFFCov_circle_centredCircle hε hs1 hys,
    circleAverage_logMax_eq_zero (f := wholePlaneNormalization) (fun x => rfl) hε (hys.trans hs1),
    circleAverage_logMax_eq_zero (f := wholePlaneNormalization) (fun x => rfl) hs (by simpa using hs1),
    max_self, max_self]
  ring

/-- Two circle averages of positive radii have a jointly Gaussian difference. -/
theorem hasGaussianLaw_circle_sub_circle {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P' hC' hc)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    HasGaussianLaw (fun ω => hc ω r z - hc ω s w) P' := by
  let o : Bool → GFFObservable.Admissible := fun b =>
    if b then ⟨.circle r z, hr⟩ else ⟨.circle s w, hs⟩
  simpa [o, GFFObservable.eval] using
    ((hG.isGaussianProcess.comp_right o).hasGaussianLaw_fun_sub (s := true) (t := false))

/-- Exponential moment of a centred real Gaussian random variable: `E exp(γ X) = exp(γ² Var X / 2)`. -/
theorem lintegral_exp_of_hasGaussianLaw {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {X : Ω' → ℝ} (hX : HasGaussianLaw X P') (hm : ∫ ω, X ω ∂P' = 0) (γ : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * X ω)) ∂P' =
      ENNReal.ofReal (Real.exp (γ ^ 2 / 2 * Var[X; P'])) := by
  have hv : 0 ≤ Var[X; P'] := variance_nonneg _ _
  have hf : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (γ * x)) :=
    (Real.measurable_exp.comp (measurable_id.const_mul γ)).ennreal_ofReal
  have hmap : ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * X ω)) ∂P' =
      ∫⁻ x, ENNReal.ofReal (Real.exp (γ * x)) ∂(P'.map X) :=
    (lintegral_map' hf.aemeasurable hX.aemeasurable).symm
  rw [hmap, hX.map_eq_gaussianReal, hm]
  have hint : Integrable (fun x : ℝ => Real.exp (γ * x)) (gaussianReal 0 (Var[X; P']).toNNReal) :=
    integrable_exp_mul_gaussianReal γ
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => (Real.exp_pos _).le)]
  congr 1
  have hmgf := congrFun (mgf_id_gaussianReal (μ := 0) (v := (Var[X; P']).toNNReal)) γ
  have hmgf' : ∫ x, Real.exp (γ * x) ∂(gaussianReal 0 (Var[X; P']).toNNReal) =
      Real.exp (0 * γ + ((Var[X; P']).toNNReal : ℝ) * γ ^ 2 / 2) := hmgf
  rw [hmgf', Real.coe_toNNReal _ hv]
  congr 1
  ring

/-- **Exponential moment of a non-concentric increment**: for `‖y‖ + ε ≤ s ≤ 1`,
`E exp(γ (h^ℂ_ε(y) - h^ℂ_s(0))) = exp(γ²/2 · (log s - log ε)) = (s / ε)^{γ²/2}`. -/
theorem lintegral_exp_circle_sub_centredCircle {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P' hC' hc) (γ : ℝ)
    {ε s : ℝ} (hε : 0 < ε) (hs1 : s ≤ 1) {y : ℂ} (hys : ‖y‖ + ε ≤ s) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * (hc ω ε y - hc ω s 0))) ∂P' =
      ENNReal.ofReal (Real.exp (γ ^ 2 / 2 * (Real.log s - Real.log ε))) := by
  have : IsProbabilityMeasure P' := hG.isProbabilityMeasure
  have hs : 0 < s := by linarith [norm_nonneg y]
  have hrlp : MemLp (fun ω => hc ω ε y) 2 P' := (hG.hasGaussianLaw_circle hε y).memLp (by simp)
  have hslp : MemLp (fun ω => hc ω s 0) 2 P' := (hG.hasGaussianLaw_circle hs 0).memLp (by simp)
  have h1 : ∫ ω, hc ω ε y ∂P' = 0 := hG.integral_eq_zero (.circle ε y) hε
  have h2 : ∫ ω, hc ω s 0 ∂P' = 0 := hG.integral_eq_zero (.circle s 0) hs
  have hm : ∫ ω, (hc ω ε y - hc ω s 0) ∂P' = 0 := by
    rw [integral_sub (hrlp.integrable one_le_two) (hslp.integrable one_le_two), h1, h2, sub_zero]
  rw [lintegral_exp_of_hasGaussianLaw (hasGaussianLaw_circle_sub_circle hG hε hs y 0) hm γ,
    variance_circle_sub_centredCircle hG hε hs1 hys]

/-- **Tilted first moment of the circle-average density**: for `‖y‖ + ε ≤ s ≤ 1`,
`E[ε^{γ²/2} exp(γ h^ℂ_ε(y)) exp(-γ h^ℂ_s(0))] = s^{γ²/2}`. -/
theorem lintegral_density_mul_exp_neg_centredCircle {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P' hC' hc) (γ : ℝ)
    {ε s : ℝ} (hε : 0 < ε) (hs1 : s ≤ 1) {y : ℂ} (hys : ‖y‖ + ε ≤ s) :
    ∫⁻ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hc ω ε y)) *
        ENNReal.ofReal (Real.exp (-γ * hc ω s 0)) ∂P' =
      ENNReal.ofReal (s ^ (γ ^ 2 / 2)) := by
  have hs : 0 < s := by linarith [norm_nonneg y]
  have hpt : ∀ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hc ω ε y)) *
      ENNReal.ofReal (Real.exp (-γ * hc ω s 0)) =
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2)) * ENNReal.ofReal (Real.exp (γ * (hc ω ε y - hc ω s 0))) := by
    intro ω
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _), mul_assoc, ← Real.exp_add]
    congr 3
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_exp_circle_sub_centredCircle hG γ hε hs1 hys,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
  congr 1
  rw [Real.rpow_def_of_pos hε, Real.rpow_def_of_pos hs, ← Real.exp_add]
  congr 1
  ring

end MatedCRT.KilledOccupation
