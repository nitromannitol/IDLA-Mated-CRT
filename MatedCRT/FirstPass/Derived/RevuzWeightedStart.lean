import MatedCRT.FirstPass.Derived.PlanarBrownianStoppedOccupationBound
import MatedCRT.FirstPass.Derived.PlanarGaussianLowerBound
import MatedCRT.FirstPass.Derived.RevuzLebesgueInvariance
import MatedCRT.FirstPass.Derived.RevuzPositive

/-!
# Symmetry of the planar heat kernel with respect to Lebesgue measure

The planar Gaussian kernel `(x, dy) ↦ planarGaussian x s (dy)` is symmetric with respect to Lebesgue measure:
for measurable `g, H ≥ 0`, `∫ g(x) ∫ H(y) p_s(x, dy) dx = ∫ H(y) ∫ g(x) p_s(y, dx) dy`. In path form, for planar
Brownian motion, `∫ g(x) E_x[H(B_s)] dx = ∫ H(y) E_y[g(B_s)] dy`. Combined with the Markov property at the fixed
time `s` and the stationarity of planar Brownian motion under Lebesgue starts, this gives the reversed Markov
identity `∫ E_x[g(B_0) F(θ_s B)] dx = ∫ E_x[(P_s g)(B_s) F(θ_s B)] dx`, the first step of the weighted-start
formula for the Revuz measure of a positive continuous additive functional.
-/

open MeasureTheory MarkovProcess HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

/-- The standard planar Gaussian law is invariant under `w ↦ -w`. -/
theorem stdPlanarGaussian_map_neg : stdPlanarGaussian.map (fun w : ℂ => -w) = stdPlanarGaussian := by
  have he := Complex.measurableEquivRealProd.symm.measurable
  have hcomm : (fun w : ℂ => -w) ∘ Complex.measurableEquivRealProd.symm =
      Complex.measurableEquivRealProd.symm ∘ Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x) := by
    funext p
    apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
  rw [stdPlanarGaussian, planarGaussian, Measure.map_map measurable_neg he, hcomm,
    ← Measure.map_map he (measurable_neg.prodMap measurable_neg),
    ← Measure.map_prod_map _ _ measurable_neg measurable_neg, ProbabilityTheory.gaussianReal_map_neg,
    ProbabilityTheory.gaussianReal_map_neg, Complex.zero_re, Complex.zero_im, neg_zero]

/-- Translation form of a Gaussian double integral: `∫ u(x) ∫ v(y) p_s(x, dy) dx = ∫∫ u(x) v(x + √s w) dx dγ(w)`,
with `γ` the standard planar Gaussian law. -/
theorem lintegral_mul_lintegral_planarGaussian_eq (s : ℝ≥0) {u v : ℂ → ℝ≥0∞} (hu : Measurable u)
    (hv : Measurable v) :
    ∫⁻ x, u x * ∫⁻ y, v y ∂planarGaussian x s =
      ∫⁻ w, (∫⁻ x, u x * v (x + (Real.sqrt s : ℂ) * w)) ∂stdPlanarGaussian := by
  have h1 : ∀ x, ∫⁻ y, v y ∂planarGaussian x s =
      ∫⁻ w, v (x + (Real.sqrt s : ℂ) * w) ∂stdPlanarGaussian := fun x => by
    rw [planarGaussian_eq_map_add_sqrt_mul, lintegral_map hv (by fun_prop)]
  have hm : Measurable (Function.uncurry fun (x w : ℂ) => u x * v (x + (Real.sqrt s : ℂ) * w)) :=
    (hu.comp measurable_fst).mul (hv.comp (measurable_fst.add (measurable_const.mul measurable_snd)))
  calc ∫⁻ x, u x * ∫⁻ y, v y ∂planarGaussian x s
      = ∫⁻ x, (∫⁻ w, u x * v (x + (Real.sqrt s : ℂ) * w) ∂stdPlanarGaussian) := by
        refine lintegral_congr fun x => ?_
        rw [h1]
        exact (lintegral_const_mul (u x) (f := fun w => v (x + (Real.sqrt s : ℂ) * w))
          (hv.comp (measurable_const.add (measurable_const.mul measurable_id)))).symm
    _ = _ := lintegral_lintegral_swap hm.aemeasurable

/-- **Symmetry of the planar heat kernel** with respect to Lebesgue measure: for measurable `g, H ≥ 0`,
`∫ g(x) ∫ H(y) p_s(x, dy) dx = ∫ H(y) ∫ g(x) p_s(y, dx) dy`. -/
theorem lintegral_mul_lintegral_planarGaussian_comm (s : ℝ≥0) {g H : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hH : Measurable H) :
    ∫⁻ x, g x * ∫⁻ y, H y ∂planarGaussian x s = ∫⁻ y, H y * ∫⁻ x, g x ∂planarGaussian y s := by
  set c : ℂ := (Real.sqrt s : ℂ)
  have hF : Measurable fun w : ℂ => ∫⁻ y, H y * g (y + c * w) :=
    ((hH.comp measurable_snd).mul (hg.comp (measurable_snd.add
      (measurable_const.mul measurable_fst)))).lintegral_prod_right'
  have htr : ∀ w : ℂ, ∫⁻ x, g x * H (x + c * w) = ∫⁻ y, H y * g (y + c * -w) := fun w => by
    have := lintegral_add_right_eq_self (μ := (volume : Measure ℂ))
      (fun y => H y * g (y + c * -w)) (c * w)
    rw [← this]
    refine lintegral_congr fun x => ?_
    rw [mul_comm, mul_neg, add_neg_cancel_right]
  rw [lintegral_mul_lintegral_planarGaussian_eq s hg hH, lintegral_mul_lintegral_planarGaussian_eq s hH hg]
  calc ∫⁻ w, (∫⁻ x, g x * H (x + c * w)) ∂stdPlanarGaussian
      = ∫⁻ w, (fun w => ∫⁻ y, H y * g (y + c * w)) (-w) ∂stdPlanarGaussian :=
        lintegral_congr fun w => htr w
    _ = ∫⁻ w, (∫⁻ y, H y * g (y + c * w)) ∂(stdPlanarGaussian.map fun w : ℂ => -w) :=
        (lintegral_map hF measurable_neg).symm
    _ = _ := by rw [stdPlanarGaussian_map_neg]

/-- **Symmetry of planar Brownian motion** with respect to Lebesgue measure at a fixed time: for measurable
`g, H ≥ 0`, `∫ g(x) E_x[H(B_s)] dx = ∫ H(y) E_y[g(B_s)] dy`. -/
theorem lintegral_mul_lintegral_planarLaw_eval_comm (s : ℝ≥0) {g H : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hH : Measurable H) :
    ∫⁻ x, g x * ∫⁻ ω, H (ω s) ∂planarLaw x = ∫⁻ y, H y * ∫⁻ ω, g (ω s) ∂planarLaw y := by
  have e : ∀ {v : ℂ → ℝ≥0∞}, Measurable v → ∀ x,
      ∫⁻ ω, v (ω s) ∂planarLaw x = ∫⁻ y, v y ∂planarGaussian x s := fun hv x => by
    rw [planarLaw, ← KilledOccupation.map_eval_planarBrownianMotion x s,
      lintegral_map hv (g := fun b : ContinuousPath ℂ => b s) (ContinuousPath.measurable_coordinateProcess _)]
  simp_rw [e hH, e hg]
  exact lintegral_mul_lintegral_planarGaussian_comm s hg hH

/-- The fixed-time marginal integral `E_x[v(B_s)] = ∫ v d p_s(x, ·)`. -/
theorem lintegral_planarLaw_eval_eq (s : ℝ≥0) {v : ℂ → ℝ≥0∞} (hv : Measurable v) (x : ℂ) :
    ∫⁻ ω, v (ω s) ∂planarLaw x = ∫⁻ y, v y ∂planarGaussian x s := by
  rw [planarLaw, ← KilledOccupation.map_eval_planarBrownianMotion x s,
    lintegral_map hv (g := fun b : ContinuousPath ℂ => b s) (ContinuousPath.measurable_coordinateProcess _)]

/-- **Simple Markov property at a fixed time**, integral form: `E_x[F ∘ θ_s] = ∫ E_y[F] p_s(x, dy)`. -/
theorem lintegral_pathShift_planarLaw_eq (x : ℂ) (s : ℝ≥0) {F : ContinuousPath ℂ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (LatticeProb.pathShift ω s) ∂planarLaw x =
      ∫⁻ y, (∫⁻ ω, F ω ∂planarLaw y) ∂planarGaussian x s := by
  have hs : ∀ ω : ContinuousPath ℂ, LatticeProb.pathShift ω s = ContinuousPath.shift s ω :=
    fun ω => congrFun (pathShift_eq_shift s) ω
  simp_rw [hs]
  rw [planarLaw, ← lintegral_map hF (ContinuousPath.continuous_shift_fixed s).measurable,
    KilledOccupation.planarBrownianMotion_map_shift x s,
    Measure.lintegral_bind planarBrownianMotion.measurable.aemeasurable hF.aemeasurable]
  rfl

/-- A functional weighted by a function of the starting point: `E_x[g(B_0) F] = g(x) E_x[F]`. -/
theorem lintegral_eval_zero_mul_planarLaw (x : ℂ) (g : ℂ → ℝ≥0∞) {F : ContinuousPath ℂ → ℝ≥0∞}
    (hF : Measurable F) : ∫⁻ ω, g (ω 0) * F ω ∂planarLaw x = g x * ∫⁻ ω, F ω ∂planarLaw x := by
  rw [← lintegral_const_mul _ hF]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_planarLaw_eval_zero x] with ω h
  rw [h]

/-- **Reversed Markov identity** for planar Brownian motion under Lebesgue starts: for measurable `g ≥ 0` and a
measurable functional `F ≥ 0`, `∫ E_x[g(B_0) F(θ_s B)] dx = ∫ E_x[(P_s g)(B_s) F(θ_s B)] dx`, where
`P_s g(y) = E_y[g(B_s)]`. -/
theorem lintegral_eval_zero_mul_pathShift_eq (s : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    {F : ContinuousPath ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, ∫⁻ ω, g (ω 0) * F (LatticeProb.pathShift ω s) ∂planarLaw x =
      ∫⁻ x, ∫⁻ ω, (∫⁻ ω', g (ω' s) ∂planarLaw (ω s)) * F (LatticeProb.pathShift ω s) ∂planarLaw x := by
  set EF : ℂ → ℝ≥0∞ := fun y => ∫⁻ ω, F ω ∂planarLaw y with hEF
  set Pg : ℂ → ℝ≥0∞ := fun y => ∫⁻ ω', g (ω' s) ∂planarLaw y with hPg
  have hEFm : Measurable EF := hF.lintegral_kernel (κ := planarBrownianMotion)
  have hgs : Measurable fun ω : ContinuousPath ℂ => g (ω s) :=
    hg.comp (ContinuousPath.measurable_coordinateProcess s)
  have hPgm : Measurable Pg := hgs.lintegral_kernel (κ := planarBrownianMotion)
  have hFs : Measurable fun ω : ContinuousPath ℂ => F (LatticeProb.pathShift ω s) :=
    hF.comp (measurable_pathShift_const s)
  have hΦ : Measurable fun ω : ContinuousPath ℂ => Pg (ω 0) * F ω :=
    (hPgm.comp (ContinuousPath.measurable_coordinateProcess 0)).mul hF
  have hL : ∫⁻ x, ∫⁻ ω, g (ω 0) * F (LatticeProb.pathShift ω s) ∂planarLaw x =
      ∫⁻ y, EF y * Pg y := by
    have h1 : ∀ x, ∫⁻ ω, g (ω 0) * F (LatticeProb.pathShift ω s) ∂planarLaw x =
        g x * ∫⁻ y, EF y ∂planarGaussian x s := fun x => by
      rw [lintegral_eval_zero_mul_planarLaw x g hFs, lintegral_pathShift_planarLaw_eq x s hF]
    simp_rw [h1]
    rw [lintegral_mul_lintegral_planarGaussian_comm s hg hEFm]
    refine lintegral_congr fun y => ?_
    exact congrArg (EF y * ·) (lintegral_planarLaw_eval_eq s hg y).symm
  have hR : ∫⁻ x, ∫⁻ ω, Pg (ω s) * F (LatticeProb.pathShift ω s) ∂planarLaw x =
      ∫⁻ y, EF y * Pg y := by
    have h2 := lintegral_pathShift_planarLaw s hΦ
    simp only [LatticeProb.pathShift_apply, add_zero] at h2
    rw [h2]
    refine lintegral_congr fun y => ?_
    rw [lintegral_eval_zero_mul_planarLaw y Pg hF, mul_comm]
  rw [hL, hR]

end MatedCRT
