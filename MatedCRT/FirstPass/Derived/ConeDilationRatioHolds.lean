import MatedCRT.FirstPass.Derived.ConeGFFIsGFF
import MatedCRT.FirstPass.Derived.ConeDilationRatio
import LatticeProb.LQG.GMCRatioLimitSingular
import LatticeProb.LQG.GMCOriginContinuum
import LatticeProb.LQG.GMCContinuumMaximal
import LatticeProb.LQG.LQGWeylScalingAlong
import LatticeProb.LQG.LQGWeylScaling
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4

/-!
# The ratio limit of the γ-quantum cone, and the non-dyadic dilation part of Fact 2.2

For the circle average embedding `(hC, hcirc)` of a γ-quantum cone with LQG measure `μ`, almost surely the
approximations of `μ` converge vaguely along the scales `r 2^{-k}` for every ratio `r ∈ (1/2, 1]` simultaneously.
By `lqgMeasureNonDyadicDilationPart_of_ratio` this is the non-dyadic dilation part of Fact 2.2.

The proof couples the cone with an independent standard Brownian motion `w` (`isWholePlaneGFF_coneGFF`): the coupled
field `h^ℂ` is a whole-plane GFF under `P ⊗ BM`, and the cone is `h^ℂ - γ log |·| + rem` with a continuous remainder
`rem = coneCouplingRemainder` (`coneCircle_eq_addCircleAverage`). By Weyl scaling the LQG measure of
`h^ℂ - γ log |·|` is `e^{-γ rem} dμ`; the ratio limit for the field with a logarithmic singularity at the origin
(`ae_isLQGLimitAlong_ratio_fieldCircleAverage_of_origin`, with the mass bound near the origin from the continuum
growth condition) and Weyl scaling along the scales `r 2^{-k}` with `+rem` return to `μ`. The Brownian coordinate is
then dropped (an almost sure statement on a product about the first coordinate only).

## Main results
* `isLQGLimit_coneGFF`, `isLQGLimitAlong_of_coneGFF`: the two pathwise Weyl scaling steps.
* `ae_isLQGLimitAlong_ratio_cone`: the almost sure ratio limit of the cone field.
* `lqgMeasureNonDyadicDilationPart_holds`: `LQGMeasureNonDyadicDilationPart`.
-/

open MeasureTheory Filter Set Topology MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The circle average of `-f` is minus the circle average of `f`. -/
theorem circleAverage_neg_fun (f : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    Real.circleAverage (fun x => -f x) c R = -Real.circleAverage f c R := by
  have h := Real.circleAverage_fun_smul (a := (-1 : ℝ)) (f := f) (c := c) (R := R)
  simpa using h

/-- The coupled field minus `γ log |·|` is the cone field minus the circle averages of the remainder. -/
theorem fieldCircleAverage_coneGFFCircle (γ : ℝ) (F : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) :
    LatticeProb.Gauss.fieldCircleAverage γ (coneGFFCircle γ F w) =
      LatticeProb.Gauss.addCircleAverage F (fun x => -coneCouplingRemainder γ F w x) := by
  funext r z
  simp only [LatticeProb.Gauss.addCircleAverage, LatticeProb.Gauss.fieldCircleAverage, coneGFFCircle,
    circleAverage_neg_fun]
  ring

/-- Adding the circle averages of `-f` and then of `f` gives back the field. -/
theorem addCircleAverage_neg_add (hε : ℝ → ℂ → ℝ) (f : ℂ → ℝ) :
    LatticeProb.Gauss.addCircleAverage (LatticeProb.Gauss.addCircleAverage hε (fun x => -f x)) f = hε := by
  funext r z
  simp only [LatticeProb.Gauss.addCircleAverage, circleAverage_neg_fun]
  ring

/-- The densities `e^{-γ f}` and `e^{γ f}` cancel. -/
theorem withDensity_exp_neg_exp (m : Measure ℂ) (γ : ℝ) {f : ℂ → ℝ} (hf : Measurable f) :
    (m.withDensity fun z => ENNReal.ofReal (Real.exp (γ * -f z))).withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * f z))) = m := by
  have h1 : Measurable fun z => ENNReal.ofReal (Real.exp (γ * -f z)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hf.neg))
  have h2 : Measurable fun z => ENNReal.ofReal (Real.exp (γ * f z)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hf))
  rw [← withDensity_mul m h1 h2]
  have hone : ((fun z => ENNReal.ofReal (Real.exp (γ * -f z))) *
      fun z => ENNReal.ofReal (Real.exp (γ * f z))) = 1 := by
    funext z
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  rw [hone, withDensity_one]

/-- A field whose circle averages are continuous on `(0, ∞) × ℂ` is continuous in the centre at each positive
radius. -/
theorem continuous_of_continuousOn_circle {F : ℝ → ℂ → ℝ}
    (hF : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (Ioi 0 ×ˢ univ)) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (F ρ) :=
  hF.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hρ, mem_univ _⟩

/-- **Weyl scaling, first step (pathwise).** If `μ` is the LQG limit of a field `F` with continuous circle averages
and `w` is continuous, then `e^{-γ rem} dμ` is the LQG limit of the coupled field minus `γ log |·|`. -/
theorem isLQGLimit_coneGFF {γ : ℝ} {F : ℝ → ℂ → ℝ} {w : ℝ≥0 → ℝ} {m : Measure ℂ}
    (hF : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (Ioi 0 ×ˢ univ)) (hw : Continuous w)
    (h : LatticeProb.LQG.IsLQGLimit γ F m) :
    LatticeProb.LQG.IsLQGLimit γ (LatticeProb.Gauss.fieldCircleAverage γ (coneGFFCircle γ F w))
      (m.withDensity fun z => ENNReal.ofReal (Real.exp (γ * -coneCouplingRemainder γ F w z))) := by
  have hc : ContinuousOn (fun ρ => F ρ 0) (Ioi 0) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn fun ρ hρ => ⟨hρ, mem_univ _⟩
  have hrem := continuous_coneCouplingRemainder γ hc hw
  rw [fieldCircleAverage_coneGFFCircle]
  exact LatticeProb.LQG.LQGWeylScalingDerived.isLQGLimit_addCircleAverage h
    (fun n => continuous_of_continuousOn_circle hF (by unfold LatticeProb.LQG.dyadicScale; positivity)) _ hrem.neg

/-- **Weyl scaling, second step (pathwise).** If the coupled field minus `γ log |·|` has the LQG limit `e^{-γ rem} dμ`
along positive scales `s k → 0`, then `F` has the limit `μ` along the same scales. -/
theorem isLQGLimitAlong_of_coneGFF {γ : ℝ} {F : ℝ → ℂ → ℝ} {w : ℝ≥0 → ℝ} {m : Measure ℂ} {s : ℕ → ℝ}
    (hF : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (Ioi 0 ×ˢ univ)) (hw : Continuous w)
    (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0))
    (h : LatticeProb.LQG.IsLQGLimitAlong γ (LatticeProb.Gauss.fieldCircleAverage γ (coneGFFCircle γ F w)) s
      (m.withDensity fun z => ENNReal.ofReal (Real.exp (γ * -coneCouplingRemainder γ F w z)))) :
    LatticeProb.LQG.IsLQGLimitAlong γ F s m := by
  have hc : ContinuousOn (fun ρ => F ρ 0) (Ioi 0) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn fun ρ hρ => ⟨hρ, mem_univ _⟩
  have hrem := continuous_coneCouplingRemainder γ hc hw
  rw [fieldCircleAverage_coneGFFCircle] at h
  have hcont : ∀ n, Continuous (LatticeProb.Gauss.addCircleAverage F
      (fun x => -coneCouplingRemainder γ F w x) (s n)) := fun n => by
    have hav := (LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center hrem.neg).comp
      ((continuous_const : Continuous fun _ : ℂ => s n).prodMk continuous_id)
    exact (continuous_of_continuousOn_circle hF (hs n)).add hav
  have h1 := LatticeProb.LQG.LQGWeylScalingAlong.isLQGLimitAlong_addCircleAverage h (fun n => (hs n).le) hs0
    hcont _ hrem
  rwa [addCircleAverage_neg_add, withDensity_exp_neg_exp _ _ hrem.measurable] at h1

/-- `γ < Q = 2/γ + γ/2` for `0 < γ < 2`. -/
theorem lt_lqgQ_self {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : γ < LatticeProb.LQG.lqgQ γ := by
  have h : 1 < 2 / γ := by rw [lt_div_iff₀ hγ0]; linarith
  unfold LatticeProb.LQG.lqgQ
  linarith

/-- **The ratio limit of the γ-quantum cone.** For the circle average embedding `(hC, hcirc)` of a γ-quantum cone with
LQG measure `μ`, `0 < γ < 2`, almost surely the approximations converge vaguely to `μ` along the scales `r 2^{-k}`,
for every ratio `r ∈ (1/2, 1]` simultaneously. -/
theorem ae_isLQGLimitAlong_ratio_cone {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) :
    ∀ᵐ ω ∂P, ∀ r ∈ Ioc (1 / 2 : ℝ) 1,
      LatticeProb.LQG.IsLQGLimitAlong γ (hcirc ω) (fun k => r * LatticeProb.LQG.dyadicScale k) (μ ω) := by
  obtain ⟨hP, hQ, hμ⟩ := hcone
  obtain ⟨N, -, hN0, hG⟩ := isWholePlaneGFF_coneGFF hQ
  have hG' := (HarmonicBalls.LPBridge.isWholePlaneGFF_iff _ _ _).1 hG
  have hμ' : ∀ᵐ ω ∂P, LatticeProb.LQG.IsLQGLimit γ (hcirc ω) (μ ω) :=
    (HarmonicBalls.LPBridge.isLQGMeasure_iff P γ hcirc μ).1 hμ
  have hgood : ∀ᵐ ω ∂P, ω ∉ N ∧ LatticeProb.LQG.IsLQGLimit γ (hcirc ω) (μ ω) ∧
      ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi 0 ×ˢ univ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0, hμ', hQ.ae_continuousOn_circle] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hgood' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := brownianMotion (0 : ℝ))).ae hgood
  have hμG : LatticeProb.LQG.IsLQGMeasureOfField (P.prod (brownianMotion 0)) γ γ
      (fun p => coneGFFCircle γ (circleOff N hcirc p.1) (fun t => p.2 t))
      (fun p => (μ p.1).withDensity fun z => ENNReal.ofReal
        (Real.exp (γ * -coneCouplingRemainder γ (circleOff N hcirc p.1) (fun t => p.2 t) z))) := by
    filter_upwards [hgood'] with p hp
    obtain ⟨hpN, hpμ, hpc⟩ := hp
    have hoff := circleOff_of_notMem (hcirc := hcirc) hpN
    rw [← hoff] at hpμ hpc
    exact isLQGLimit_coneGFF hpc p.2.continuous hpμ
  have hO := LatticeProb.LQG.ae_origin_ratio_of_ae_continuumOriginGrowth hγ0 (lt_lqgQ_self hγ0 hγ2)
    (hG'.ae_continuumOriginGrowth hγ0 hγ2)
  have hC5 := hG'.ae_isLQGLimitAlong_ratio_fieldCircleAverage_of_origin hγ0 hγ2 hμG hO
  have hprod : ∀ᵐ p ∂(P.prod (brownianMotion 0)), ∀ r ∈ Ioc (1 / 2 : ℝ) 1,
      LatticeProb.LQG.IsLQGLimitAlong γ (hcirc p.1) (fun k => r * LatticeProb.LQG.dyadicScale k) (μ p.1) := by
    filter_upwards [hC5, hgood'] with p hp hpg r hr
    obtain ⟨hpN, -, hpc⟩ := hpg
    have hoff := circleOff_of_notMem (hcirc := hcirc) hpN
    rw [← hoff] at hpc
    have hr0 : 0 < r := lt_trans (by norm_num) hr.1
    have hs : ∀ n, 0 < r * LatticeProb.LQG.dyadicScale n := fun n =>
      mul_pos hr0 (by unfold LatticeProb.LQG.dyadicScale; positivity)
    have hs0 : Tendsto (fun k => r * LatticeProb.LQG.dyadicScale k) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul r
      simpa [LatticeProb.LQG.dyadicScale] using h
    have h1 := isLQGLimitAlong_of_coneGFF hpc p.2.continuous hs hs0 (hp r hr)
    rwa [hoff] at h1
  filter_upwards [Measure.ae_ae_of_ae_prod hprod] with ω hω
  exact hω.exists.elim fun _ h => h

/-- **`LQGMeasureNonDyadicDilationPart` holds** (the non-dyadic dilation part of Fact 2.2). -/
theorem lqgMeasureNonDyadicDilationPart_holds : LQGMeasureNonDyadicDilationPart :=
  lqgMeasureNonDyadicDilationPart_of_ratio fun _ hγ0 hγ2 _ _ _ _ _ _ hcone =>
    ae_isLQGLimitAlong_ratio_cone hγ0 hγ2 hcone

end MatedCRT.FirstPass.Derived
