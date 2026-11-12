import MatedCRT.FirstPass.LPBridge.GFFRadialLateralIndep
import MatedCRT.Proofs.Field.WholePlaneBrownian

/-!
# The two-sided radial process of a whole-plane GFF is a pair of independent Brownian motions

For a whole-plane Gaussian free field `h^ℂ` (normalized so that `h^ℂ_1(0) = 0`) the radial process is recorded as the
pair of paths `t ↦ h^ℂ_{e^{-t}}(0)` and `s ↦ h^ℂ_{e^s}(0)`, `t, s ≥ 0` (`radialProcess`). This file shows that its law
on `(ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)` (product σ-algebras) is the law of a pair of independent standard Brownian motions
(Duplantier-Sheffield 2011, Section 3.1; Berestycki-Powell, Ch. 3).

The covariance of the circle averages at the origin is `Cov(h_a(0), h_b(0)) = log max(a,1) + log max(b,1) -
log max(a,b)` (Newton's identity for the logarithm, `covariance_radial_radial`). Hence
* the outer path `s ↦ h_{e^s}(0)` has covariance `min(s, s')`, so it has the law of Brownian motion
  (`map_eq_of_covariance`, as for the inner path in `map_radial_eq_brownian`);
* the inner and outer circle averages are uncorrelated, and the two paths are jointly Gaussian, so they are
  independent (`IsGaussianProcess.indepFun_of_covariance_eq_zero`).

* `covariance_origin_circles`: the covariance formula for two circles centred at the origin.
* `covariance_radial_inner_outer`, `covariance_radial_outer`: the two covariances.
* `indepFun_radial_inner_outer`: independence of the inner and outer radial paths.
* `map_radial_outer_eq_brownian`: the outer radial path is a standard Brownian motion in law.
* `map_radialProcess_eq_brownian_prod`: the radial process has the law of two independent Brownian motions.
-/

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- The law of the coordinate process of standard Brownian motion on `ℝ≥0 → ℝ` (product σ-algebra). -/
noncomputable abbrev brownianPathLaw : Measure (ℝ≥0 → ℝ) :=
  (brownianMotion 0).map fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The covariance of the circle averages at the origin of radii `a, b > 0` of a whole-plane GFF:
`Cov(h_a(0), h_b(0)) = log max(a, 1) + log max(b, 1) - log max(b, a)`. -/
theorem covariance_origin_circles (hh : IsWholePlaneGFF P hC hcirc) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    covariance (fun ω => hcirc ω a 0) (fun ω => hcirc ω b 0) P =
      Real.log (max a 1) + Real.log (max b 1) - Real.log (max b a) := by
  have hn : ‖(a : ℂ)‖ = a := by simp [abs_of_pos ha]
  rw [MatedCRT.ConeMeanZeroRestriction.covariance_radial_radial hh ha hb,
    MatedCRT.ConeMeanZeroRestriction.circleAverage_cW_sphere ha (a : ℂ) b hn]
  simp only [MatedCRT.ConeMeanZeroRestriction.cW, hn]

/-- The inner and outer circle averages at the origin are uncorrelated:
`Cov(h_{e^{-t}}(0), h_{e^s}(0)) = 0`. -/
theorem covariance_radial_inner_outer (hh : IsWholePlaneGFF P hC hcirc) (t s : ℝ≥0) :
    covariance (fun ω => hcirc ω (Real.exp (-(t : ℝ))) 0) (fun ω => hcirc ω (Real.exp s) 0) P = 0 := by
  rw [covariance_origin_circles hh (Real.exp_pos _) (Real.exp_pos _)]
  have h1 : Real.exp (-(t : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [t.2])
  have h2 : 1 ≤ Real.exp (s : ℝ) := Real.one_le_exp_iff.2 s.2
  rw [max_eq_right h1, max_eq_left h2, max_eq_left (h1.trans h2), Real.log_one]
  ring

/-- The outer radial path has the covariance of Brownian motion: `Cov(h_{e^s}(0), h_{e^{s'}}(0)) = min(s, s')`. -/
theorem covariance_radial_outer (hh : IsWholePlaneGFF P hC hcirc) (s s' : ℝ≥0) :
    covariance (fun ω => hcirc ω (Real.exp s) 0) (fun ω => hcirc ω (Real.exp s') 0) P =
      min (s : ℝ) (s' : ℝ) := by
  rw [covariance_origin_circles hh (Real.exp_pos _) (Real.exp_pos _)]
  rw [max_eq_left (Real.one_le_exp_iff.2 s.coe_nonneg), max_eq_left (Real.one_le_exp_iff.2 s'.coe_nonneg), Real.log_exp,
    Real.log_exp]
  rcases le_total (s : ℝ) (s' : ℝ) with h | h
  · rw [max_eq_left (Real.exp_le_exp.2 h), Real.log_exp, min_eq_left h]
    ring
  · rw [max_eq_right (Real.exp_le_exp.2 h), Real.log_exp, min_eq_right h]
    ring

/-- The two-sided radial family `(h_{e^{-t}}(0))_t ⊔ (h_{e^s}(0))_s` of a whole-plane GFF is a Gaussian process. -/
theorem isGaussianProcess_radial_twoSided (hh : IsWholePlaneGFF P hC hcirc) :
    IsGaussianProcess (Sum.elim (fun (t : ℝ≥0) ω => hcirc ω (Real.exp (-(t : ℝ))) 0)
      (fun (s : ℝ≥0) ω => hcirc ω (Real.exp s) 0)) P := by
  have h := hh.isGaussianProcess.comp_right (Sum.elim
    (fun t : ℝ≥0 => (⟨GFFObservable.circle (Real.exp (-(t : ℝ))) 0, Real.exp_pos _⟩ :
      GFFObservable.Admissible))
    (fun s : ℝ≥0 => (⟨GFFObservable.circle (Real.exp s) 0, Real.exp_pos _⟩ : GFFObservable.Admissible)))
  convert h using 1
  funext i
  cases i <;> rfl

/-- The inner and outer radial paths of a whole-plane GFF are independent. -/
theorem indepFun_radial_inner_outer (hh : IsWholePlaneGFF P hC hcirc) :
    IndepFun (fun ω => (radialProcess (hcirc ω)).1) (fun ω => (radialProcess (hcirc ω)).2) P :=
  IsGaussianProcess.indepFun_of_covariance_eq_zero (isGaussianProcess_radial_twoSided hh)
    (fun _ => (hh.measurable_circle _ _ (Real.exp_pos _)).aemeasurable)
    (fun _ => (hh.measurable_circle _ _ (Real.exp_pos _)).aemeasurable)
    (fun t s => covariance_radial_inner_outer hh t s)

/-- The coordinate process of standard Brownian motion is centred. -/
theorem integral_brownian_coord (t : ℝ≥0) : ∫ w : ContinuousPath ℝ, w t ∂(brownianMotion 0) = 0 := by
  have hmap : ∫ x : ℝ, x ∂((brownianMotion 0).map (fun w : ContinuousPath ℝ => w t))
      = ∫ w : ContinuousPath ℝ, w t ∂(brownianMotion 0) :=
    integral_map (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t).aemeasurable
      aestronglyMeasurable_id
  rw [← hmap, brownianMotion_map_eval, integral_id_gaussianReal]

/-- **The outer radial path of a whole-plane GFF is a standard Brownian motion in law.** On `ℝ≥0 → ℝ` with the
product σ-algebra, `s ↦ h^ℂ_{e^s}(0)` has the law of the coordinate process of `brownianMotion 0`. -/
theorem map_radial_outer_eq_brownian [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) :
    P.map (fun ω (s : ℝ≥0) => hcirc ω (Real.exp s) 0) = brownianPathLaw := by
  have hG : IsGaussianProcess (fun (s : ℝ≥0) ω => hcirc ω (Real.exp s) 0) P :=
    hh.isGaussianProcess.comp_right (fun s : ℝ≥0 =>
      (⟨GFFObservable.circle (Real.exp s) 0, Real.exp_pos _⟩ : GFFObservable.Admissible))
  refine MatedCRT.Field.map_eq_of_covariance hG MatedCRT.Field.brownian_isGaussianProcess
    (fun s => hh.measurable_circle _ _ (Real.exp_pos _))
    (fun s => ContinuousPath.measurable_coordinateProcess (alpha := ℝ) s)
    (fun s => ?_) (fun s => integral_brownian_coord s) (fun s s' => ?_)
  · exact hh.integral_eq_zero (GFFObservable.circle (Real.exp s) 0) (Real.exp_pos _)
  · exact (covariance_radial_outer hh s s').trans (MatedCRT.Field.brownian_covariance s s').symm

/-- **The radial process of a whole-plane GFF is a pair of independent standard Brownian motions in law**:
`(t ↦ h^ℂ_{e^{-t}}(0), s ↦ h^ℂ_{e^s}(0))` has the law `B ⊗ B` on `(ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)`. -/
theorem map_radialProcess_eq_brownian_prod [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) :
    P.map (fun ω => radialProcess (hcirc ω)) = brownianPathLaw.prod brownianPathLaw := by
  have hX : Measurable fun ω => (radialProcess (hcirc ω)).1 :=
    Measurable.of_eval fun _ => hh.measurable_circle _ _ (Real.exp_pos _)
  have hY : Measurable fun ω => (radialProcess (hcirc ω)).2 :=
    Measurable.of_eval fun _ => hh.measurable_circle _ _ (Real.exp_pos _)
  have h := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1
    (indepFun_radial_inner_outer hh)
  have hin : P.map (fun ω => (radialProcess (hcirc ω)).1) = brownianPathLaw :=
    MatedCRT.Field.map_radial_eq_brownian hh
  have hout : P.map (fun ω => (radialProcess (hcirc ω)).2) = brownianPathLaw :=
    map_radial_outer_eq_brownian hh
  rw [hin, hout] at h
  exact h

end MatedCRT.FirstPass.Derived
