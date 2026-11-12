import MatedCRT.FirstPass.Derived.ConeReferenceLaw
import MatedCRT.FirstPass.Derived.ConeRadialIntegrable
import MatedCRT.FirstPass.Derived.GFFRadialTwoSided
import MatedCRT.Proofs.Field.ConeLevelIntegrable
import LatticeProb.Prob.RadialCircleIntegrable
import LatticeProb.LQG.LocalMeasureKernel4

/-!
# The lateral part of the quantum cone built from a whole-plane GFF and a path

For the explicit cone data `(coneRefPairing γ hC hcirc w, coneRefCircle γ hcirc w)` built from the pairings `hC`
and circle averages `hcirc` of a whole-plane Gaussian free field `h^ℂ` and a continuous path `w`, the lateral
part `h - h_{|·|}(0)` of the cone equals the lateral part of `h^ℂ` at every admissible observable on which
`x ↦ h^ℂ_{|x|}(0)` is integrable (against the test function, respectively on the circle).

* `wholePlaneGFF_integral_abs_radial_le`: `E |h^ℂ_ρ(0)| ≤ 1 + |log ρ|`.
* `wholePlaneGFF_ae_circleIntegrable_radial`: for a fixed circle, almost surely `x ↦ h^ℂ_{|x|}(0)` is integrable
  on it (also through the origin).
* `wholePlaneGFF_ae_integrable_radial_mul`: for a fixed test function `φ`, almost surely
  `x ↦ φ(x) h^ℂ_{|x|}(0)` is integrable.
* `lateralEval_coneRef_pairing`, `lateralEval_coneRef_circle`: the deterministic identities.
* `ae_lateralProcess_coneRef_apply`: at a fixed admissible observable, almost surely for the field and for every
  continuous path `w`, the lateral observable of the cone data equals that of the field.
-/

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

section GFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- `E |h^ℂ_ρ(0)| ≤ 1 + |log ρ|` for a whole-plane GFF (its variance is `|log ρ|`). -/
theorem wholePlaneGFF_integral_abs_radial_le (hh : IsWholePlaneGFF P hC hcirc) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ ω, |hcirc ω ρ 0| ∂P ≤ 1 + |Real.log ρ| := by
  have : IsProbabilityMeasure P := hh.isGaussianProcess.isProbabilityMeasure
  have hG := hh.hasGaussianLaw_circle hρ 0
  have hm : Measurable fun ω => hcirc ω ρ 0 := hh.measurable_circle ρ 0 hρ
  have h0 : ∫ ω, hcirc ω ρ 0 ∂P = 0 := hh.integral_eq_zero (.circle ρ 0) hρ
  have hv : Var[fun ω => hcirc ω ρ 0; P] = |Real.log ρ| := by
    have := covariance_origin_circles hh hρ hρ
    rw [covariance_self hm.aemeasurable] at this
    rw [this]
    rcases le_total ρ 1 with h | h
    · rw [max_eq_right h, max_self, Real.log_one, abs_of_nonpos (Real.log_nonpos hρ.le h)]; ring
    · rw [max_eq_left h, max_self, abs_of_nonneg (Real.log_nonneg h)]; ring
  have hmap : P.map (fun ω => hcirc ω ρ 0) = gaussianReal 0 (|Real.log ρ|).toNNReal := by
    rw [hG.map_eq_gaussianReal, hv]
    congr 1
  have := MatedCRT.Field.GaussClosure.integral_abs_le_of_map_eq hm hmap
  rwa [Real.coe_toNNReal _ (abs_nonneg _)] at this

/-- For a fixed circle `∂B_r(z)`, almost surely `x ↦ h^ℂ_{|x|}(0)` is integrable on it, also when the circle
passes through the origin. -/
theorem wholePlaneGFF_ae_circleIntegrable_radial (hh : IsWholePlaneGFF P hC hcirc) (r : ℝ) (z : ℂ) :
    ∀ᵐ ω ∂P, CircleIntegrable (fun x => hcirc ω ‖x‖ 0) z r := by
  have : IsProbabilityMeasure P := hh.isGaussianProcess.isProbabilityMeasure
  refine LatticeProb.RadialCircle.ae_circleIntegrable_comp_norm (X := fun ω ρ => hcirc ω ρ 0) (C := 1)
    (fun ρ hρ => hh.measurable_circle ρ 0 hρ) ?_ zero_le_one ?_ z r
  · filter_upwards [hh.ae_continuousOn_circle] with ω hc using continuousOn_radial_of_continuousOn hc
  · intro ρ hρ hρ1
    have hint : Integrable (fun ω => hcirc ω ρ 0) P := (hh.hasGaussianLaw_circle hρ 0).memLp_two.integrable one_le_two
    have h1 := wholePlaneGFF_integral_abs_radial_le hh hρ
    rw [abs_of_nonpos (Real.log_nonpos hρ.le hρ1)] at h1
    calc ∫⁻ ω, ‖hcirc ω ρ 0‖ₑ ∂P = ENNReal.ofReal (∫ ω, ‖hcirc ω ρ 0‖ ∂P) :=
          (ofReal_integral_norm_eq_lintegral_enorm hint).symm
      _ ≤ ENNReal.ofReal (1 * (1 - Real.log ρ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          simp only [Real.norm_eq_abs]
          linarith

/-- For a fixed test function `φ`, almost surely `x ↦ φ(x) h^ℂ_{|x|}(0)` is integrable. -/
theorem wholePlaneGFF_ae_integrable_radial_mul (hh : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) :
    ∀ᵐ ω ∂P, Integrable (fun x => φ x * hcirc ω ‖x‖ 0) := by
  have : IsProbabilityMeasure P := hh.isGaussianProcess.isProbabilityMeasure
  have hφc : Continuous φ := hφ.1.continuous
  have hlog : Integrable (fun x : ℂ => φ x * (1 + |Real.log ‖x‖|)) := by
    have habs : LocallyIntegrable (fun x : ℂ => |Real.log ‖x‖|) volume :=
      LatticeProb.LocalMeasureKernel.LocalDecoderCommon.locallyIntegrable_log_norm_complex.mono
        (by fun_prop : Measurable fun x : ℂ => |Real.log ‖x‖|).aestronglyMeasurable
        (ae_of_all _ fun x => by simp)
    have hloc : LocallyIntegrable (fun x : ℂ => 1 + |Real.log ‖x‖|) volume :=
      (locallyIntegrable_const (1 : ℝ)).add habs
    have := hloc.integrable_smul_left_of_hasCompactSupport hφc hφ.2.1
    simpa [smul_eq_mul] using this
  have key := MatedCRT.Field.GaussClosure.ae_integrable_level (P := P)
    (V := fun u ω => hcirc ω (Real.exp u) 0) (fun u => hh.measurable_circle _ 0 (Real.exp_pos u))
    (by
      filter_upwards [hh.ae_continuousOn_circle] with ω hc
      exact (continuousOn_radial_of_continuousOn hc).comp_continuous Real.continuous_exp
        fun u => Real.exp_pos u)
    (fun u => (hh.hasGaussianLaw_circle (Real.exp_pos u) 0).memLp_two.integrable one_le_two)
    (fun u => by simpa [Real.log_exp] using wholePlaneGFF_integral_abs_radial_le hh (Real.exp_pos u))
    (ν := (volume : Measure ℂ)) (g := φ) (s := fun x => Real.log ‖x‖) hφc.measurable
    (measurable_norm.log) hlog
  filter_upwards [key] with ω hω
  refine hω.congr ?_
  have h0 : ∀ᵐ x : ℂ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [h0] with x hx
  simp [Real.exp_log (norm_pos_iff.2 hx)]

end GFF

section Identities

/-- Lateral pairing of the cone data equals that of the field, given the integrability of the three radial
pieces against `φ`. -/
theorem lateralEval_coneRef_pairing (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) {hcirc : ℝ → ℂ → ℝ}
    {w : ContinuousPath ℝ} {φ : ℂ → ℝ}
    (hF : Integrable (fun x => φ x * coneRefField hcirc w x))
    (hL : Integrable (fun x : ℂ => φ x * Real.log ‖x‖))
    (hA : Integrable (fun x => φ x * hcirc ‖x‖ 0)) :
    lateralEval (coneRefPairing γ hC hcirc w) (coneRefCircle γ hcirc w) (.pairing φ) =
      lateralEval hC hcirc (.pairing φ) := by
  have hfun : (fun x : ℂ => φ x * coneRefCircle γ hcirc w ‖x‖ 0) =
      fun x => (φ x * hcirc ‖x‖ 0 - γ * (φ x * Real.log ‖x‖)) + φ x * coneRefField hcirc w x := by
    funext x
    rw [coneRefCircle_norm_zero γ hcirc w (norm_nonneg x)]
    have : coneRefField hcirc w x = coneRefProfile (fun ρ => hcirc ρ 0) w ‖x‖ := rfl
    rw [← this]
    ring
  simp only [lateralEval, coneRefPairing, fieldPairing]
  have hL' : Integrable (fun x : ℂ => γ * (φ x * Real.log ‖x‖)) := hL.const_mul γ
  have hAL : Integrable (fun x => φ x * hcirc ‖x‖ 0 - γ * (φ x * Real.log ‖x‖)) := hA.sub hL'
  rw [hfun, integral_add hAL hF, integral_sub hA hL', integral_const_mul]
  ring

/-- Lateral circle average of the cone data equals that of the field, given the circle integrability of the
radial part of the field and of the radial correction. -/
theorem lateralEval_coneRef_circle (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) {hcirc : ℝ → ℂ → ℝ}
    {w : ContinuousPath ℝ} {r : ℝ} {z : ℂ}
    (hF : CircleIntegrable (coneRefField hcirc w) z r)
    (hA : CircleIntegrable (fun x => hcirc ‖x‖ 0) z r) :
    lateralEval (coneRefPairing γ hC hcirc w) (coneRefCircle γ hcirc w) (.circle r z) =
      lateralEval hC hcirc (.circle r z) := by
  have hL : CircleIntegrable (fun x : ℂ => Real.log ‖x‖) z r := circleIntegrable_log_norm z r
  have hL' : CircleIntegrable (fun x : ℂ => γ * Real.log ‖x‖) z r := hL.const_mul γ
  have hfun : (fun x : ℂ => coneRefCircle γ hcirc w ‖x‖ 0) =
      fun x => (hcirc ‖x‖ 0 - γ * Real.log ‖x‖) + coneRefField hcirc w x := by
    funext x
    rw [coneRefCircle_norm_zero γ hcirc w (norm_nonneg x)]
    rfl
  have h3 : Real.circleAverage (fun x : ℂ => γ * Real.log ‖x‖) z r =
      γ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r :=
    Real.circleAverage_fun_smul (a := γ)
  simp only [lateralEval]
  have hAL : CircleIntegrable (fun x : ℂ => hcirc ‖x‖ 0 - γ * Real.log ‖x‖) z r := hA.sub hL'
  rw [hfun, Real.circleAverage_fun_add hAL hF, Real.circleAverage_fun_sub hA hL', h3]
  simp only [coneRefCircle, fieldCircleAverage]
  ring

end Identities

section Ae

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- For a whole-plane GFF and an admissible observable `o` fixed in advance, almost surely the lateral observable
`o` of the cone data built from the field and a continuous path `w` equals that of the field, simultaneously for
all continuous paths `w`. -/
theorem ae_lateralProcess_coneRef_apply (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    (o : GFFObservable.Admissible) :
    ∀ᵐ ω ∂P, ∀ w : ContinuousPath ℝ,
      lateralProcess (coneRefPairing γ (hC ω) (hcirc ω) w) (coneRefCircle γ (hcirc ω) w) o =
        lateralProcess (hC ω) (hcirc ω) o := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ =>
    filter_upwards [wholePlaneGFF_ae_integrable_radial_mul hh ho, hh.ae_continuousOn_circle]
      with ω hA hc w
    have hφ : IsTestFunction Set.univ φ := ho
    have hFc := continuous_coneRefField (continuousOn_radial_of_continuousOn hc) w
    have hF : Integrable (fun x => φ x * coneRefField (hcirc ω) w x) :=
      (hφ.1.continuous.mul hFc).integrable_of_hasCompactSupport hφ.2.1.mul_right
    have hL : Integrable (fun x : ℂ => φ x * Real.log ‖x‖) := by
      have := LatticeProb.LocalMeasureKernel.LocalDecoderCommon.locallyIntegrable_log_norm_complex.integrable_smul_left_of_hasCompactSupport
        hφ.1.continuous hφ.2.1
      simpa [smul_eq_mul] using this
    exact lateralEval_coneRef_pairing γ (hC ω) hF hL hA
  | circle r z =>
    filter_upwards [wholePlaneGFF_ae_circleIntegrable_radial hh r z, hh.ae_continuousOn_circle]
      with ω hA hc w
    have hFc := continuous_coneRefField (continuousOn_radial_of_continuousOn hc) w
    exact lateralEval_coneRef_circle γ (hC ω) hFc.continuousOn.circleIntegrable' hA

end Ae

end MatedCRT.FirstPass.Derived
