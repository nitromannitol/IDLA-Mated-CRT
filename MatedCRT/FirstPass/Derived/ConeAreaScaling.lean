import MatedCRT.FirstPass.Derived.ConeDilationRatioHolds
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime
import MatedCRT.Proofs.Infra.Setting
import HarmonicBalls.Proofs.Sec2.AffineField

/-!
# Scaling of the area measure of the quantum cone at every radius

For the field `h` of the `γ`-quantum cone with `γ`-LQG measure `μ`, `R > 0` and `b > 0`, let
`h^{R,b} = h(R ·) + Q log R - γ⁻¹ log b` be the rescaled field, with circle averages `rescaledCircle γ hcirc R b`.
Then the `γ`-LQG measure of `h^{R,b}` is `b⁻¹` times the image of `μ` under `z ↦ R⁻¹ z`:
`μ_{h^{R,b}} = b⁻¹ (z ↦ R⁻¹ z)_* μ_h` (`rescaledMeasure μ R b`).

The identity holds almost surely for all `R > 0` and `b > 0` simultaneously, so in particular at a radius which
depends on the field, such as the cone scale radius `R_b`. The proof is pathwise on one event: the almost sure
vague convergence of the approximations of `h` along the scales `r 2^{-k}` for every ratio `r ∈ (1/2, 1]` at once
(`ae_isLQGLimitAlong_ratio_cone`) gives the dyadic limit of every dilated field
(`isLQGLimit_dilate_of_ratio`), and adding the constant `-γ⁻¹ log b` multiplies the limit by `b⁻¹`
(`HarmonicBalls.IsLQGLimit.add_const`). No convergence at all scales across the cone singularity is used beyond
these ratio limits.

## Main results

* `isLQGLimit_rescaledCircle_of_ratio`: pathwise, the ratio limits give the dyadic limit of every rescaled field.
* `MatedCRT.MatedCRTEnv.IsValid.ae_forall_isLQGLimit_rescaledCircle`: in a valid environment, almost surely, for all
  `R, b > 0`, the rescaled circle averages have dyadic LQG limit `rescaledMeasure (S.μ ω) R b`.
* `MatedCRT.MatedCRTEnv.IsValid.ae_eq_rescaledMeasure`: every LQG measure of the rescaled field at a random positive
  radius agrees almost surely with `rescaledMeasure (S.μ ω) (R ω) b`.
-/

open MeasureTheory Filter Set

namespace MatedCRT.FirstPass.Derived

/-- **Scaling of the LQG limit at every radius (pathwise).** If the approximations of `h` converge vaguely to `m`
along `r 2^{-k}` for every `r ∈ (1/2, 1]`, then for all `R, b > 0` the dyadic approximations of the rescaled field
`(r, z) ↦ h (R r) (R z) + Q log R - γ⁻¹ log b` converge vaguely to `b⁻¹ (z ↦ R⁻¹ z)_* m`. -/
theorem isLQGLimit_rescaledCircle_of_ratio {γ : ℝ} (hγ : γ ≠ 0) {h : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (H : ∀ r ∈ Ioc (1 / 2 : ℝ) 1,
      LatticeProb.LQG.IsLQGLimitAlong γ h (fun k => r * LatticeProb.LQG.dyadicScale k) m)
    {R b : ℝ} (hR : 0 < R) (hb : 0 < b) :
    HarmonicBalls.IsLQGLimit γ (rescaledCircle γ h R b) (rescaledMeasure m R b) := by
  have hA := (isLQGLimit_dilate_of_ratio hγ H hR).add_const (-(γ⁻¹ * Real.log b))
  have hexp : Real.exp (γ * -(γ⁻¹ * Real.log b)) = b⁻¹ := by
    have h1 : γ * -(γ⁻¹ * Real.log b) = -Real.log b := by
      field_simp
    rw [h1, Real.exp_neg, Real.exp_log hb]
  rw [hexp] at hA
  have hfield : rescaledCircle γ h R b =
      fun ε z => h (R * ε) ((R : ℂ) * z) + HarmonicBalls.lqgQ γ * Real.log R + -(γ⁻¹ * Real.log b) := by
    funext ε z
    simp only [rescaledCircle, sub_eq_add_neg]
  rw [hfield]
  exact hA

end MatedCRT.FirstPass.Derived

namespace MatedCRT

/-- **Area scaling in a valid environment, all radii at once.** Almost surely, for all `R > 0` and `b > 0`, the
rescaled circle averages `rescaledCircle γ (S.hcirc ω) R b` of the cone field have the dyadic `γ`-LQG limit
`rescaledMeasure (S.μ ω) R b = b⁻¹ (z ↦ R⁻¹ z)_* (S.μ ω)`. -/
theorem MatedCRTEnv.IsValid.ae_forall_isLQGLimit_rescaledCircle {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂S.P, ∀ R b : ℝ, 0 < R → 0 < b →
      HarmonicBalls.IsLQGLimit γ (rescaledCircle γ (S.hcirc ω) R b) (rescaledMeasure (S.μ ω) R b) := by
  filter_upwards [FirstPass.Derived.ae_isLQGLimitAlong_ratio_cone hγ0 hγ2 hS.isConeField] with ω hω R b hR hb
  exact FirstPass.Derived.isLQGLimit_rescaledCircle_of_ratio hγ0.ne' hω hR hb

/-- **Area scaling at a random radius.** In a valid environment, for `b > 0` and a radius `R ω > 0` which may depend
arbitrarily on the sample (for instance the cone scale radius `R_b`), every `γ`-LQG measure `ν` of the rescaled
circle averages agrees almost surely with `b⁻¹ (z ↦ (R ω)⁻¹ z)_* (S.μ ω)`. -/
theorem MatedCRTEnv.IsValid.ae_eq_rescaledMeasure {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {R : Ω → ℝ} {b : ℝ} (hR : ∀ᵐ ω ∂S.P, 0 < R ω) (hb : 0 < b) {ν : Ω → Measure ℂ}
    (hν : HarmonicBalls.IsLQGMeasure S.P γ (fun ω => rescaledCircle γ (S.hcirc ω) (R ω) b) ν) :
    ∀ᵐ ω ∂S.P, ν ω = rescaledMeasure (S.μ ω) (R ω) b := by
  filter_upwards [hS.ae_forall_isLQGLimit_rescaledCircle hγ0 hγ2, hR, hν] with ω hω hRω hνω
  exact hνω.unique (hω (R ω) b hRω hb)

end MatedCRT
