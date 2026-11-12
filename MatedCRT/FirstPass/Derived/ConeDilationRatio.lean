import MatedCRT.Steps.Sec2.LQGMeasureProperties
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.GMCAffineCovariance

/-!
# The non-dyadic dilation part of Fact 2.2 from the ratio limit

`LQGMeasureNonDyadicDilationPart` (Steps/Sec2/LQGMeasureProperties.lean) asks, for the field of the γ-quantum cone and
its LQG measure `μ`, that almost surely for every `s ∈ (1, 2)` the dilated field
`(r, z) ↦ h_{s r}(s z) + Q log s` has LQG measure `μ ∘ (x ↦ s x)` (the image of `μ` under `x ↦ s⁻¹ x`), with the
measure again obtained as the dyadic limit.

By the change of variables `x = s z` (library `lqgApprox_affine`), the approximation of the dilated field at scale
`2^{-k}` is the image of the approximation of `h` at scale `s 2^{-k}`. So the statement is the vague convergence of the
approximations of `h` along the scales `s 2^{-k}`, simultaneously in `s`. By the reduction of the library
(`isLQGLimitAlong_of_ratio_Ioc`) it suffices to have this for the ratios `r ∈ (1/2, 1]`.

## Main results

* `isLQGLimit_dilate_of_ratio`: pathwise, the ratio limit for all `r ∈ (1/2, 1]` gives the dyadic limit of every
  dilated field `(r, z) ↦ h_{s r}(s z) + Q log s`, `s > 0`, to the image measure.
* `lqgMeasureNonDyadicDilationPart_of_ratio`: `LQGMeasureNonDyadicDilationPart` follows from the almost sure ratio limit
  of the cone field (the ratio limit at all `r ∈ (1/2, 1]` simultaneously).
-/

open MeasureTheory Filter Set

namespace MatedCRT.FirstPass.Derived

/-- **Dilation from the ratio limit (pathwise).** If the approximations of `h` converge vaguely to `m` along `r 2^{-k}`
for every `r ∈ (1/2, 1]`, then for every `s > 0` the dyadic approximations of the dilated field
`(r, z) ↦ h (s r) (s z) + Q log s` converge vaguely to the image of `m` under `x ↦ s⁻¹ x`. -/
theorem isLQGLimit_dilate_of_ratio {γ : ℝ} (hγ : γ ≠ 0) {h : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (H : ∀ r ∈ Ioc (1 / 2 : ℝ) 1,
      LatticeProb.LQG.IsLQGLimitAlong γ h (fun k => r * LatticeProb.LQG.dyadicScale k) m)
    {s : ℝ} (hs : 0 < s) :
    HarmonicBalls.IsLQGLimit γ (fun r z => h (s * r) ((s : ℂ) * z) + HarmonicBalls.lqgQ γ * Real.log s)
      (m.map fun x => (s : ℂ)⁻¹ * x) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hnorm : ‖(s : ℂ)‖ = s := Complex.norm_of_nonneg hs.le
  have hAlong : LatticeProb.LQG.IsLQGLimitAlong γ h
      (fun k => ‖(s : ℂ)‖ * LatticeProb.LQG.dyadicScale k) m := by
    rw [hnorm]
    exact LatticeProb.LQG.isLQGLimitAlong_of_ratio_Ioc H hs
  have hA := LatticeProb.LQG.isLQGLimit_affine_map_of_along hγ h hs' 0 hAlong
  have hfield : LatticeProb.LQG.affineField γ (s : ℂ) 0 h =
      fun r z => h (s * r) ((s : ℂ) * z) + HarmonicBalls.lqgQ γ * Real.log s := by
    funext r z
    simp only [LatticeProb.LQG.affineField, hnorm, add_zero]
    rfl
  have hchart : LatticeProb.LQG.affineChart (s : ℂ) 0 = fun x => (s : ℂ)⁻¹ * x := by
    funext x
    simp only [LatticeProb.LQG.affineChart, sub_zero]
    rw [div_eq_inv_mul]
  rw [hfield, hchart] at hA
  exact (HarmonicBalls.LPBridge.isLQGLimit_iff _ _ _).2 hA

/-- **`LQGMeasureNonDyadicDilationPart` from the ratio limit of the cone field.** If, for every γ-quantum cone field
`(hC, hcirc)` with LQG measure `μ`, almost surely the approximations of `hcirc ω` converge vaguely to `μ ω` along
`r 2^{-k}` for every `r ∈ (1/2, 1]` simultaneously, then the non-dyadic dilation part of Fact 2.2 holds. -/
theorem lqgMeasureNonDyadicDilationPart_of_ratio
    (H : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsConeField γ P hC hcirc μ →
      ∀ᵐ ω ∂P, ∀ r ∈ Ioc (1 / 2 : ℝ) 1,
        LatticeProb.LQG.IsLQGLimitAlong γ (hcirc ω) (fun k => r * LatticeProb.LQG.dyadicScale k) (μ ω)) :
    LQGMeasureNonDyadicDilationPart := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  filter_upwards [H γ hγ0 hγ2 Ω P hC hcirc μ hcone] with ω hω s hs1 _
  exact isLQGLimit_dilate_of_ratio hγ0.ne' hω (by linarith)

end MatedCRT.FirstPass.Derived
