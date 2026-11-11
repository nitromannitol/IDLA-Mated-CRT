import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Basic.Complex.Basic

/-! # Occupation under a differentiable time change -/

namespace MatedCRT

open Set

/-- A continuously differentiable clock converts occupation of its
reparametrized path into occupation of the original path weighted by the
clock density. The tracking identity is needed only up to the terminal
Brownian time. -/
theorem clock_occupation_substitution
    {T : ℝ} (hT : 0 ≤ T) (A a : ℝ → ℝ) (p q : ℝ → ℂ) (f : ℂ → ℝ)
    (hA0 : A 0 = 0) (hA : ContinuousOn A (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivWithinAt A (a t) (Ioi t) t)
    (ha : ContinuousOn a (Icc 0 T))
    (hq : ContinuousOn q (A '' Icc 0 T)) (hf : Continuous f)
    (htrack : ∀ t ∈ Icc 0 T, q (A t) = p t) :
    (∫ t in (0 : ℝ)..T, f (p t) * a t) =
      ∫ s in (0 : ℝ)..(A T), f (q s) := by
  have hsubst := intervalIntegral.integral_comp_mul_deriv''
    (a := 0) (b := T) (f := A) (f' := a) (g := fun s => f (q s))
    (by simpa only [uIcc_of_le hT] using hA)
    (by simpa only [min_eq_left hT, max_eq_right hT] using hderiv)
    (by simpa only [uIcc_of_le hT] using ha)
    (by simpa only [uIcc_of_le hT, Function.comp_def] using hf.comp_continuousOn hq)
  calc
    _ = ∫ t in (0 : ℝ)..T, ((fun s => f (q s)) ∘ A) t * a t := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hT]
      intro t ht
      simp only [Function.comp_apply, htrack t ht]
    _ = _ := by simpa only [hA0] using hsubst

end MatedCRT

#print axioms MatedCRT.clock_occupation_substitution
