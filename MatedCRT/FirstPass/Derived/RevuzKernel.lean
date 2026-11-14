import MatedCRT.FirstPass.Derived.RevuzRegularize
import LatticeProb.Prob.OccupationMeasureKernel

/-!
# The occupation kernel of the regularized clock is measurable

For a family `A` of measurable functionals of the canonical planar path, the map
`ω ↦ occupationMeasure (regularize A · ω) ω` is a measurable function from the path space to `Measure ℂ`.
Hence the iterated `bind` in `MatedCRT.revuz` is the genuine Revuz integral `∫ dz ∫ W z (dω) ∫_{(0,1]} 1_S(ω_s) dA_s`
and not the zero measure obtained from a non-measurable integrand.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- For a monotone clock, `stieltjesOfNNReal` is the Stieltjes function of the monotone extension to `ℝ`. -/
theorem stieltjesOfNNReal_apply_of_monotone {a : ℝ≥0 → ℝ≥0} (h : Monotone a) (x : ℝ) :
    stieltjesOfNNReal a x = Function.rightLim (fun y : ℝ => ((a y.toNNReal : ℝ≥0) : ℝ)) x := by
  unfold stieltjesOfNNReal
  simp only [h, ↓reduceDIte]
  rfl

/-- The Stieltjes function of the regularized clock is a measurable function of the path. -/
theorem measurable_stieltjesOfNNReal_regularize {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (x : ℝ) :
    Measurable fun ω : ContinuousPath ℂ => stieltjesOfNNReal (fun t => regularize A t ω) x := by
  have hfun : (fun ω : ContinuousPath ℂ => stieltjesOfNNReal (fun t => regularize A t ω) x) =
      fun ω => Function.rightLim (fun y : ℝ => ((regularize A y.toNNReal ω : ℝ≥0) : ℝ)) x :=
    funext fun ω => stieltjesOfNNReal_apply_of_monotone (regularize_monotone A ω) x
  rw [hfun]
  refine LatticeProb.measurable_rightLim_of_monotone
    (a := fun ω y => ((regularize A y.toNNReal ω : ℝ≥0) : ℝ)) (fun ω y z hyz => ?_)
    (fun y => measurable_coe_nnreal_real.comp (measurable_regularize hA _)) x
  exact_mod_cast regularize_monotone A ω (Real.toNNReal_mono hyz)

/-- **The occupation kernel is measurable.**  For measurable functionals `A t`, the map
`ω ↦ occupationMeasure (regularize A · ω) ω` from the canonical planar path space to `Measure ℂ` is measurable. -/
theorem measurable_occupationMeasure_regularize {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) :
    Measurable fun ω : ContinuousPath ℂ => occupationMeasure (fun t => regularize A t ω) ω := by
  unfold occupationMeasure
  exact LatticeProb.measurable_map_stieltjes_restrict_Ioc
    (F := fun ω : ContinuousPath ℂ => stieltjesOfNNReal (fun t => regularize A t ω))
    (measurable_stieltjesOfNNReal_regularize hA) (fun ω s => ω s.toNNReal)
    (fun ω => ω.continuous.comp continuous_real_toNNReal)
    (fun s => ContinuousMap.measurable_eval _)

end MatedCRT
