import MatedCRT.FirstPass.Derived.UniformStartStoppedBM
import LatticeProb.Prob.MarkovPathKernelDense

/-! # Continuity of planar Brownian path laws in the starting point -/

set_option autoImplicit false

open MeasureTheory HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.StopAtExitCmp

/-- Planar Brownian motion viewed as a probability law on continuous paths. -/
noncomputable def planarBrownianPathLaw (z : ℂ) : ProbabilityMeasure (ContinuousPath ℂ) :=
  ⟨planarBrownianMotion z, inferInstance⟩

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- Planar Brownian path laws vary weakly continuously with their starting point. -/
theorem continuous_planarBrownianPathLaw : Continuous planarBrownianPathLaw := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro g
  have hF : Continuous (fun p : ContinuousPath ℂ × ℂ =>
      (⟨fun t => p.1 t + p.2, p.1.continuous.add continuous_const⟩ : ContinuousPath ℂ)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : (ContinuousPath ℂ × ℂ) × ℝ≥0 => p.1.1 p.2 + p.1.2)
    fun_prop
  have hF' : Continuous (fun p : ContinuousPath ℂ × ℂ => translatePath p.2 p.1) := by
    convert hF using 1
    funext p
    ext t
    rfl
  have h : Continuous (fun z : ℂ => ∫ b, g (translatePath z b)
      ∂(planarBrownianMotion 0)) := by
    change Continuous (fun z : ℂ => ∫ b, g (translatePath z b)
      ∂(planarBrownianPathLaw 0 : Measure (ContinuousPath ℂ)))
    apply LatticeProb.continuous_integral_of_continuous_measure
      (μ := fun _ : ℂ => planarBrownianPathLaw 0)
      (G := fun p => g (translatePath p.2 p.1)) continuous_const
    · exact g.continuous.comp hF'
    · exact fun p => g.norm_coe_le_norm _
  convert h using 1
  funext z
  change (∫ b, g b ∂planarBrownianMotion z) = _
  rw [← map_translatePath_planarBrownianMotion z]
  exact integral_map (translatePath z).measurable.aemeasurable g.continuous.aestronglyMeasurable

end MatedCRT.StopAtExitCmp
