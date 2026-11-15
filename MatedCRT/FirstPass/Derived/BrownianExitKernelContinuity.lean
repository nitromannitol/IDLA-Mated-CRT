import MatedCRT.FirstPass.Derived.BrownianHarmonicMeasureContinuity
import MatedCRT.FirstPass.Derived.TargetLawTemplateEvent

/-! Weak continuity of the planar Brownian exit probability kernel. -/

set_option autoImplicit false

open MeasureTheory Filter Set HarmonicBalls MarkovProcess
open scoped Topology

namespace MatedCRT

/-- The law of the first exit position from an open set. -/
noncomputable def planarBrownianExitProbability (U : Set ℂ) (hU : IsOpen U)
    (z : ℂ) : ProbabilityMeasure ℂ := by
  let f : ContinuousPath ℂ → ℂ := fun ω => ω ((ContinuousPath.exitTime U ω).toNNReal)
  have hf : Measurable f := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  exact ⟨(planarBrownianMotion z).map f,
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance⟩

/-- The exit probability law varies continuously with an interior starting point. -/
theorem continuous_planarBrownianExitProbability {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    Continuous (fun z : U => planarBrownianExitProbability U hU z) := by
  let F : U → LevyProkhorov (ProbabilityMeasure ℂ) :=
    fun z => LevyProkhorov.ofMeasure (planarBrownianExitProbability U hU z)
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ :=
      exists_forall_levyProkhorovDist_planarBrownian_exitLaw_le hU hUb
        (isCompact_singleton : IsCompact ({(z : ℂ)} : Set ℂ))
        (singleton_subset_iff.mpr z.property) (half_pos hε)
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    change dist (y : ℂ) (z : ℂ) < δ at hy
    have hd := hbound z (mem_singleton (z : ℂ)) y (by simpa only [dist_comm] using hy)
    have hlt := lt_of_le_of_lt hd (half_lt_self hε)
    rw [levyProkhorovDist_comm] at hlt
    change levyProkhorovDist
      ((planarBrownianMotion y).map fun ω => ω ((ContinuousPath.exitTime U ω).toNNReal))
      ((planarBrownianMotion z).map fun ω => ω ((ContinuousPath.exitTime U ω).toNNReal)) < ε
    exact hlt
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.comp hF

/-- Euclidean-coordinate exit probability laws inherit the same continuity. -/
theorem continuous_euclidean_planarBrownianExitProbability {U : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    Continuous (fun z : U => (planarBrownianExitProbability U hU z).map
      Complex.orthonormalBasisOneI.repr) :=
  (ProbabilityMeasure.continuous_map Complex.orthonormalBasisOneI.repr.continuous).comp
    (continuous_planarBrownianExitProbability hU hUb)

end MatedCRT
