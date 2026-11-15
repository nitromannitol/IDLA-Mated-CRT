import MatedCRT.FirstPass.Derived.AreaCellNestedPathLaw
import MatedCRT.FirstPass.Derived.ValidIntegerWalkCurveSupport

/-! # Support of relabelled walk path laws -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS
open LatticeProb.ConstantStepInterpolation LatticeProb.ReparamDistanceIsometry
open scoped NNReal

/-- At each positive mesh, for almost every valid environment, every relabelled
walk has a probability law supported on unbounded constant-step curves. -/
theorem MatedCRTEnv.IsValid.ae_areaCell_nested_path_law_support
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      ∀ (x : ℤ) (v : ℝ) (_hv : 0 < v),
        let Q := ((srwLaw (S.mult ε ω) x).map
          (fun ξ n => euclideanCellEquiv h hε (ξ n))).map
          (fun ξ => continuousPlanePath v
            (fun n => areaCellRepresentative h hε (S.mult ε ω) (ξ n)))
        IsProbabilityMeasure Q ∧
          ∀ᵐ (f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) ∂Q,
            ¬ Bornology.IsBounded (Set.range f) := by
  filter_upwards [hS.isAreaParametrized,
    hS.ae_unbounded_range_map_integerWalk S hε] with ω harea hsupp
  refine ⟨harea, ?_⟩
  intro x v hv
  dsimp only
  rw [areaCell_constantStepPath_nested_map harea hε (S.mult ε ω) hv.le]
  constructor
  · apply (Measure.isProbabilityMeasure_map_iff ?_).2 inferInstance
    exact (continuous_complexToEuclideanPath.measurable.comp
      (measurable_interpPathCM (vertexPoint ε (S.η ω)) hv.le)).aemeasurable
  · exact hsupp x v hv

end MatedCRT
end
