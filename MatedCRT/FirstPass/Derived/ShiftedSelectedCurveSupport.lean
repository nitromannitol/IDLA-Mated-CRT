import MatedCRT.FirstPass.Derived.ConeShiftedSelectedWalkLaw
import MatedCRT.FirstPass.Derived.EuclideanCurveLawSupport
import LatticeProb.Walk.CellConfigVisitPathLaw

/-! # Support of shifted selected walk curves -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open LatticeProb LatticeProb.CellConfigWalk LatticeProb.ReparamDistanceIsometry
open scoped NNReal

namespace MatedCRT

/-- The Euclidean path law of the selected shifted walk is a probability measure. -/
theorem shiftedSelectedWalkLaw_euclidean_isProbability
    (η : ℝ → ℂ) (w : MatedCRTHarmonic.MatedCRT.Path2)
    (ε τ : ℝ) (m : ℝ≥0) (z : ℂ) :
    IsProbabilityMeasure ((shiftedSelectedWalkLaw ε m τ z η w).map complexToEuclideanPath) := by
  unfold shiftedSelectedWalkLaw
  rw [Measure.map_map continuous_complexToEuclideanPath.measurable
    (measurable_interpPathCM _ m.coe_nonneg)]
  exact (Measure.isProbabilityMeasure_map_iff
    (continuous_complexToEuclideanPath.measurable.comp
      (measurable_interpPathCM _ m.coe_nonneg)).aemeasurable).2 inferInstance

/-- A shifted selected walk has unbounded Euclidean range when its relabelled
integer law is the walk of a matching line-connected cell configuration. -/
theorem ae_unbounded_range_shiftedSelectedWalkLaw
    (η : ℝ → ℂ) (w : MatedCRTHarmonic.MatedCRT.Path2)
    (ε θ : ℝ) (m : ℝ≥0) (hm : 0 < m) (z : ℂ)
    (H : CellConfig) (hH : H.IsCellConfiguration) (hL : H.LineConnected)
    (e : ℤ ≃ H.cells)
    (hmem : ∀ k, Complex.orthonormalBasisOneI.repr
      (vertexPoint ε (fun t => η (t + ε * θ)) k) ∈ ((e k).1 : Set Plane))
    (hQ : H.IsSRWLaw (e (vertexOf ε (fun t => η (t + ε * θ)) z))
      ((srwLaw (bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
        (fun t => (w (t + ε * θ)).2))
          (vertexOf ε (fun t => η (t + ε * θ)) z)).map
            (fun ξ n => e (ξ n)))) :
    ∀ᵐ (f : C(ℝ≥0, Plane)) ∂((shiftedSelectedWalkLaw ε m (ε * θ) z η w).map complexToEuclideanPath),
      ¬ Bornology.IsBounded (Set.range f) := by
  let Q := srwLaw (bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
    (fun t => (w (t + ε * θ)).2)) (vertexOf ε (fun t => η (t + ε * θ)) z)
  let E : (ℕ → ℤ) → ℕ → H.cells := fun ξ n => e (ξ n)
  have hE : Measurable E := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable e).comp (measurable_pi_apply n)
  have hinf : ∀ᵐ ξ ∂Q, (Set.range (E ξ)).Infinite :=
    ae_of_ae_map hE.aemeasurable (ae_infinite_range_of_lineConnected H hH hL hQ)
  have hm' : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  have hpath : Measurable (fun ξ => complexToEuclideanPath
      (interpPathCM (vertexPoint ε (fun t => η (t + ε * θ))) m.coe_nonneg ξ)) :=
    continuous_complexToEuclideanPath.measurable.comp
      (measurable_interpPathCM _ m.coe_nonneg)
  have hmap : (shiftedSelectedWalkLaw ε m (ε * θ) z η w).map complexToEuclideanPath =
      Q.map (fun ξ => complexToEuclideanPath
        (interpPathCM (vertexPoint ε (fun t => η (t + ε * θ))) m.coe_nonneg ξ)) := by
    unfold shiftedSelectedWalkLaw
    exact Measure.map_map continuous_complexToEuclideanPath.measurable
      (measurable_interpPathCM _ m.coe_nonneg)
  rw [hmap]
  apply (ae_map_iff hpath.aemeasurable
    (LatticeProb.measurableSet_continuousMap_unbounded_range (0 : Plane))).2
  filter_upwards [hinf] with ξ hξ
  intro hb
  apply (unbounded_range_representatives_of_infinite_range_cells H hH (E ξ)
    (fun n => Complex.orthonormalBasisOneI.repr
      (vertexPoint ε (fun t => η (t + ε * θ)) (ξ n)))
    (fun n => hmem (ξ n)) hξ)
  apply hb.subset
  rintro _ ⟨n, rfl⟩
  refine ⟨((n : ℝ) / (m : ℝ)).toNNReal, ?_⟩
  change Complex.orthonormalBasisOneI.repr
    (interpPathCM (vertexPoint ε (fun t => η (t + ε * θ))) m.coe_nonneg ξ _) = _
  rw [interpPathCM_vertexPoint, interpolatedWalk_natCast_div hm']

end MatedCRT
end
