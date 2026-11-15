import MatedCRT.FirstPass.Derived.SelectedVertexScoreTransfer
import LatticeProb.Topology.TranslatedCurveLawUniformContinuity

/-! # Selected starting points and translated curve laws -/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory Filter Topology LatticeProb
open LatticeProb.UnboundedRayIntervalIntegrand
open LatticeProb.UnboundedRayCurveSpace

namespace MatedCRT

local instance : MeasurableSpace (UnboundedRayCurveSpace 2) := borel _
local instance : BorelSpace (UnboundedRayCurveSpace 2) := ⟨rfl⟩
attribute [local instance] dUnifMetricSpace

/-- On a fixed ball, small cells transfer selected-start curve-law failures
    to failures at their anchored vertices. -/
theorem selected_translatedCurveScore_failure_subset_vertex
    (μ : Measure (Path 2)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ (f : Path 2) ∂μ, ¬ Bornology.IsBounded (Set.range f))
    (ρ a : ℝ) (ha : 0 < a) :
    ∃ δ > 0, ∀ {η : ℝ → ℂ}, Continuous η →
      Tendsto η (cocompact ℝ) (cocompact ℂ) → Function.Surjective η →
      ∀ {ε : ℝ}, 0 < ε →
      ∀ (q : ℤ → ℂ × ProbabilityMeasure (UnboundedRayCurveSpace 2)),
      (∀ k, (q k).1 = vertexPoint ε η k) →
      (∀ k, (∃ z ∈ closedBall (0 : ℂ) ρ, z ∈ cell ε η k) →
        ∀ z ∈ cell ε η k, dist z (vertexPoint ε η k) ≤ δ) →
      ∀ t : ℝ,
      (∃ z ∈ closedBall (0 : ℂ) ρ,
        t + a < levyProkhorovDist
          (translatedCurveProbability μ hμ (Complex.orthonormalBasisOneI.repr z) :
            Measure (UnboundedRayCurveSpace 2))
          ((q (vertexOf ε η z)).2 : Measure (UnboundedRayCurveSpace 2))) →
      ∃ k, (q k).1 ∈ closedBall (0 : ℂ) (ρ + δ) ∧
        t < levyProkhorovDist
          (translatedCurveProbability μ hμ (Complex.orthonormalBasisOneI.repr (q k).1) :
            Measure (UnboundedRayCurveSpace 2))
          ((q k).2 : Measure (UnboundedRayCurveSpace 2)) := by
  obtain ⟨d, hd, hmod⟩ := translated_curveLaw_levyProkhorovDist_lt μ hμ
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (ρ + 1)) a ha
  let δ := min (d / 2) 1
  have hδ : 0 < δ := lt_min (half_pos hd) zero_lt_one
  have hδone : δ ≤ 1 := min_le_right _ _
  have hδd : δ < d := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hd)
  refine ⟨δ, hδ, ?_⟩
  intro η hη hp hs ε hε q hq hc t hfail
  obtain ⟨z, hz, hf⟩ := hfail
  let k := vertexOf ε η z
  have hzcell : z ∈ cell ε η k := Tightness.mem_cell_vertexOf hη hp hs hε z
  have hdist := hc k ⟨z, hz, hzcell⟩ z hzcell
  have hv : dist (vertexPoint ε η k) (0 : ℂ) ≤ ρ + δ := by
    have ht := dist_triangle (vertexPoint ε η k) z (0 : ℂ)
    rw [dist_comm (vertexPoint ε η k) z] at ht
    linarith [mem_closedBall.mp hz]
  have hzK : Complex.orthonormalBasisOneI.repr z ∈
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) (ρ + 1) := by
    rw [mem_closedBall, ← map_zero Complex.orthonormalBasisOneI.repr,
      Complex.orthonormalBasisOneI.repr.isometry.dist_eq]
    linarith [mem_closedBall.mp hz]
  have hvK : Complex.orthonormalBasisOneI.repr (vertexPoint ε η k) ∈
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) (ρ + 1) := by
    rw [mem_closedBall, ← map_zero Complex.orthonormalBasisOneI.repr,
      Complex.orthonormalBasisOneI.repr.isometry.dist_eq]
    linarith
  have hnear := hmod _ hzK _ hvK (by
    rw [Complex.orthonormalBasisOneI.repr.isometry.dist_eq]
    exact lt_of_le_of_lt hdist hδd)
  have htri := levyProkhorovDist_triangle
    (translatedCurveProbability μ hμ (Complex.orthonormalBasisOneI.repr z) :
      Measure (UnboundedRayCurveSpace 2))
    (translatedCurveProbability μ hμ (Complex.orthonormalBasisOneI.repr (vertexPoint ε η k)) :
      Measure (UnboundedRayCurveSpace 2))
    ((q k).2 : Measure (UnboundedRayCurveSpace 2))
  refine ⟨k, ?_, ?_⟩
  · rw [hq k, mem_closedBall]
    exact hv
  · rw [hq k]
    change t + a < levyProkhorovDist
      (translatedCurveProbability μ hμ (Complex.orthonormalBasisOneI.repr z) :
        Measure (UnboundedRayCurveSpace 2)) ((q k).2 : Measure (UnboundedRayCurveSpace 2)) at hf
    linarith

end MatedCRT
end
