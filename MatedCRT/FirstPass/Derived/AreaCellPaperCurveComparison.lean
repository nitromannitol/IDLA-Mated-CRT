import MatedCRT.FirstPass.Derived.AreaCellSourceContinuousCurveLaw
import LatticeProb.Walk.SourceStoppedCurveLawComparison

/-! # Comparison of area-cell stopped-curve laws -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set MeasureTheory HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov LatticeProb
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- A source polygonal-curve estimate controls the continuously stopped paper
curve law of the inverse-relabelled cell-path measure. -/
theorem areaCell_paperContinuousExitCurve_le
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {δ : ℝ} (hδ : 0 < δ) (c : ℤ → ℤ → ℕ)
    (hc : (areaCellConfig h hδ c).IsCellConfiguration)
    (hpos : ∀ K, 0 < (areaCellConfig h hδ c).holding K)
    {a m : ℝ≥0} (ha : 0 < a) (hm : 0 < m)
    {U : Set ℂ} (hU : IsOpen U)
    (hconv : Convex ℝ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U))
    (P : Measure (ℕ → (areaCellConfig h hδ c).cells))
    (E : Set (ℕ → (areaCellConfig h hδ c).cells)) (r s : ℝ≥0)
    (hbad : P E ≤ (r : ℝ≥0∞))
    (hgood : ∀ᵐ ω ∂P, ω ∉ E →
      (areaCellConfig h hδ c).JumpTimesUnbounded ω ∧
      (∀ n, (areaCellConfig h hδ c).Adj (ω n) (ω (n + 1))) ∧
      (a : ℝ) • areaCellRepresentative h hδ c (ω 0) ∈
        Complex.orthonormalBasisOneI.repr.symm ⁻¹' U ∧
      hitTime {K : (areaCellConfig h hδ c).cells |
        (a : ℝ) • areaCellRepresentative h hδ c K ∉
          Complex.orthonormalBasisOneI.repr.symm ⁻¹' U} ω ≠ ⊤ ∧
      ∀ n, ENNReal.ofReal (2 * ((a : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
        Metric.diam ((ω (n + 1)).1 : Set Plane)))) < (r : ℝ≥0∞))
    (hX : AEMeasurable (fun ω : ℕ → (areaCellConfig h hδ c).cells =>
      let g := ConstantStepInterpolation.continuousPlanePath m
        (fun n => (a : ℝ) • areaCellRepresentative h hδ c (ω n))
      CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve g
          (LatticeProb.continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0 g).toNNReal)) P)
    (hY : AEMeasurable (stoppedPolygonalCurve
      (fun K => (a : ℝ) • areaCellRepresentative h hδ c K)
      {K | (a : ℝ) • areaCellRepresentative h hδ c K ∈
        Complex.orthonormalBasisOneI.repr.symm ⁻¹' U}) P)
    (ν : Measure (BouRabeeGwynne.CurveSpace 2))
    (hsource : levyProkhorovEDist
      (P.map (stoppedPolygonalCurve
        (fun K => (a : ℝ) • areaCellRepresentative h hδ c K)
        {K | (a : ℝ) • areaCellRepresentative h hδ c K ∈
          Complex.orthonormalBasisOneI.repr.symm ⁻¹' U})) ν ≤ (s : ℝ≥0∞)) :
    levyProkhorovEDist
      ((P.map (fun y n => (euclideanCellEquiv h hδ).symm (y n))).map
        (fun x => CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath ((a : ℝ) • interpPathCM (vertexPoint δ η) hm.le x))
            (pathExitTime U ((a : ℝ) • interpPathCM (vertexPoint δ η) hm.le x)).toNNReal))) ν ≤
      (r : ℝ≥0∞) + (s : ℝ≥0∞) := by
  have hU' : IsOpen (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) :=
    hU.preimage Complex.orthonormalBasisOneI.repr.symm.continuous
  have hbound := LatticeProb.CellConfigInterpolation.levyProkhorov_continuousExitCurve_le
    (areaCellConfig h hδ c) hc (areaCellRepresentative h hδ c)
    (areaCellRepresentative_mem h hδ c) hpos ha hm hU' hconv P E r s hbad hgood hX hY ν hsource
  change levyProkhorovEDist (P.map (fun y => CurveSpaceComparison.isometryEquiv 2
    (normalizedPrefixCurve
      (ConstantStepInterpolation.continuousPlanePath m
        (fun n => (a : ℝ) • areaCellRepresentative h hδ c (y n)))
      (LatticeProb.continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
        (ConstantStepInterpolation.continuousPlanePath m
          (fun n => (a : ℝ) • areaCellRepresentative h hδ c (y n)))).toNNReal))) ν ≤
    (r : ℝ≥0∞) + (s : ℝ≥0∞) at hbound
  exact le_of_eq_of_le (congrArg (fun Q => levyProkhorovEDist Q ν)
    (areaCell_sourceContinuousExitCurve_law h hδ c hm.le (a : ℝ) hU P)).symm hbound

end MatedCRT
end
