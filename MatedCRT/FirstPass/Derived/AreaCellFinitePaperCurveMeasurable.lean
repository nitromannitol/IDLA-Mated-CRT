import MatedCRT.FirstPass.Derived.AreaCellFinitePaperCurveComparison

/-! # Measurable finite-walk exit curves -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set MeasureTheory _root_.HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov LatticeProb
open ProbabilityTheory MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- The finite-walk comparison with continuous-curve measurability supplied. -/
theorem areaCell_finitePaperContinuousExitCurve_le_of_measurable
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ζ : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ζ))
    {δ : ℝ} (hδ : 0 < δ) (hlf : IsLocallyFiniteMult (S.mult δ ζ))
    (hc : (areaCellConfig h hδ (S.mult δ ζ)).IsCellConfiguration)
    (hpos : ∀ K, 0 < (areaCellConfig h hδ (S.mult δ ζ)).holding K)
    {a m : ℝ≥0} (ha : 0 < a) (hm : 0 < m)
    {U : Set ℂ} (hU : IsOpen U)
    (hconv : Convex ℝ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U))
    (P : Measure (ℕ → (areaCellConfig h hδ (S.mult δ ζ)).cells))
    (R : Set (areaCellConfig h hδ (S.mult δ ζ)).cells) [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] (A : Set R)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R →
      (areaCellConfig h hδ (S.mult δ ζ)).c v w = 0)
    (hactive : ∀ v ∈ A, 0 < (LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hδ (S.mult δ ζ)).cells) =>
        (areaCellConfig h hδ (S.mult δ ζ)).c v w)
      (areaCellConfig_conductance_symm h hδ (S.mult δ ζ) (S.mult_symm δ ζ))
      (areaCellConfig_conductance_nonneg h hδ (S.mult δ ζ))
      (areaCellConfig_conductance_self h hδ (S.mult δ ζ) (S.mult_self δ ζ)) R).totalConductance v)
    (v : R)
    (hP : P = ((LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hδ (S.mult δ ζ)).cells) =>
        (areaCellConfig h hδ (S.mult δ ζ)).c v w)
      (areaCellConfig_conductance_symm h hδ (S.mult δ ζ) (S.mult_symm δ ζ))
      (areaCellConfig_conductance_nonneg h hδ (S.mult δ ζ))
      (areaCellConfig_conductance_self h hδ (S.mult δ ζ) (S.mult_self δ ζ)) R).trajectoryLaw A hactive v).map
      (fun p n => (p n : (areaCellConfig h hδ (S.mult δ ζ)).cells)))
    (hB : (fun x : R => (x : (areaCellConfig h hδ (S.mult δ ζ)).cells)) ⁻¹'
      {K | (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) K ∈
        Complex.orthonormalBasisOneI.repr.symm ⁻¹' U} = A)
    (E : Set (ℕ → (areaCellConfig h hδ (S.mult δ ζ)).cells)) (r s : ℝ≥0)
    (hbad : P E ≤ (r : ℝ≥0∞))
    (hgood : ∀ᵐ path ∂P, path ∉ E →
      (areaCellConfig h hδ (S.mult δ ζ)).JumpTimesUnbounded path ∧
      (∀ n, (areaCellConfig h hδ (S.mult δ ζ)).Adj (path n) (path (n + 1))) ∧
      (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) (path 0) ∈
        Complex.orthonormalBasisOneI.repr.symm ⁻¹' U ∧
      hitTime {K : (areaCellConfig h hδ (S.mult δ ζ)).cells |
        (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) K ∉
          Complex.orthonormalBasisOneI.repr.symm ⁻¹' U} path ≠ ⊤ ∧
      ∀ n, ENNReal.ofReal (2 * ((a : ℝ) * (Metric.diam ((path n).1 : Set Plane) +
        Metric.diam ((path (n + 1)).1 : Set Plane)))) < (r : ℝ≥0∞))
    (ν : Measure (BouRabeeGwynne.CurveSpace 2))
    (hsource : levyProkhorovEDist
      ((srwLaw (S.mult δ ζ) ((euclideanCellEquiv h hδ).symm v.1)).map
        (stoppedPolygonalCurve
          ((fun K => (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) K) ∘
            euclideanCellEquiv h hδ)
          {i | ∃ x ∈ A, euclideanCellEquiv h hδ i = x.1})) ν ≤ (s : ℝ≥0∞)) :
    levyProkhorovEDist
      ((P.map (fun y n => (euclideanCellEquiv h hδ).symm (y n))).map
        (fun x => CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath ((a : ℝ) • interpPathCM (vertexPoint δ (S.η ζ)) hm.le x))
            (pathExitTime U ((a : ℝ) • interpPathCM (vertexPoint δ (S.η ζ)) hm.le x)).toNNReal))) ν ≤
      (r : ℝ≥0∞) + (s : ℝ≥0∞) := by
  have hX := ((CurveSpaceComparison.isometryEquiv 2).continuous.measurable.comp
    (measurable_areaCell_continuousExitCurve h hδ (S.mult δ ζ) hm.le (a : ℝ) hU)).aemeasurable (μ := P)
  exact areaCell_finitePaperContinuousExitCurve_le S ζ h hδ hlf hc hpos ha hm hU hconv
    P R A hretain hactive v hP hB E r s hbad hgood hX ν hsource

end MatedCRT
end
