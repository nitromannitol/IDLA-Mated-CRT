import MatedCRT.FirstPass.Derived.AreaCellPaperCurveComparison
import MatedCRT.FirstPass.Derived.AreaCellFullStoppedCurveLaw
import LatticeProb.Walk.SourceStoppedCurveLawComparison

/-! # Comparison of area-cell stopped-curve laws -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set MeasureTheory _root_.HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov LatticeProb
open ProbabilityTheory MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- A stopped integer-walk curve estimate controls the paper curve law of a
finite restricted walk, under the stated geometric and good-path conditions. -/
theorem areaCell_finitePaperContinuousExitCurve_le
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
    (hX : AEMeasurable (fun path : ℕ → (areaCellConfig h hδ (S.mult δ ζ)).cells =>
      let g := ConstantStepInterpolation.continuousPlanePath m
        (fun n => (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) (path n))
      CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve g
          (LatticeProb.continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0 g).toNNReal)) P)
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
  classical
  let _ : Countable (areaCellConfig h hδ (S.mult δ ζ)).cells :=
    Countable.of_equiv ℤ (euclideanCellEquiv h hδ)
  have hY := (LatticeProb.measurable_stoppedPolygonalCurve_countable
    (fun K : (areaCellConfig h hδ (S.mult δ ζ)).cells =>
      (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) K)
    {K | (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) K ∈
      Complex.orthonormalBasisOneI.repr.symm ⁻¹' U}).aemeasurable (μ := P)
  have heq := areaCellConfig_fullCell_stopped_curveLaw S ζ h hδ hlf R A hretain hactive v
    (fun K => (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) K)
    {K | (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) K ∈
      Complex.orthonormalBasisOneI.repr.symm ⁻¹' U} hB
  dsimp only at heq
  rw [← hP] at heq
  have hsource' : levyProkhorovEDist
      (P.map (stoppedPolygonalCurve
        (fun K => (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) K)
        {K | (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ζ) K ∈
          Complex.orthonormalBasisOneI.repr.symm ⁻¹' U})) ν ≤ (s : ℝ≥0∞) := by
    rw [heq]
    exact hsource
  exact areaCell_paperContinuousExitCurve_le h hδ (S.mult δ ζ) hc hpos ha hm hU hconv
    P E r s hbad hgood hX hY ν hsource'

end MatedCRT
end
