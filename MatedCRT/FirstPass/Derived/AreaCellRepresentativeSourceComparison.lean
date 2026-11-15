import MatedCRT.FirstPass.Derived.AreaCellUnrestrictedContinuousCurveLaw
import LatticeProb.Walk.FiniteSourceSharpMeshCurveLaw

/-! # Representative area-cell exit-curve comparison -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set MeasureTheory _root_.HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- A representative stopped-curve bound controls the unrestricted continuously
stopped walk, with the local mesh error added. -/
theorem areaCell_representative_sourceContinuousExitCurve_le
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ₀ : Measure ℂ} (h : IsAreaParametrized μ₀ (S.η ω))
    {δ : ℝ} (hδ : 0 < δ) (hlf : IsLocallyFiniteMult (S.mult δ ω))
    (hc : (areaCellConfig h hδ (S.mult δ ω)).IsCellConfiguration)

    (hpos : ∀ K, 0 < (areaCellConfig h hδ (S.mult δ ω)).holding K) {a m : ℝ≥0} (ha : 0 < a) (hm : 0 < m)
    {Uc : Set ℂ} (hU : IsOpen Uc) (hconv : Convex ℝ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    (R : Set (areaCellConfig h hδ (S.mult δ ω)).cells) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (A : Set R)
    (hAB : ∀ v : R, v ∈ A ↔ (a : ℝ) • (areaCellRepresentative h hδ (S.mult δ ω)) v ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    (hA : ∀ v ∈ A, 0 < (finiteConductanceRestriction
      (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells => (areaCellConfig h hδ (S.mult δ ω)).c v w) (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R).totalConductance v)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R → (areaCellConfig h hδ (S.mult δ ω)).c v w = 0)
    (hpaths : ∀ v ∈ A, ∃ w : (areaCellConfig h hδ (S.mult δ ω)).cells, (a : ℝ) • (areaCellRepresentative h hδ (S.mult δ ω)) w ∉ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) ∧
      Relation.ReflTransGen (fun x y : (areaCellConfig h hδ (S.mult δ ω)).cells => 0 < (areaCellConfig h hδ (S.mult δ ω)).c x y) (v : (areaCellConfig h hδ (S.mult δ ω)).cells) w)
    (v : R) (hv : v ∈ A)
    (W : Set Plane) (d : ℝ) (hd : 0 ≤ d)
    (hbuffer : ∀ x ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc), Metric.closedBall x ((a : ℝ) * d) ⊆ W)
    (hmesh : ∀ K : (areaCellConfig h hδ (S.mult δ ω)).cells, (∃ z ∈ (K.1 : Set Plane), (a : ℝ) • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ d)
    (ν : Measure (BouRabeeGwynne.CurveSpace 2)) (s : ℝ≥0)
    (hsource : levyProkhorovEDist
      (((finiteConductanceRestriction
        (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells => (areaCellConfig h hδ (S.mult δ ω)).c v w) (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R).trajectoryLaw A hA v).map
        (stoppedPolygonalCurve
          (fun x : R => (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) x)
          {x : R | (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) x ∈
            (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)})) ν ≤ (s : ℝ≥0∞))
    (hactive : {i : ℤ | ∃ x ∈ A, euclideanCellEquiv h hδ i =
      (x : (areaCellConfig h hδ (S.mult δ ω)).cells)} =
      (fun i => (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω)
        (euclideanCellEquiv h hδ i)) ⁻¹'
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) :
    levyProkhorovEDist
      ((srwLaw (S.mult δ ω) ((euclideanCellEquiv h hδ).symm v.1)).map
        (fun x => CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath ((a : ℝ) • interpPathCM (vertexPoint δ (S.η ω)) hm.le x))
            (pathExitTime Uc ((a : ℝ) • interpPathCM (vertexPoint δ (S.η ω)) hm.le x)).toNNReal)))
      ν ≤
      ENNReal.ofReal (4 * ((a : ℝ) * d)) + (s : ℝ≥0∞) := by
  classical
  let C := areaCellConfig h hδ (S.mult δ ω)
  let e := euclideanCellEquiv h hδ
  let : Countable C.cells := Countable.of_equiv ℤ e
  have hb := LatticeProb.CellConfigInterpolation.levyProkhorov_continuousExitCurve_le_of_finite_source_sharp_local_mesh
    C hc
    (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
    (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
    (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω))
    (areaCellRepresentative h hδ (S.mult δ ω))
    (areaCellRepresentative_mem h hδ (S.mult δ ω)) hpos ha hm
    (hU.preimage Complex.orthonormalBasisOneI.repr.symm.continuous) hconv
    R A hAB hA hretain hpaths v hv _ rfl s W d hd hbuffer hmesh ν hsource
  have heq := areaCell_finite_unrestricted_sourceContinuousExitCurve_law
    S ω h hδ hlf R A hretain hA v (show 0 < (m : ℝ) from hm) (a : ℝ) hU hactive
  dsimp only at heq
  rw [heq] at hb
  exact hb

end MatedCRT
end
