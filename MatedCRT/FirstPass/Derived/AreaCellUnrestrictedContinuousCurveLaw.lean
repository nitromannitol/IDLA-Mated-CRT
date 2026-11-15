import MatedCRT.FirstPass.Derived.AreaCellAbsorbedContinuousCurveLaw
import MatedCRT.FirstPass.Derived.DiscreteAbsorptionContinuousExit

/-! # Finite and unrestricted continuous exit-curve laws -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory _root_.HarmonicBalls LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped NNReal

/-- With matching active vertices, the finite cell walk and unrestricted integer
walk have the same continuously stopped curve law. -/
theorem areaCell_finite_unrestricted_sourceContinuousExitCurve_law
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε) (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] (A : Set R)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R →
      (areaCellConfig h hε (S.mult ε ω)).c v w = 0)
    (hpos : ∀ v ∈ A, 0 < (LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).totalConductance v)
    (v : R) {m : ℝ} (hm : 0 < m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (hactive : {i : ℤ | ∃ x ∈ A, euclideanCellEquiv h hε i =
      (x : (areaCellConfig h hε (S.mult ε ω)).cells)} =
      (fun i => a • areaCellRepresentative h hε (S.mult ε ω)
        (euclideanCellEquiv h hε i)) ⁻¹'
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U)) :
    let e := euclideanCellEquiv h hε
    let N := LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
    (((N.trajectoryLaw A hpos v).map (fun p n =>
      (p n : (areaCellConfig h hε (S.mult ε ω)).cells))).map
      (fun y => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (ConstantStepInterpolation.continuousPlanePath m
            (fun n => a • areaCellRepresentative h hε (S.mult ε ω) (y n)))
          (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
            (ConstantStepInterpolation.continuousPlanePath m
              (fun n => a • areaCellRepresentative h hε (S.mult ε ω) (y n)))).toNNReal))) =
    (srwLaw (S.mult ε ω) (e.symm v.1)).map
      (fun x => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath (a • interpPathCM (vertexPoint ε (S.η ω)) hm.le x))
          (pathExitTime U (a • interpPathCM (vertexPoint ε (S.η ω)) hm.le x)).toNNReal)) := by
  classical
  dsimp only
  rw [areaCell_finite_sourceContinuousExitCurve_law S ω h hε hlf R A hretain hpos v hm.le a hU]
  rw [hactive]
  let p : ℤ → ReflectedGMS.Plane := fun i =>
    a • areaCellRepresentative h hε (S.mult ε ω) (euclideanCellEquiv h hε i)
  let V : Set ReflectedGMS.Plane := Complex.orthonormalBasisOneI.repr.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage Complex.orthonormalBasisOneI.repr.symm.continuous
  have hp : Measurable (fun x : ℕ → ℤ =>
      a • interpPathCM (vertexPoint ε (S.η ω)) hm.le x) :=
    ((continuous_interpPathCM (vertexPoint ε (S.η ω)) hm.le).const_smul a).measurable
  have hc := (CurveSpaceComparison.isometryEquiv 2).continuous.measurable.comp
    ((measurable_paperNormalizedExitCurve hU).comp hp)
  change Measurable (fun x : ℕ → ℤ => CurveSpaceComparison.isometryEquiv 2
    (normalizedPrefixCurve
      (complexToEuclideanPath (a • interpPathCM (vertexPoint ε (S.η ω)) hm.le x))
      (pathExitTime U (a • interpPathCM (vertexPoint ε (S.η ω)) hm.le x)).toNNReal)) at hc
  rw [Measure.map_map hc (measurable_stoppedPath (p ⁻¹' V))]
  congr 1
  funext x
  apply congrArg (CurveSpaceComparison.isometryEquiv 2)
  rw [← areaCell_scaled_normalizedExitCurve_eq h hε (S.mult ε ω) hm.le a
    (stoppedPath (p ⁻¹' V) x) U,
    ← areaCell_scaled_normalizedExitCurve_eq h hε (S.mult ε ω) hm.le a x U]
  exact continuousExitCurve_stoppedPath p hV (show (0 : ℝ≥0) < ⟨m, hm.le⟩ from hm) x

end MatedCRT
end
