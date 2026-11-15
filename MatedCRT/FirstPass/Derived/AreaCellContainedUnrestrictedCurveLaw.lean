import MatedCRT.FirstPass.Derived.AreaCellUnrestrictedContinuousCurveLaw

/-! # Contained finite and unrestricted continuous exit-curve laws -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set MeasureTheory _root_.HarmonicBalls LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped NNReal

/-- A finite restriction containing all active cells gives the unrestricted
continuous exit-curve law. -/
theorem areaCell_contained_unrestricted_sourceContinuousExitCurve_law
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
    (hAB : ∀ v : R, v ∈ A ↔ a • areaCellRepresentative h hε (S.mult ε ω) v ∈
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U))
    (hcontain : ∀ K : (areaCellConfig h hε (S.mult ε ω)).cells,
      a • areaCellRepresentative h hε (S.mult ε ω) K ∈
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) → K ∈ R) :
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
  have hactive : {i : ℤ | ∃ x ∈ A, euclideanCellEquiv h hε i =
      (x : (areaCellConfig h hε (S.mult ε ω)).cells)} =
      (fun i => a • areaCellRepresentative h hε (S.mult ε ω)
        (euclideanCellEquiv h hε i)) ⁻¹'
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) := by
    ext i
    constructor
    · rintro ⟨x, hx, he⟩
      change a • areaCellRepresentative h hε (S.mult ε ω)
        (euclideanCellEquiv h hε i) ∈ Complex.orthonormalBasisOneI.repr.symm ⁻¹' U
      rw [he]
      exact (hAB x).mp hx
    · intro hi
      change a • areaCellRepresentative h hε (S.mult ε ω)
        (euclideanCellEquiv h hε i) ∈ Complex.orthonormalBasisOneI.repr.symm ⁻¹' U at hi
      let x : R := ⟨euclideanCellEquiv h hε i, hcontain _ hi⟩
      exact ⟨x, (hAB x).mpr hi, rfl⟩
  exact areaCell_finite_unrestricted_sourceContinuousExitCurve_law
    S ω h hε hlf R A hretain hpos v hm a hU hactive

end MatedCRT
end
