import MatedCRT.FirstPass.Derived.AreaCellSourceContinuousCurveLaw
import MatedCRT.FirstPass.Derived.AreaCellStoppedLaw

/-! # Continuous exit curves of absorbed area-cell walks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory _root_.HarmonicBalls LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open BouRabeeGwynne.FiniteConductanceNetwork

/-- The finite cell walk has the continuous exit-curve law of the integer walk
absorbed on leaving the active vertices. -/
theorem areaCell_finite_sourceContinuousExitCurve_law
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
    (v : R) {m : ℝ} (hm : 0 ≤ m) (a : ℝ) {U : Set ℂ} (hU : IsOpen U) :
    let e := euclideanCellEquiv h hε
    let D : Set ℤ := {i | ∃ x ∈ A, e i = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
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
    ((srwLaw (S.mult ε ω) (e.symm v.1)).map (stoppedPath D)).map
      (fun x => CurveSpaceComparison.isometryEquiv 2
        (normalizedPrefixCurve
          (complexToEuclideanPath (a • interpPathCM (vertexPoint ε (S.η ω)) hm x))
          (pathExitTime U (a • interpPathCM (vertexPoint ε (S.η ω)) hm x)).toNNReal)) := by
  classical
  let _ : Countable (areaCellConfig h hε (S.mult ε ω)).cells :=
    Countable.of_equiv ℤ (euclideanCellEquiv h hε)
  dsimp only
  rw [areaCell_sourceContinuousExitCurve_law h hε (S.mult ε ω) hm a hU]
  have hrel :
      (((LatticeProb.finiteConductanceRestriction
        (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
          (areaCellConfig h hε (S.mult ε ω)).c v w)
        (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
        (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
        (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).trajectoryLaw A hpos v).map
          (fun p n => (p n : (areaCellConfig h hε (S.mult ε ω)).cells))).map
            (fun y n => (euclideanCellEquiv h hε).symm (y n)) =
      (srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1)).map
        (stoppedPath {i | ∃ x ∈ A, euclideanCellEquiv h hε i =
          (x : (areaCellConfig h hε (S.mult ε ω)).cells)}) := by
    have hf : Measurable (fun p : ℕ → R => fun n =>
        (p n : (areaCellConfig h hε (S.mult ε ω)).cells)) := by
      apply Measurable.of_eval
      intro n
      exact (measurable_of_finite (fun x : R =>
        (x : (areaCellConfig h hε (S.mult ε ω)).cells))).comp (measurable_pi_apply n)
    let e : ℤ ≃ (areaCellConfig h hε (S.mult ε ω)).cells := euclideanCellEquiv h hε
    have hg : Measurable (fun y : ℕ → (areaCellConfig h hε (S.mult ε ω)).cells =>
        fun n => (euclideanCellEquiv h hε).symm (y n)) := by
      apply Measurable.of_eval
      intro n
      exact (measurable_of_countable e.symm).comp (measurable_pi_apply n)
    rw [Measure.map_map hg hf]
    exact areaCellConfig_finiteRestriction_stopped_trajectoryLaw_map S ω h hε hlf R A hretain hpos v
  rw [hrel]

end MatedCRT
end
