import MatedCRT.FirstPass.Derived.AreaCellPaperSourceEndpoint
import LatticeProb.Prob.WalkSourcePrefixLaw

/-! # Exit positions of area-cell and paper walks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set HarmonicBalls LatticeProb BouRabeeGwynne
open ReflectedGMS ReflectedGMS.GMS
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open LatticeProb.CellConfigWalk
open scoped NNReal ENNReal

/-- The exit-position law of the holding-time cell walk agrees with the paper's
constant-step walk, provided the holding-time exit is almost surely finite. -/
theorem areaCell_holding_exitPosition_law
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℤ → ℕ)
    (hrec : (areaCellConfig h hε c).Recurrent)
    (hpos : ∀ K, 0 < (areaCellConfig h hε c).holding K)
    (x : ℤ) (Q : Measure (ℕ → ℤ))
    (hQ : (areaCellConfig h hε c).IsSRWLaw (euclideanCellEquiv h hε x)
      (Q.map (fun ξ n => euclideanCellEquiv h hε (ξ n))))
    {σ m : ℝ≥0} (hσ : 0 < σ) (hm : 0 < m)
    {U : Set ℂ} (hU : IsOpen U)
    (hfinite : ∀ᵐ ξ ∂(Q.map (fun ξ n => euclideanCellEquiv h hε (ξ n))),
      LatticeProb.continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
        ((areaCellConfig h hε c).interpolatedWalk (areaCellRepresentative h hε c) σ ξ) ≠ ∞) :
    ((Q.map (fun ξ n => euclideanCellEquiv h hε (ξ n))).map (fun ξ =>
      ((areaCellConfig h hε c).interpolatedWalk (areaCellRepresentative h hε c) σ ξ)
        (LatticeProb.continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' U) 0
          ((areaCellConfig h hε c).interpolatedWalk (areaCellRepresentative h hε c) σ ξ)).toNNReal)).map
      Complex.orthonormalBasisOneI.repr.symm =
    Q.map (fun ξ => ((σ : ℝ) • interpPathCM (vertexPoint ε η) hm.le ξ)
      (pathExitTime U ((σ : ℝ) • interpPathCM (vertexPoint ε η) hm.le ξ)).toNNReal) := by
  let C := areaCellConfig h hε c
  let e := euclideanCellEquiv h hε
  let P := Q.map (fun ξ n => e (ξ n))
  let p := areaCellRepresentative h hε c
  let V := Complex.orthonormalBasisOneI.repr.symm ⁻¹' U
  let _ : Countable C.cells := Countable.of_equiv ℤ e
  have hV : IsOpen V := hU.preimage Complex.orthonormalBasisOneI.repr.symm.continuous
  have hprefix := map_walkExitPathClockLaw_sourcePrefix_eq_constantStep
    hrec hpos hQ p hσ hm hV hfinite
  have heval : Measurable (fun q : C(ℝ≥0, Plane) × ℝ≥0∞ => q.1 q.2.toNNReal) := by
    simpa only [normalizedPrefixCurve_endPoint, Function.comp_def] using
      LatticeProb.CurveSpace.continuous_endPoint.measurable.comp
        measurable_normalizedPrefixCurve_toNNReal
  have hleft : ((walkExitPathClockLaw C p σ V P).map
      (fun q => CurveSpaceComparison.isometryEquiv 2 (normalizedPrefixCurve q.1 q.2.toNNReal))).map
      (fun q => Complex.orthonormalBasisOneI.repr.symm (BouRabeeGwynne.CurveSpace.endPoint q)) =
      (P.map (fun ξ => (C.interpolatedWalk p σ ξ)
        (LatticeProb.continuousExitTime V 0 (C.interpolatedWalk p σ ξ)).toNNReal)).map
        Complex.orthonormalBasisOneI.repr.symm := by
    have hc : Measurable (fun q : C(ℝ≥0, Plane) × ℝ≥0∞ =>
        CurveSpaceComparison.isometryEquiv 2 (normalizedPrefixCurve q.1 q.2.toNNReal)) :=
      (CurveSpaceComparison.isometryEquiv 2).continuous.measurable.comp
        measurable_normalizedPrefixCurve_toNNReal
    change ((walkExitPathClockLaw C p σ V P).map
      (fun q => CurveSpaceComparison.isometryEquiv 2 (normalizedPrefixCurve q.1 q.2.toNNReal))).map
      (Complex.orthonormalBasisOneI.repr.symm ∘ BouRabeeGwynne.CurveSpace.endPoint) = _
    rw [Measure.map_map (Complex.orthonormalBasisOneI.repr.symm.continuous.measurable.comp
      BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable) hc]
    have hfun : ((Complex.orthonormalBasisOneI.repr.symm ∘ BouRabeeGwynne.CurveSpace.endPoint) ∘
        (fun q : C(ℝ≥0, Plane) × ℝ≥0∞ =>
          CurveSpaceComparison.isometryEquiv 2 (normalizedPrefixCurve q.1 q.2.toNNReal))) =
        (Complex.orthonormalBasisOneI.repr.symm ∘ fun q : C(ℝ≥0, Plane) × ℝ≥0∞ =>
          q.1 q.2.toNNReal) := by
      funext q
      change Complex.orthonormalBasisOneI.repr.symm
        (LatticeProb.CurveSpace.endPoint (normalizedPrefixCurve q.1 q.2.toNNReal)) = _
      simp only [Function.comp_apply, normalizedPrefixCurve_endPoint]
    rw [hfun]
    rw [← Measure.map_map Complex.orthonormalBasisOneI.repr.symm.continuous.measurable heval]
    congr 1
    exact map_walkExitPathClockLaw_endpoint (H := C) (Q := P) hrec hpos hQ p σ hV
  have hright := areaCell_relabelled_sourceCurve_endpoint_law h hε c hm.le (σ : ℝ) hU Q
  exact hleft.symm.trans ((congrArg (fun M => M.map (fun q =>
    Complex.orthonormalBasisOneI.repr.symm (BouRabeeGwynne.CurveSpace.endPoint q))) hprefix).trans hright)

end MatedCRT
end
