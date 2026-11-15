import MatedCRT.FirstPass.Derived.AreaCellContainedSourceComparison
import MatedCRT.FirstPass.Derived.AreaCellUnitBallBufferedMesh

/-! # Unit-ball mesh for contained area-cell source comparison -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set MeasureTheory _root_.HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- A unit-ball diameter bound and domain margin supply the local mesh for
the contained finite-network source comparison. -/
theorem areaCell_unitBall_contained_sourceContinuousExitCurve_le
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
    (r₀ d : ℝ) (hd : 0 ≤ d)
    (hUr : Uc ⊆ Metric.ball 0 r₀) (hmargin : r₀ + (a : ℝ) * d ≤ a)
    (hdiam : ∀ k, (cell δ (S.η ω) k ∩ Metric.ball 0 1).Nonempty →
      Metric.diam (cell δ (S.η ω) k) ≤ d)
    (q : R → Plane) (z : Plane) (μ : Measure (BouRabeeGwynne.BrownianPath 2))
    (D : ℝ) (r s : ℝ≥0)
    (hdist : ∀ x : R, dist ((a : ℝ) • (areaCellRepresentative h hδ (S.mult δ ω)) x) (q x) ≤ D) (hdr : D < (r : ℝ))
    (n : ℕ)
    (hbound : ((finiteConductanceRestriction
      (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells => (areaCellConfig h hδ (S.mult δ ω)).c v w) (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R).trajectoryLaw A hA v)
        {ω | (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime (q ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) ω} +
      ∑ k ∈ Finset.range n, ((finiteConductanceRestriction
        (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells => (areaCellConfig h hδ (S.mult δ ω)).c v w) (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R).trajectoryLaw A hA v)
        {ω | q (ω k) ∈ Metric.thickening (r : ℝ) (frontier (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))} ≤ (r : ℝ≥0∞))
    (hsource : levyProkhorovEDist
      (((finiteConductanceRestriction
        (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells => (areaCellConfig h hδ (S.mult δ ω)).c v w) (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R).trajectoryLaw A hA v).map
        (stoppedPolygonalCurve q (q ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)))) (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) z μ) ≤ (s : ℝ≥0∞))
    (hcontain : ∀ K : (areaCellConfig h hδ (S.mult δ ω)).cells,
      (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) K ∈
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) → K ∈ R) :
    levyProkhorovEDist
      ((srwLaw (S.mult δ ω) ((euclideanCellEquiv h hδ).symm v.1)).map
        (fun x => CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath ((a : ℝ) • interpPathCM (vertexPoint δ (S.η ω)) hm.le x))
            (pathExitTime Uc ((a : ℝ) • interpPathCM (vertexPoint δ (S.η ω)) hm.le x)).toNNReal)))
      (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) z μ) ≤
      ENNReal.ofReal (4 * ((a : ℝ) * d)) + ((r + s : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨hbuffer, hmesh⟩ := areaCellConfig_unit_ball_buffer_and_scaled_local_mesh
    h hδ (S.mult δ ω) (show 0 < (a : ℝ) from ha) Uc r₀ d hUr hmargin hdiam
  exact areaCell_contained_sourceContinuousExitCurve_le S ω h hδ hlf hc hpos ha hm
    hU hconv R A hAB hA hretain hpaths v hv (Metric.ball 0 (a : ℝ)) d hd hbuffer
    hmesh q z μ D r s hdist hdr n hbound hsource hcontain

end MatedCRT
end
