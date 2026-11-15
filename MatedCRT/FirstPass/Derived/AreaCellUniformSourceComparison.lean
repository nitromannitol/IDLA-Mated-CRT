import MatedCRT.FirstPass.Derived.AreaCellContainedSourceComparison
import MatedCRT.FirstPass.Derived.AreaCellFiniteNetworkPreparation

/-! # Source comparison for every start on a bounded area-cell network -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set MeasureTheory _root_.HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 MatedCRTHarmonic.Markov LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- One finite network supports the conditional continuous exit-curve comparison
for every active starting cell in a bounded domain. -/
theorem MatedCRTEnv.exists_areaCell_finite_all_sourceContinuousExitCurve_le
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {δ : ℝ} (hδ : 0 < δ) (hlf : IsLocallyFiniteMult (S.mult δ ω))
    (hlfg : MatedCRTHarmonic.MatedCRT.IsLocallyFinite δ (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph δ (S.bm ω) hlfg) (0 : ℤ))
    (hH : H.cell = cell δ (S.η ω))
    (hc : (areaCellConfig h hδ (S.mult δ ω)).IsCellConfiguration)
    (hpos : ∀ K, 0 < (areaCellConfig h hδ (S.mult δ ω)).holding K)
    {a m : ℝ≥0} (ha : 0 < a) (hm : 0 < m)
    {Uc : Set ℂ} (hU : IsOpen Uc) (hUb : Bornology.IsBounded Uc)
    (hconv : Convex ℝ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) :
    ∃ (R : Set (areaCellConfig h hδ (S.mult δ ω)).cells) (hR : R.Finite),
      (∀ v, (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) v ∈
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) → v ∈ R) ∧
      (∀ v, (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) v ∈
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) → ∀ w, w ∉ R →
        (areaCellConfig h hδ (S.mult δ ω)).c v w = 0) ∧
      (∀ v : (areaCellConfig h hδ (S.mult δ ω)).cells, ∃ w,
        (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) w ∉
          (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) ∧
        Relation.ReflTransGen
          (fun x y : (areaCellConfig h hδ (S.mult δ ω)).cells =>
            0 < (areaCellConfig h hδ (S.mult δ ω)).c x y) v w) ∧
      letI := hR.fintype
      let A : Set R := {v | (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) v ∈
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)}
      ∃ hactive : ∀ v ∈ A, 0 < (finiteConductanceRestriction
        (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells =>
          (areaCellConfig h hδ (S.mult δ ω)).c v w)
        (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R).totalConductance v,
      ∀ (start : R) (_hstart : start ∈ A)
    (W : Set Plane) (d : ℝ) (_hd : 0 ≤ d)
    (_hbuffer : ∀ x ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc), Metric.closedBall x ((a : ℝ) * d) ⊆ W)
    (_hmesh : ∀ K : (areaCellConfig h hδ (S.mult δ ω)).cells, (∃ z ∈ (K.1 : Set Plane), (a : ℝ) • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ d)
    (q : R → Plane) (z : Plane) (μ : Measure (BouRabeeGwynne.BrownianPath 2))
    (D : ℝ) (r s : ℝ≥0)
    (_hdist : ∀ x : R, dist ((a : ℝ) • (areaCellRepresentative h hδ (S.mult δ ω)) x) (q x) ≤ D) (_hdr : D < (r : ℝ))
    (n : ℕ)
    (_hbound : ((finiteConductanceRestriction
      (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells => (areaCellConfig h hδ (S.mult δ ω)).c v w) (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R).trajectoryLaw A hactive start)
        {ω | (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime (q ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) ω} +
      ∑ k ∈ Finset.range n, ((finiteConductanceRestriction
        (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells => (areaCellConfig h hδ (S.mult δ ω)).c v w) (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R).trajectoryLaw A hactive start)
        {ω | q (ω k) ∈ Metric.thickening (r : ℝ) (frontier (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))} ≤ (r : ℝ≥0∞))
    (_hsource : levyProkhorovEDist
      (((finiteConductanceRestriction
        (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells => (areaCellConfig h hδ (S.mult δ ω)).c v w) (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R).trajectoryLaw A hactive start).map
        (stoppedPolygonalCurve q (q ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)))) (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) z μ) ≤ (s : ℝ≥0∞))
    , levyProkhorovEDist
      ((srwLaw (S.mult δ ω) ((euclideanCellEquiv h hδ).symm start.1)).map
        (fun x => CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath ((a : ℝ) • interpPathCM (vertexPoint δ (S.η ω)) hm.le x))
            (pathExitTime Uc ((a : ℝ) • interpPathCM (vertexPoint δ (S.η ω)) hm.le x)).toNNReal)))
      (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) z μ) ≤
      ENNReal.ofReal (4 * ((a : ℝ) * d)) + ((r + s : ℝ≥0) : ℝ≥0∞) := by
  classical
  have hbounded : Bornology.IsBounded (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) :=
    Complex.orthonormalBasisOneI.repr.symm.isometry.antilipschitzWith.isBounded_preimage hUb
  obtain ⟨R, hR, hs, hcontain, hretain, hactive, hpaths⟩ :=
    S.exists_areaCell_finite_network_for_bounded_domain ω h hδ hlf hlfg H hH ha hbounded (euclideanCellEquiv h hδ 0)
  refine ⟨R, hR, hcontain, hretain, hpaths, ?_⟩
  let : Fintype R := hR.fintype
  refine ⟨hactive, ?_⟩
  intro start hstart W d hd hbuffer hmesh q z μ D r s hdist hdr n hbound hsource
  exact areaCell_contained_sourceContinuousExitCurve_le S ω h hδ hlf hc hpos ha hm
    hU hconv R _ (fun _ => Iff.rfl) hactive
    (fun v hv w hw => hretain v hv w hw) (fun v _ => hpaths v)
    start hstart W d hd hbuffer hmesh q z μ D r s hdist hdr n hbound hsource hcontain

end MatedCRT
end
