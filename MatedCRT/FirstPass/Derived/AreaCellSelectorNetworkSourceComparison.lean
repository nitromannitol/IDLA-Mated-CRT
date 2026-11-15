import MatedCRT.FirstPass.Derived.AreaCellSelectorNetworkUnitMesh
import MatedCRT.FirstPass.Derived.AreaCellContainedUnitBallSourceComparison

/-! # Selector networks and continuous exit-curve comparison -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set _root_.HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 MatedCRTHarmonic.Markov LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- The selector network also supports the target continuous-exit comparison. -/
theorem MatedCRTEnv.exists_areaCell_selector_network_source_comparison
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hc : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (hpos : ∀ K, 0 < (areaCellConfig h hε (S.mult ε ω)).holding K)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hlfg : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlfg) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    {a : ℝ≥0} (ha : 0 < a) {W : Set Plane} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (centers : Finset Plane) (s : ℝ)
    (hballs : ∀ c ∈ centers, closedBall c s ⊆ W)
    (start : (areaCellConfig h hε (S.mult ε ω)).cells) {t : ℝ} (ht : 0 < t)
    (Uc : Set ℂ) (hUopen : IsOpen Uc)
    (hconv : Convex ℝ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    {m : ℝ≥0} (hm : 0 < m) (r d : ℝ) (hd : 0 ≤ d)
    (hUW : Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc ⊆ W)
    (hU : Uc ⊆ ball 0 r) (hmargin : r + (a : ℝ) * d ≤ a)
    (hdiam : ∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
      diam (cell ε (S.η ω) k) ≤ d) :
    ∃ (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) (hR : R.Finite),
    start ∈ R ∧
    (∀ v, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ W → v ∈ R) ∧
    (∀ v, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ W →
      ∀ w, w ∉ R → (areaCellConfig h hε (S.mult ε ω)).c v w = 0) ∧
    (∀ v : (areaCellConfig h hε (S.mult ε ω)).cells,
      ∃ w, (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) w ∉
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) ∧
        Relation.ReflTransGen
          (fun x y : (areaCellConfig h hε (S.mult ε ω)).cells =>
            0 < (areaCellConfig h hε (S.mult ε ω)).c x y) v w) ∧
    (letI := hR.fintype
     let N := finiteConductanceRestriction
       (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
         (areaCellConfig h hε (S.mult ε ω)).c v w)
       (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
       (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
       (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
     let p : R → Plane := fun v => (a : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v
     let A := p ⁻¹' W
     ∃ (hA : ∀ v ∈ A, 0 < N.totalConductance v) (q : R → Plane),
       N.BoundaryAccessible A ∧ Function.Injective q ∧
       (∀ v, ∃ x ∈ (v.1.1 : Set Plane), q v = (a : ℝ) • x) ∧
       (∀ v, dist (p v) (q v) < t) ∧
       (∀ j : centers, q ⁻¹' ball j.val s ⊆ A) ∧
       (p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) ⊆ A) ∧
       (∀ j : centers, ∀ v ∈ q ⁻¹' ball j.val s, 0 < N.totalConductance v) ∧
       (∀ v ∈ p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc),
         0 < N.totalConductance v) ∧
       (∀ [MeasurableSpace R] [MeasurableSingletonClass R] (v : R),
         ∀ᵐ ξ ∂N.trajectoryLaw A hA v, ∀ j : ℕ,
           (j : WithTop ℕ) < FiniteConductanceNetwork.exitTime
             (p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) ξ →
           dist (p (ξ (j + 1))) (p (ξ j)) ≤ 2 * ((a : ℝ) * d)) ∧
       (∀ [MeasurableSpace R] [MeasurableSingletonClass R]
         (v : R) (_hv : v ∈ p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
         (ν : Measure (BouRabeeGwynne.CurveSpace 2)) (s₀ : ℝ≥0)
         (_hsource : levyProkhorovEDist
           ((N.trajectoryLaw (p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
             (fun v hv => hA v (hUW hv)) v).map
             (stoppedPolygonalCurve p (p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))))
           ν ≤ (s₀ : ℝ≥0∞)),
         levyProkhorovEDist
           ((srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1)).map
             (fun x => CurveSpaceComparison.isometryEquiv 2
               (normalizedPrefixCurve
                 (complexToEuclideanPath ((a : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm.le x))
                 (pathExitTime Uc ((a : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm.le x)).toNNReal)))
           ν ≤ ENNReal.ofReal (4 * ((a : ℝ) * d)) + (s₀ : ℝ≥0∞))) := by
  classical
  obtain ⟨R, hR, hs, hcontain, hretain, hpaths, hA, q, haccess, hqinj, hqcell,
    hqnear, hsel, hsub, hBpos, hUpos, hstep⟩ :=
    S.exists_areaCell_selector_network_unit_mesh ω h hε hc hlf hlfg H hH ha hW hWb
      centers s hballs start ht Uc r d hd hUW hU hmargin hdiam
  let : Fintype R := hR.fintype
  refine ⟨R, hR, hs, hcontain, hretain, hpaths, hA, q, haccess, hqinj, hqcell,
    hqnear, hsel, hsub, hBpos, hUpos, hstep, ?_⟩
  intro _ _ v hv ν s₀ hsource
  exact areaCell_contained_unitBall_sourceContinuousExitCurve_le S ω h hε hlf hc
    hpos ha hm hUopen hconv R _ (fun _ => Iff.rfl) _
    (fun x hx w hw => hretain x (hUW hx) w hw) (fun x _ => hpaths x)
    v hv r d hd hU hmargin hdiam ν s₀ hsource
    (fun x hx => hcontain x (hUW hx))

end MatedCRT
end
