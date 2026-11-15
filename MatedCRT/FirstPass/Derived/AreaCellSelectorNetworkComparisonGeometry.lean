import MatedCRT.FirstPass.Derived.AreaCellSelectorNetworkBrownianBudget
import MatedCRT.FirstPass.Derived.AreaCellRestrictionNetworkGeometry

/-! # Selector network comparison and finite restriction geometry -/

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

/-- One finite selector network has the unit-ball geometry needed for the
stopped-curve comparison, and transfers its Brownian error bound. -/
theorem MatedCRTEnv.exists_areaCell_selector_network_comparison_geometry
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
       (∀ K, areaCellRepresentative h hε (S.mult ε ω) K ∈ (K.1 : Set Plane)) ∧
       (∀ v w : R, 0 < N.a v w →
         (areaCellConfig h hε (S.mult ε ω)).Adj v.1 w.1) ∧
       (∀ x ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc),
         closedBall x ((a : ℝ) * d) ⊆ ball 0 (a : ℝ)) ∧
       (∀ K : (areaCellConfig h hε (S.mult ε ω)).cells,
         (∃ z ∈ (K.1 : Set Plane), (a : ℝ) • z ∈ ball 0 (a : ℝ)) →
           diam (K.1 : Set Plane) ≤ d) ∧
       (∀ [MeasurableSpace R] [MeasurableSingletonClass R] (v : R),
         ∀ᵐ ξ ∂N.trajectoryLaw A hA v, ∀ j : ℕ,
           (j : WithTop ℕ) < FiniteConductanceNetwork.exitTime
             (p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) ξ →
           dist (p (ξ (j + 1))) (p (ξ j)) ≤ 2 * ((a : ℝ) * d)) ∧
       (∀ [MeasurableSpace R] [MeasurableSingletonClass R]
         (v : R) (_hv : v ∈ p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
         (ν : Measure (BouRabeeGwynne.CurveSpace 2)) (s₀ : ℝ≥0) (τ : ℝ)
         (_hsource : levyProkhorovEDist
           ((N.trajectoryLaw (p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
             (fun v hv => hA v (hUW hv)) v).map
             (stoppedPolygonalCurve p (p ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))))
           ν ≤ (s₀ : ℝ≥0∞) + ENNReal.ofReal τ),
         levyProkhorovEDist
           ((srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1)).map
             (fun x => CurveSpaceComparison.isometryEquiv 2
               (normalizedPrefixCurve
                 (complexToEuclideanPath ((a : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm.le x))
                 (pathExitTime Uc ((a : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm.le x)).toNNReal)))
           ν ≤ ENNReal.ofReal (4 * ((a : ℝ) * d)) +
             ((s₀ : ℝ≥0∞) + ENNReal.ofReal τ))) := by
  classical
  obtain ⟨R, hR, hs, hcontain, hretain, hpaths, hA, q, haccess, hqinj, hqcell,
    hqnear, hsel, hsub, hBpos, hUpos, hstep, hcomparison⟩ :=
    S.exists_areaCell_selector_network_brownian_budget ω h hε hc hpos hlf hlfg H hH
      ha hW hWb centers s hballs start ht Uc hUopen hconv hm r d hd hUW hU hmargin hdiam
  let : Fintype R := hR.fintype
  obtain ⟨hrep, hedge, hbuffer, hmesh⟩ :=
    areaCellConfig_finiteRestriction_geometry S ω h hε R (show (0 : ℝ) < a by exact_mod_cast ha)
      Uc r d hU hmargin hdiam
  exact ⟨R, hR, hs, hcontain, hretain, hpaths, hA, q, haccess, hqinj, hqcell,
    hqnear, hsel, hsub, hBpos, hUpos, hrep, hedge, hbuffer, hmesh, hstep, hcomparison⟩

end MatedCRT
end
