import MatedCRT.FirstPass.Derived.AreaCellRepresentativeSourceComparison
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteProbability

/-! # Area-cell stopped curve comparison with Brownian motion -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set MeasureTheory _root_.HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- A representative excursion comparison and Brownian clock-tail estimate
control the actual continuously stopped walk law. -/
theorem areaCell_representative_sourceContinuousExitCurve_brownian_le
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
    {J : Type*} [Countable J] [MeasurableSpace (Option J)]
    [MeasurableSingletonClass (Option J)]
    (μ : Measure (BouRabeeGwynne.BrownianPath 2)) (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ)
    (Wb : J → Set (BouRabeeGwynne.Euc 2)) (hWb : ∀ j, IsOpen (Wb j))
    (hWbounded : ∀ j, Bornology.IsBounded (Wb j)) (z : BouRabeeGwynne.Euc 2) (j₀ : J)
    (selector : ℕ → BouRabeeGwynne.Euc 2 → Option J) (hselector : ∀ n, Measurable (selector n))
    (hnone : ∀ n x, selector n x = none →
      x ∉ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    (n : ℕ) (P : TimePartition n) (r : ℝ≥0) (hr : 0 < r)
    (hbad : μ {ω | (brownianSkeletonClock Wb z j₀ selector n ω).1 = false} ≤ (r : ℝ≥0∞))
    (s : ℝ≥0)
    (hsource : levyProkhorovEDist
      (((finiteConductanceRestriction
        (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells => (areaCellConfig h hδ (S.mult δ ω)).c v w) (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R).trajectoryLaw A hA v).map
        (stoppedPolygonalCurve
          (fun x : R => (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) x)
          {x : R | (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) x ∈
            (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)})) (((μ.map (fun ω k => brownianSkeletonExcursion Wb z j₀ selector k ω)).map
            (pastedBrownianCurve P)).map
              (unitCurveExitProjection (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))) ≤ (s : ℝ≥0∞))
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
      (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) z μ) ≤
      ENNReal.ofReal (4 * ((a : ℝ) * d)) + (s : ℝ≥0∞) + (r : ℝ≥0∞) := by
  classical
  let U := Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc
  have hU' : IsOpen U := hU.preimage Complex.orthonormalBasisOneI.repr.symm.continuous
  let ν := ((μ.map (fun ω k => brownianSkeletonExcursion Wb z j₀ selector k ω)).map
    (pastedBrownianCurve P)).map (unitCurveExitProjection U)
  have hleft := areaCell_representative_sourceContinuousExitCurve_le S ω h hδ hlf hc
    hpos ha hm hU hconv R A hAB hA hretain hpaths v hv W d hd hbuffer hmesh ν s hsource hactive
  have hmap : ν = (μ.map (fun ω k => brownianSkeletonExcursion Wb z j₀ selector k ω)).map
      (reconstructedBrownianStoppedCurve U P) := by
    dsimp only [ν]
    rw [Measure.map_map (measurable_unitCurveExitProjection hU') (measurable_pastedBrownianCurve P)]
    rfl
  have hright : levyProkhorovEDist ν (stoppedBrownianLaw U z μ) ≤ (r : ℝ≥0∞) := by
    rw [levyProkhorovEDist_comm, hmap]
    exact levyProkhorov_stoppedBrownian_reconstruction_le (by decide) hμ Wb hWb hWbounded z j₀
      selector hselector hU' hnone n P r hr hbad
  exact (levyProkhorovEDist_triangle _ ν _).trans (add_le_add hleft hright)

end MatedCRT
end
