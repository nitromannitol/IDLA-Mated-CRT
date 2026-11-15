import MatedCRT.FirstPass.Derived.AreaCellActualStoppedSourceComparison
import LatticeProb.Walk.RestrictedBoundaryAccessibility

/-! # Actual stopped-law comparison from ambient paths -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory _root_.HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- Ambient paths and retention of active neighbors supply boundary accessibility
in the actual stopped-law comparison. -/
theorem areaCell_contained_actualStoppedSource_le_of_ambient_paths
    {J : Type*} [Countable J] [MeasurableSpace (Option J)]
    [MeasurableSingletonClass (Option J)]
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ₀ : Measure ℂ} (h : IsAreaParametrized μ₀ (S.η ω))
    {δ : ℝ} (hδ : 0 < δ) (hlf : IsLocallyFiniteMult (S.mult δ ω))
    (hc : (areaCellConfig h hδ (S.mult δ ω)).IsCellConfiguration)

    (hpos : ∀ K, 0 < (areaCellConfig h hδ (S.mult δ ω)).holding K) {a m : ℝ≥0} (ha : 0 < a) (hm : 0 < m)
    {Uc : Set ℂ} (hU : IsOpen Uc) (hconv : Convex ℝ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    (R : Set (areaCellConfig h hδ (S.mult δ ω)).cells) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (N : FiniteConductanceNetwork R) (hN : N = (finiteConductanceRestriction
      (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells => (areaCellConfig h hδ (S.mult δ ω)).c v w) (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R))
    (A : Set R)
    (hAB : ∀ v : R, v ∈ A ↔ (a : ℝ) • (areaCellRepresentative h hδ (S.mult δ ω)) v ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R → (areaCellConfig h hδ (S.mult δ ω)).c v w = 0)
    (hpaths : ∀ v ∈ A, ∃ w : (areaCellConfig h hδ (S.mult δ ω)).cells, (a : ℝ) • (areaCellRepresentative h hδ (S.mult δ ω)) w ∉ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) ∧
      Relation.ReflTransGen (fun x y : (areaCellConfig h hδ (S.mult δ ω)).cells => 0 < (areaCellConfig h hδ (S.mult δ ω)).c x y) (v : (areaCellConfig h hδ (S.mult δ ω)).cells) w)
    (v : R) (hv : v ∈ A)
    (W : Set Plane) (d : ℝ) (hd : 0 ≤ d)
    (hbuffer : ∀ x ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc), Metric.closedBall x ((a : ℝ) * d) ⊆ W)
    (hmesh : ∀ K : (areaCellConfig h hδ (S.mult δ ω)).cells, (∃ z ∈ (K.1 : Set Plane), (a : ℝ) • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ d)
    (q : R → Plane) (z : Plane) (μ : Measure (BouRabeeGwynne.BrownianPath 2))
    (D : ℝ) (r s : ℝ≥0)
    (hdist : ∀ x : R, dist ((a : ℝ) • (areaCellRepresentative h hδ (S.mult δ ω)) x) (q x) ≤ D) (hdr : D < (r : ℝ))
    (n : ℕ)
    (hbound : (N.trajectoryLaw A hA v)
        {ω | (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime (q ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) ω} +
      ∑ k ∈ Finset.range n, (N.trajectoryLaw A hA v)
        {ω | q (ω k) ∈ Metric.thickening (r : ℝ) (frontier (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))} ≤ (r : ℝ≥0∞))
    (hinj : Function.Injective q)
    (B : J → Set R) (hB : ∀ j x, x ∈ B j → 0 < N.totalConductance x)
    (Wj : J → Set Plane) (hW : ∀ j, IsOpen (Wj j))
    (hWb : ∀ j, Bornology.IsBounded (Wj j))
    [IsProbabilityMeasure μ] (hμ : BouRabeeGwynne.IsStandardBrownianLaw μ)
    (select : ℕ → Plane → Option J) (hs : ∀ i, Measurable (select i))
    (parts : ℕ → ℕ) (E : ∀ i, Fin (parts i) → Set Plane)
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    (hBA : ∀ j, B j ⊆ A)
    (initial : J) (n₀ : ℕ) (P : TimePartition n₀)
    (a₀ R₀ S₀ eps mesh delta eta : ℝ)
    (heps : 0 < eps) (hmesh₀ : 0 ≤ mesh) (hbuffer₀ : eps + mesh < delta)
    (hnone : ∀ i x, select i x = none → x ∉ Metric.thickening delta
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    (hdiam : ∀ i ≤ n₀, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a₀)
    (hnear : dist (q v) z ≤ a₀) (hpoint : R₀ + a₀ + S₀ ≤ eps)
    (hsteps : ∀ᵐ x ∂N.trajectoryLaw A hA v, ∀ k, dist (q (x k)) (q (x (k + 1))) ≤ mesh)
    (hwrange : ∀ᵐ x ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (actualWalkExcursionSequence q B initial select x i).2 ∈
        curveOscillationLe R₀)
    (hbrange : ∀ᵐ x ∂μ, ∀ i,
      (brownianSkeletonExcursion Wj z initial (brownianSelectorForWalk select) i x).2 ∈
        curveOscillationLe S₀)
    {b c o : ℝ≥0∞}
    (hfailure : N.walkBrownianJointLaw q hinj B hB Wj hW μ select hs parts E hE hdE initial v z
      {p | ∃ i ≤ n₀, (p.1 i, p.2 i) ∉ goodExcursionPair q (E i) a₀} ≤ b)
    (htail : μ {x | (brownianSkeletonExcursion Wj z initial
      (brownianSelectorForWalk select) n₀ x).1 = false} ≤ c)
    (hosc : μ {x | P.concatenate (ExcursionTrajectory.prefixChain n₀ 2
      (fun k => (brownianSkeletonExcursion Wj z initial
        (brownianSelectorForWalk select) k x).2)) ∈
      unitCurveExitOscillationBad (innerDomain (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) eps)
        (Metric.thickening delta (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) eta} ≤ o)
    (rWalk rMiddle rBrownian : ℝ≥0) (hrWalk : 0 < rWalk) (hrBrownian : 0 < rBrownian)
    (hwalkBudget : b + c ≤ (rWalk : ℝ≥0∞))
    (hbrownianBudget : c ≤ (rBrownian : ℝ≥0∞))
    (hmiddleBudget : b + c + o ≤ (rMiddle : ℝ≥0∞))
    (hsmall : ENNReal.ofReal (eps + eta) < (rMiddle : ℝ≥0∞))
    (hbudget : rWalk + rMiddle + rBrownian ≤ s)
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
  have haccess : N.BoundaryAccessible A := by
    rw [hN]
    exact finiteConductanceRestriction_boundaryAccessible_of_ambient_paths
      (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells =>
        (areaCellConfig h hδ (S.mult δ ω)).c v w)
      (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
      (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
      (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω))
      R A {K | (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) K ∈
        Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc} hAB hretain hpaths
  exact areaCell_contained_actualStoppedSource_le S ω h hδ hlf hc hpos ha hm
    hU hconv R N hN A hAB hA hretain hpaths v hv W d hd hbuffer hmesh
    q z μ D r s hdist hdr n hbound hinj B hB Wj hW hWb hμ select hs parts E hE hdE
    hBA haccess initial n₀ P a₀ R₀ S₀ eps mesh delta eta heps hmesh₀ hbuffer₀
    hnone hdiam hnear hpoint hsteps hwrange hbrange hfailure htail hosc
    rWalk rMiddle rBrownian hrWalk hrBrownian hwalkBudget hbrownianBudget
    hmiddleBudget hsmall hbudget hcontain

end MatedCRT
end
