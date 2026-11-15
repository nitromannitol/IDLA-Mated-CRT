import MatedCRT.FirstPass.Derived.AreaCellActualSourceAmbientPaths
import MatedCRT.FirstPass.Derived.AreaCellFiniteNetworkPreparation

/-! # Actual stopped-law comparison on a bounded area-cell network -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory _root_.HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 MatedCRTHarmonic.Markov LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal

/-- A bounded domain admits a finite network for the actual stopped-law comparison,
with the coupling and quantitative bounds supplied after the network is chosen. -/
theorem MatedCRTEnv.exists_areaCell_finite_actualStoppedSource_le
    {J : Type*} [Countable J] [MeasurableSpace (Option J)]
    [MeasurableSingletonClass (Option J)]
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
    (hconv : Convex ℝ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    (start : (areaCellConfig h hδ (S.mult δ ω)).cells)
    (hstart : (a : ℝ) • areaCellRepresentative h hδ (S.mult δ ω) start ∈
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) :
    ∃ (R : Set (areaCellConfig h hδ (S.mult δ ω)).cells) (hR : R.Finite)
      (hs : start ∈ R),
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
      let N : FiniteConductanceNetwork R := (finiteConductanceRestriction
        (fun v w : (areaCellConfig h hδ (S.mult δ ω)).cells =>
          (areaCellConfig h hδ (S.mult δ ω)).c v w)
        (areaCellConfig_conductance_symm h hδ (S.mult δ ω) (S.mult_symm δ ω))
        (areaCellConfig_conductance_nonneg h hδ (S.mult δ ω))
        (areaCellConfig_conductance_self h hδ (S.mult δ ω) (S.mult_self δ ω)) R)
      ∃ hactive : ∀ v ∈ A, 0 < N.totalConductance v,
      ∀
    (W : Set Plane) (d : ℝ) (_hd : 0 ≤ d)
    (_hbuffer : ∀ x ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc), Metric.closedBall x ((a : ℝ) * d) ⊆ W)
    (_hmesh : ∀ K : (areaCellConfig h hδ (S.mult δ ω)).cells, (∃ z ∈ (K.1 : Set Plane), (a : ℝ) • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ d)
    (q : R → Plane) (z : Plane) (μ : Measure (BouRabeeGwynne.BrownianPath 2))
    (D : ℝ) (r s : ℝ≥0)
    (_hdist : ∀ x : R, dist ((a : ℝ) • (areaCellRepresentative h hδ (S.mult δ ω)) x) (q x) ≤ D) (_hdr : D < (r : ℝ))
    (n : ℕ)
    (_hbound : (N.trajectoryLaw A hactive ⟨start, hs⟩)
        {ω | (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime (q ⁻¹' (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) ω} +
      ∑ k ∈ Finset.range n, (N.trajectoryLaw A hactive ⟨start, hs⟩)
        {ω | q (ω k) ∈ Metric.thickening (r : ℝ) (frontier (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))} ≤ (r : ℝ≥0∞))
    (hinj : Function.Injective q)
    (B : J → Set R) (hB : ∀ j x, x ∈ B j → 0 < N.totalConductance x)
    (Wj : J → Set Plane) (hW : ∀ j, IsOpen (Wj j))
    (_hWb : ∀ j, Bornology.IsBounded (Wj j))
    [IsProbabilityMeasure μ] (_hμ : BouRabeeGwynne.IsStandardBrownianLaw μ)
    (select : ℕ → Plane → Option J) (hselect : ∀ i, Measurable (select i))
    (parts : ℕ → ℕ) (E : ∀ i, Fin (parts i) → Set Plane)
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    (_hBA : ∀ j, B j ⊆ A)
    (initial : J) (n₀ : ℕ) (P : TimePartition n₀)
    (a₀ R₀ S₀ eps mesh delta eta : ℝ)
    (_heps : 0 < eps) (_hmesh₀ : 0 ≤ mesh) (_hbuffer₀ : eps + mesh < delta)
    (_hnone : ∀ i x, select i x = none → x ∉ Metric.thickening delta
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    (_hdiam : ∀ i ≤ n₀, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a₀)
    (_hnear : dist (q ⟨start, hs⟩) z ≤ a₀) (_hpoint : R₀ + a₀ + S₀ ≤ eps)
    (_hsteps : ∀ᵐ x ∂N.trajectoryLaw A hactive ⟨start, hs⟩, ∀ k, dist (q (x k)) (q (x (k + 1))) ≤ mesh)
    (_hwrange : ∀ᵐ x ∂N.trajectoryLaw A hactive ⟨start, hs⟩, ∀ i,
      ClockedWalkExcursion.curve (actualWalkExcursionSequence q B initial select x i).2 ∈
        curveOscillationLe R₀)
    (_hbrange : ∀ᵐ x ∂μ, ∀ i,
      (brownianSkeletonExcursion Wj z initial (brownianSelectorForWalk select) i x).2 ∈
        curveOscillationLe S₀)
    {b c o : ℝ≥0∞}
    (_hfailure : N.walkBrownianJointLaw q hinj B hB Wj hW μ select hselect parts E hE hdE initial ⟨start, hs⟩ z
      {p | ∃ i ≤ n₀, (p.1 i, p.2 i) ∉ goodExcursionPair q (E i) a₀} ≤ b)
    (_htail : μ {x | (brownianSkeletonExcursion Wj z initial
      (brownianSelectorForWalk select) n₀ x).1 = false} ≤ c)
    (_hosc : μ {x | P.concatenate (ExcursionTrajectory.prefixChain n₀ 2
      (fun k => (brownianSkeletonExcursion Wj z initial
        (brownianSelectorForWalk select) k x).2)) ∈
      unitCurveExitOscillationBad (innerDomain (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) eps)
        (Metric.thickening delta (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) eta} ≤ o)
    (rWalk rMiddle rBrownian : ℝ≥0) (_hrWalk : 0 < rWalk) (_hrBrownian : 0 < rBrownian)
    (_hwalkBudget : b + c ≤ (rWalk : ℝ≥0∞))
    (_hbrownianBudget : c ≤ (rBrownian : ℝ≥0∞))
    (_hmiddleBudget : b + c + o ≤ (rMiddle : ℝ≥0∞))
    (_hsmall : ENNReal.ofReal (eps + eta) < (rMiddle : ℝ≥0∞))
    (_hbudget : rWalk + rMiddle + rBrownian ≤ s)
    , levyProkhorovEDist
      ((srwLaw (S.mult δ ω) ((euclideanCellEquiv h hδ).symm start)).map
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
    S.exists_areaCell_finite_network_for_bounded_domain ω h hδ hlf hlfg H hH ha hbounded start
  refine ⟨R, hR, hs, hcontain, hretain, hpaths, ?_⟩
  let : Fintype R := hR.fintype
  refine ⟨hactive, ?_⟩
  intro W d hd hbuffer hmesh q z μ D r s hdist hdr n hbound hinj B hB Wj hW hWb
    hprob hμ select hselect parts E hE hdE hBA initial n₀ P a₀ R₀ S₀ eps mesh delta eta
    heps hmesh₀ hbuffer₀ hnone hdiam hnear hpoint hsteps hwrange hbrange b c o hfailure
    htail hosc rWalk rMiddle rBrownian hrWalk hrBrownian hwalkBudget hbrownianBudget
    hmiddleBudget hsmall hbudget
  exact areaCell_contained_actualStoppedSource_le_of_ambient_paths S ω h hδ hlf hc hpos ha hm
    hU hconv R _ rfl _ (fun _ => Iff.rfl) hactive
    (fun v hv w hw => hretain v hv w hw) (fun v _ => hpaths v)
    ⟨start, hs⟩ hstart W d hd hbuffer hmesh q z μ D r s hdist hdr n hbound hinj
    B hB Wj hW hWb hμ select hselect parts E hE hdE hBA initial n₀ P a₀ R₀ S₀
    eps mesh delta eta heps hmesh₀ hbuffer₀ hnone hdiam hnear hpoint hsteps hwrange
    hbrange hfailure htail hosc rWalk rMiddle rBrownian hrWalk hrBrownian
    hwalkBudget hbrownianBudget hmiddleBudget hsmall hbudget hcontain

end MatedCRT
end
