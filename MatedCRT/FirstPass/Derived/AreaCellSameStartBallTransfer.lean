import MatedCRT.FirstPass.Derived.AreaCellBallSelectorBoundedTransfer

/-! # Same-start stopped-collar transfer for ball selectors -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace MatedCRT
open MeasureTheory Metric Set ProbabilityTheory _root_.HarmonicBalls ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 MatedCRTHarmonic.Markov LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped unitInterval NNReal ENNReal
universe u

/-- The ball-preimage stopping sets and a common starting point fit the bounded
stopped-collar transfer on the same finite network. -/
theorem MatedCRTEnv.uniform_areaCell_stopped_collar_transfer_of_same_start_ball_selectors
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (α : ℝ≥0) {m₀ : ℝ≥0} (hm₀ : 0 < m₀) (Uc : Set ℂ) (d : ℝ)
    {U : Set (LatticeProb.Euc 2)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (LatticeProb.BrownianPath 2)) [IsProbabilityMeasure μ] (hμ : LatticeProb.IsStandardBrownianLaw μ)
    {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ c > 0, ∀ (J : Type u) [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)],
    ∀ a e δ : ℝ, 0 ≤ a → 0 < e → a + e ≤ c → 0 < δ → δ ≤ c →
    ∀ C : Set (LatticeProb.Euc 2), Bornology.IsBounded C → ∀ margin : ℝ, 0 < margin →
    ∃ n : ℕ, ∀ {ε : ℝ} (hε : 0 < ε)
    (V : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (H : CellConfig) (_hH : H.IsCellConfiguration)
    (rep : H.cells → Plane) (_hrep : ∀ C, rep C ∈ (C.1 : Set Plane))
    (cell : V → H.cells) (N : FiniteConductanceNetwork V)
    (_hedge : ∀ v w, 0 < N.a v w → H.Adj (cell v) (cell w))
    (q : V → LatticeProb.Euc 2) (hinj : Function.Injective q)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (W : J → Set (LatticeProb.Euc 2)) (hW : ∀ j, IsOpen (W j))
    (center : J → LatticeProb.Euc 2)
    (rad : J → ℝ) (_hWball : ∀ j, W j = ball (center j) (rad j))
    (select : ℕ → LatticeProb.Euc 2 → Option J) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (LatticeProb.Euc 2))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    {A : Set V} (_hBpre : ∀ j, B j = q ⁻¹' W j)
    (_hballA : ∀ j, q ⁻¹' W j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (_haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : LatticeProb.Euc 2) (_hzq : z = q v) (P : TimePartition n)
    (p : V → LatticeProb.Euc 2)
    (_hsub : p ⁻¹' U ⊆ A) (hUpos : ∀ v ∈ p ⁻¹' U, 0 < N.totalConductance v)
    {mesh R Srange : ℝ} (_hmesh : 0 ≤ mesh)
    (_hbuffer : a + e + mesh < δ) (_hpq : ∀ v, dist (p v) (q v) ≤ a)
    (_hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (_hpoint : R + a + Srange ≤ e)
    (_hwrange : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial select ω i).2 ∈ curveOscillationLe R)
    (_hbrange : ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion W z initial (brownianSelectorForWalk select) i ω).2 ∈
        curveOscillationLe Srange)
    (choice : ∀ i, Fin (m i) → Option J)
    (_hselect : ∀ i, select i = cellSelector (E i) (choice i))
    {b : ℝ} (_hb : 0 ≤ b)
    (_hinside : ∀ i < n, ∀ k j, choice i k = some j → E i k ⊆ W j)
    (_hcover : ∀ i ≤ n, ∀ j, closure (W j) ⊆ ⋃ k, E i k)
    (_herror : ∀ i < n, ∀ k j, choice i k = some j →
      ∀ w : V, q w ∈ E i k → ∀ y ∈ E i k, ∀ l,
      |(((N.discreteHarmonicMeasure (B j) (hB j) w).map q) (E (i + 1) l)).toReal -
        (((stoppedBrownianLaw (W j) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E (i + 1) l)).toReal| ≤
          b / (m (i + 1) + 1))
    (_hz : z ∈ W initial)
    (_hinit : ∀ i, |(((N.discreteHarmonicMeasure (B initial) (hB initial) v).map q)
      (E 0 i)).toReal - (((stoppedBrownianLaw (W initial) z μ).map BouRabeeGwynne.CurveSpace.endPoint)
        (E 0 i)).toReal| ≤ b / (m 0 + 1))
    (_hballC : ∀ j, closure (ball (center j) (rad j)) ⊆ C) (_hzU : z ∈ U)
    (_hmargin : ∀ k x j, select k x = some j → ball x (margin / 2) ⊆ W j)
    (D : Set (LatticeProb.Euc 2)) (_hTD : thickening δ U ⊆ D)
    (_hactive : ∀ k x, x ∈ D → select k x ≠ none)
    (φ : Plane → LatticeProb.Euc 2) (_hφ : Isometry φ) (Wmesh : Set Plane)
    (scale diameter : ℝ) (_hscale : 0 ≤ scale) (_hdiameter : 0 ≤ diameter)
    (_hp : p = fun x : V => φ (scale • rep (cell x)))
    (_hcellBuffer : ∀ x ∈ φ ⁻¹' U, Metric.closedBall x (scale * diameter) ⊆ Wmesh)
    (_hcellMesh : ∀ C : H.cells, (∃ z ∈ (C.1 : Set Plane), scale • z ∈ Wmesh) →
      Metric.diam (C.1 : Set Plane) ≤ diameter)
    (_hstepMesh : 2 * (scale * diameter) ≤ mesh)
    (r : ℝ≥0)
    (_hbudget : ((n + 1 : ℝ≥0∞) * ENNReal.ofReal b +
      (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
      (ENNReal.ofReal τ + (n + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤ (r : ℝ≥0∞))
    (_hsmall : ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞))
    (_hpaper : ∀ (ν : Measure (BouRabeeGwynne.CurveSpace 2)) (s₀ : ℝ≥0) (τ₀ : ℝ),
      levyProkhorovEDist
        ((N.trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U))) ν ≤
          (s₀ : ℝ≥0∞) + ENNReal.ofReal τ₀ →
      levyProkhorovEDist
        ((srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1)).map
          (fun x => CurveSpaceComparison.isometryEquiv 2
            (normalizedPrefixCurve
              (complexToEuclideanPath ((α : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm₀.le x))
              (pathExitTime Uc ((α : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm₀.le x)).toNNReal)))
        ν ≤ ENNReal.ofReal (4 * ((α : ℝ) * d)) +
          ((s₀ : ℝ≥0∞) + ENNReal.ofReal τ₀)),
    μ {ω | (brownianSkeletonClock W z initial (brownianSelectorForWalk select) n ω).1 =
      false} ≤ ENNReal.ofReal τ ∧
    ∃ ρ : Measure ((ℕ → V) × C(unitInterval, LatticeProb.Euc 2)),
      IsProbabilityMeasure ρ ∧ ρ.fst = N.trajectoryLaw A hA v ∧
      ρ.map (fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial select x.1, x.2)) =
        (N.walkBrownianJointLaw q hinj B hB W hW μ select hs m E hE hdE initial v z).map
          (fun x => (x.1, pastedBrownianCurve P x.2)) ∧
      ρ.snd = (μ.map (fun ω k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω)).map (pastedBrownianCurve P) ∧
      levyProkhorovEDist
        ((N.trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
        (stoppedBrownianLaw U z μ) ≤ (r : ℝ≥0∞) + ENNReal.ofReal τ ∧
      levyProkhorovEDist
        ((srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1)).map
          (fun x => CurveSpaceComparison.isometryEquiv 2
            (normalizedPrefixCurve
              (complexToEuclideanPath ((α : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm₀.le x))
              (pathExitTime Uc ((α : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm₀.le x)).toNNReal)))
        (stoppedBrownianLaw U z μ) ≤ ENNReal.ofReal (4 * ((α : ℝ) * d)) +
          ((r : ℝ≥0∞) + ENNReal.ofReal τ) := by
  obtain ⟨c, hc, hcprop⟩ :=
    S.uniform_areaCell_stopped_collar_transfer_of_ball_selectors ω h α hm₀ Uc d hL hU hUb μ hμ hη hτ
  refine ⟨c, hc, ?_⟩
  intro J _ _ _ a e δ ha he hae hδ hδc C hC margin hmarginpos
  obtain ⟨n, hn⟩ := hcprop J a e δ ha he hae hδ hδc C hC margin hmarginpos
  refine ⟨n, ?_⟩
  intro ε hε V _ _ _ H hH rep hrep cell N hedge q hinj B hB W hW center rad hWball select hs m E hE hdE A hBpre hballA hA haccess
    initial v z hzq P p hsub hUpos mesh R S₀ hmesh hbuffer hpq hdiam hpoint
    hwrange hbrange choice hselect b hb hinside hcover herror hz hinit hballC hzU
    hmargin D hTD hactive φ hφ Wmesh scale diameter hscale hdiameter hp hcellBuffer
    hcellMesh hstepMesh r hbudget hsmall hpaper
  have hBA : ∀ j, B j ⊆ A := fun j => by
    rw [hBpre j]
    exact hballA j
  have hnear : dist (q v) z ≤ a := by
    rw [hzq, dist_self]
    exact ha
  exact hn hε V H hH rep hrep cell N hedge q hinj B hB W hW center rad hWball
    select hs m E hE hdE hBA hA haccess initial v z P p hsub hUpos hmesh hbuffer hpq
    hdiam hnear hpoint hwrange hbrange choice hselect hb hinside hcover herror hz
    hinit hballC hzU hmargin D hTD hactive φ hφ Wmesh scale diameter hscale hdiameter
    hp hcellBuffer hcellMesh hstepMesh r hbudget hsmall hpaper

end MatedCRT
end
