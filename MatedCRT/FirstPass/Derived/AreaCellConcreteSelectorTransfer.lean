import MatedCRT.FirstPass.Derived.AreaCellAmbientSelectedTransfer

/-! # Stopped-collar transfer with cell selectors -/

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

/-- The ambient selected-start transfer specialized to the cell selectors arising
from a common family of partitions and choices. -/
theorem MatedCRTEnv.uniform_areaCell_stopped_collar_transfer_of_cell_selectors
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
    (_hH : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (q : V → LatticeProb.Euc 2) (hinj : Function.Injective q)
    (center : J → LatticeProb.Euc 2) (rad : J → ℝ)
    (A : Set V)
    (hA : ∀ v ∈ A, 0 < (finiteConductanceRestriction
      (fun x y : (areaCellConfig h hε (S.mult ε ω)).cells =>
        (areaCellConfig h hε (S.mult ε ω)).c x y)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) V).totalConductance v)
    (hballA : ∀ j, q ⁻¹' ball (center j) (rad j) ⊆ A),
    let N := finiteConductanceRestriction
      (fun x y : (areaCellConfig h hε (S.mult ε ω)).cells =>
        (areaCellConfig h hε (S.mult ε ω)).c x y)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) V
    let B := fun j => q ⁻¹' ball (center j) (rad j)
    let hB := fun j v hv => hA v (hballA j hv)
    let W := fun j => ball (center j) (rad j)
    let hW : ∀ j, IsOpen (W j) := fun _ => isOpen_ball
    ∀ (D : Set (LatticeProb.Euc 2)) (m : ℕ → ℕ)
    (E : ∀ i, Fin (m i) → Set (LatticeProb.Euc 2))
    (choice : ∀ i, Fin (m i) → Option J)
    (hgeom : (∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k))) ∧
      (∀ i k, MeasurableSet (E i k)) ∧
      (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a) ∧
      (∀ i k j, choice i k = some j → E i k ⊆ W j) ∧
      (∀ i j, closure (W j) ⊆ ⋃ k, E i k) ∧
      (∀ i, Measurable (cellSelector (E i) (choice i))) ∧
      (∀ i x j, cellSelector (E i) (choice i) x = some j →
        ball x (margin / 2) ⊆ W j) ∧
      (∀ i x, cellSelector (E i) (choice i) x = none → x ∉ D))
    (_haccess : N.BoundaryAccessible A)
    (v : V) (P : TimePartition n)
    (p : V → LatticeProb.Euc 2) (φ : Plane → LatticeProb.Euc 2)
    (Wambient : Set Plane) (scale : ℝ)
    (hAW : ∀ v : V, scale • areaCellRepresentative h hε (S.mult ε ω) v.1 ∈ Wambient → v ∈ A)
    (hUW : φ ⁻¹' U ⊆ Wambient)
    (hp : p = fun x : V => φ (scale • areaCellRepresentative h hε (S.mult ε ω) x.1)),
    let hsub : p ⁻¹' U ⊆ A := fun v hv => hAW v (hUW (by simpa only [Set.mem_preimage, hp] using hv))
    let hUpos : ∀ v ∈ p ⁻¹' U, 0 < N.totalConductance v := fun v hv => hA v (hsub hv)
    ∀ {mesh R Srange : ℝ} (_hmesh : 0 ≤ mesh)
    (_hbuffer : a + e + mesh < δ) (_hpq : ∀ v, dist (p v) (q v) ≤ a)
    (_hpoint : R + a + Srange ≤ e)
    (_hwrange : ∀ initial : J, cellSelector (E 0) (choice 0) (q v) = some initial →
      ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial (fun i => cellSelector (E i) (choice i)) ω i).2 ∈ curveOscillationLe R)
    (_hbrange : ∀ initial : J, cellSelector (E 0) (choice 0) (q v) = some initial →
      ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion W (q v) initial (brownianSelectorForWalk (fun i => cellSelector (E i) (choice i))) i ω).2 ∈
        curveOscillationLe Srange)
    {b : ℝ} (_hb : 0 ≤ b)
    (innerSets : J → Set (LatticeProb.Euc 2))
    (_hIball : ∀ j, innerSets j ⊆ W j)
    (_hselected : ∃ initial : J, cellSelector (E 0) (choice 0) (q v) = some initial ∧ q v ∈ innerSets initial ∧
      (∀ i < n, ∀ k j, choice i k = some j →
      ∀ w : V, q w ∈ E i k → ∀ y ∈ E i k, ∀ l,
      |(((N.discreteHarmonicMeasure (B j) (hB j) w).map q) (E (i + 1) l)).toReal -
        (((stoppedBrownianLaw (W j) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E (i + 1) l)).toReal| ≤
          b / (m (i + 1) + 1)) ∧
      (∀ i, |(((N.discreteHarmonicMeasure (B initial) (hB initial) v).map q)
        (E 0 i)).toReal - (((stoppedBrownianLaw (W initial) (q v) μ).map BouRabeeGwynne.CurveSpace.endPoint)
          (E 0 i)).toReal| ≤ b / (m 0 + 1)))
    (_hballC : ∀ j, closure (ball (center j) (rad j)) ⊆ C) (_hzU : q v ∈ U)
    (_hTD : thickening δ U ⊆ D)
    (_hφ : Isometry φ) (Wmesh : Set Plane)
    (diameter : ℝ) (_hscale : 0 ≤ scale) (_hdiameter : 0 ≤ diameter)
    (_hcellBuffer : ∀ x ∈ φ ⁻¹' U, Metric.closedBall x (scale * diameter) ⊆ Wmesh)
    (_hcellMesh : ∀ C : (areaCellConfig h hε (S.mult ε ω)).cells, (∃ z ∈ (C.1 : Set Plane), scale • z ∈ Wmesh) →
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
    ∃ initial : J, cellSelector (E 0) (choice 0) (q v) = some initial ∧
    μ {ω | (brownianSkeletonClock W (q v) initial (brownianSelectorForWalk (fun i => cellSelector (E i) (choice i))) n ω).1 =
      false} ≤ ENNReal.ofReal τ ∧
    ∃ ρ : Measure ((ℕ → V) × C(unitInterval, LatticeProb.Euc 2)),
      IsProbabilityMeasure ρ ∧ ρ.fst = N.trajectoryLaw A hA v ∧
      ρ.map (fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial (fun i => cellSelector (E i) (choice i)) x.1, x.2)) =
        (N.walkBrownianJointLaw q hinj B hB W hW μ (fun i => cellSelector (E i) (choice i)) hgeom.2.2.2.2.2.1 m E hgeom.2.1 hgeom.1 initial v (q v)).map
          (fun x => (x.1, pastedBrownianCurve P x.2)) ∧
      ρ.snd = (μ.map (fun ω k => brownianSkeletonExcursion W (q v) initial
        (brownianSelectorForWalk (fun i => cellSelector (E i) (choice i))) k ω)).map (pastedBrownianCurve P) ∧
      levyProkhorovEDist
        ((N.trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
        (stoppedBrownianLaw U (q v) μ) ≤ (r : ℝ≥0∞) + ENNReal.ofReal τ ∧
      levyProkhorovEDist
        ((srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1)).map
          (fun x => CurveSpaceComparison.isometryEquiv 2
            (normalizedPrefixCurve
              (complexToEuclideanPath ((α : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm₀.le x))
              (pathExitTime Uc ((α : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm₀.le x)).toNNReal)))
        (stoppedBrownianLaw U (q v) μ) ≤ ENNReal.ofReal (4 * ((α : ℝ) * d)) +
          ((r : ℝ≥0∞) + ENNReal.ofReal τ) := by
  obtain ⟨c, hc, hcprop⟩ :=
    S.uniform_areaCell_stopped_collar_transfer_of_ambient_selected_start ω h α hm₀ Uc d hL hU hUb μ hμ hη hτ
  refine ⟨c, hc, ?_⟩
  intro J _ _ _ a e δ ha he hae hδ hδc C hC margin hmarginpos
  obtain ⟨n, hn⟩ := hcprop J a e δ ha he hae hδ hδc C hC margin hmarginpos
  refine ⟨n, ?_⟩
  intro ε hε V _ _ _ hH q hinj center rad A hA hballA
  dsimp only
  intro D m E choice hgeom haccess v P p φ Wambient scale hAW hUW hp mesh R S₀
    hmesh hbuffer hpq hpoint hwrange hbrange b hb innerSets hIball
    hselected hballC hzU hTD hφ Wmesh diameter hscale hdiameter
    hcellBuffer hcellMesh hstepMesh r hbudget hsmall hpaper
  obtain ⟨hdE, hE, hdiam, hinside, hcover, hs, hmargin, hnone⟩ := hgeom
  have hactive : ∀ k x, x ∈ D → cellSelector (E k) (choice k) x ≠ none :=
    fun k x hx heq => hnone k x heq hx
  exact hn hε V hH q hinj center rad A hA hballA
    (fun i => cellSelector (E i) (choice i)) hs m E hE hdE haccess v P p φ
    Wambient scale hAW hUW hp hmesh hbuffer hpq (fun i _ => hdiam i) hpoint hwrange hbrange
    choice (fun _ => rfl) hb (fun i _ => hinside i) (fun i _ => hcover i)
    innerSets hIball hselected hballC hzU hmargin D hTD hactive hφ Wmesh diameter
    hscale hdiameter hcellBuffer hcellMesh hstepMesh r hbudget hsmall hpaper

end MatedCRT
end
