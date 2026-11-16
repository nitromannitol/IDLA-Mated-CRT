import MatedCRT.FirstPass.Derived.AreaCellCoveredShiftedSelectors

/-! # Conditional transfer on shifted area-cell networks -/
set_option autoImplicit false
noncomputable section
namespace MatedCRT
open Set Metric MeasureTheory Filter ProbabilityTheory _root_.HarmonicBalls BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.GMS3 MatedCRTHarmonic.Markov LatticeProb
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped unitInterval ENNReal NNReal Topology
universe u

/-- A common shifted network and its selected starts satisfy the conditional coupling
and distance bounds for the chosen horizon and error budget. -/
theorem MatedCRTEnv.exists_covered_shifted_areaCell_actual_transfer
{Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (α : ℝ≥0) {m₀ : ℝ≥0} (hm₀ : 0 < m₀) (Uc : Set ℂ) (d : ℝ)
    {U : Set (LatticeProb.Euc 2)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (LatticeProb.BrownianPath 2)) [IsProbabilityMeasure μ] (hμ : LatticeProb.IsStandardBrownianLaw μ)
    (J : Type u) [Fintype J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (center : J → LatticeProb.Euc 2) (rad : J → ℝ)
    (margin : ℝ) (hmargin : 0 < margin) (r : ℝ≥0)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlf : ∀ n, IsLocallyFiniteMult (S.mult (ε n) ω))
    (hlfg : ∀ n, MatedCRTHarmonic.MatedCRT.IsLocallyFinite (ε n) (S.bm ω))
    (H : ∀ n, CellularEmbedding
      (MatedCRTHarmonic.MatedCRT.graph (ε n) (S.bm ω) (hlfg n)) (0 : ℤ))
    (hH : ∀ n, (H n).cell = cell (ε n) (S.η ω))
    {scale : ℝ≥0} (hscale : 0 < scale) {U₀ W : Set Plane} (hUW : U₀ ⊆ W)
    (hW : Bornology.IsBounded W)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Filter.Tendsto t Filter.atTop (𝓝 0))
    (φ : Plane → LatticeProb.Euc 2) (hφ : Isometry φ)
    {O : Set (LatticeProb.Euc 2)} (hO : IsOpen O)
    (hKO : ∀ j, Metric.closedBall (center j) (rad j) ⊆ O) (hOW : φ ⁻¹' O ⊆ W)
    (Us Is Ks : J → Set (LatticeProb.Euc 2))
    (hUs : ∀ j, IsOpen (Us j)) (hUsb : ∀ j, Bornology.IsBounded (Us j))
    (hIs : ∀ j, IsCompact (Is j)) (hIUs : ∀ j, Is j ⊆ Us j)
    (hKs : ∀ j, IsCompact (Ks j)) (hKUs : ∀ j, Ks j ⊆ Us j)
    (radius : J → ℝ) (hradius : ∀ j, 0 < radius j)
    (hcollar : ∀ j x, x ∈ Is j → ∀ y, dist y x < radius j → y ∈ Ks j)
    (hparams : ∃ η τ : ℝ, 0 < η ∧ 0 < τ ∧
      ∀ c : ℝ, 0 < c →
        ∃ (a e δ mesh : ℝ) (C : Set (LatticeProb.Euc 2)),
          0 < a ∧ 0 < e ∧ 0 < δ ∧ 0 < mesh ∧
          a + e ≤ c ∧ δ ≤ c ∧ a + e + mesh < δ ∧
          ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞) ∧
          IsCompact C ∧ thickening δ U ⊆ C ∧
          thickening δ U ⊆ ⋃ j, ball (center j) (margin / 4) ∧
          (∀ j, closure (ball (center j) (rad j)) ⊆ C) ∧
          ∀ L : ℕ, ∃ b : ℝ, 0 < b ∧
            ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b +
              (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
              (ENNReal.ofReal τ + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤
                (r : ℝ≥0∞)) :
    ∃ (η τ c a e δ₀ mesh : ℝ) (C : Set (LatticeProb.Euc 2)),
      0 < η ∧ 0 < τ ∧ 0 < c ∧ 0 < a ∧ 0 < e ∧ 0 < δ₀ ∧ 0 < mesh ∧
      a + e ≤ c ∧ δ₀ ≤ c ∧ a + e + mesh < δ₀ ∧
      ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞) ∧ IsCompact C ∧
      thickening δ₀ U ⊆ C ∧
      thickening δ₀ U ⊆ ⋃ j, ball (center j) (margin / 4) ∧
      (∀ j, closure (ball (center j) (rad j)) ⊆ C) ∧
    ∃ (L : ℕ) (b : ℝ), (0 < b ∧
      ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b +
        (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
        (ENNReal.ofReal τ + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤
          (r : ℝ≥0∞)) ∧ (∀ {ε : ℝ} (hε : 0 < ε)
    (V : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (_hH : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (q : V → LatticeProb.Euc 2) (hinj : Function.Injective q)
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
    (v : V) (P : TimePartition L)
    (p : V → LatticeProb.Euc 2) (φ : Plane → LatticeProb.Euc 2)
    (Wambient : Set Plane) (scale : ℝ)
    (hAW : ∀ v : V, scale • areaCellRepresentative h hε (S.mult ε ω) v.1 ∈ Wambient → v ∈ A)
    (hUW : φ ⁻¹' U ⊆ Wambient)
    (hp : p = fun x : V => φ (scale • areaCellRepresentative h hε (S.mult ε ω) x.1)),
    let hsub : p ⁻¹' U ⊆ A := fun v hv => hAW v (hUW (by simpa only [Set.mem_preimage, hp] using hv))
    let hUpos : ∀ v ∈ p ⁻¹' U, 0 < N.totalConductance v := fun v hv => hA v (hsub hv)
    ∀ {mesh R Srange : ℝ} (_hmesh : 0 ≤ mesh)
    (_hbuffer : a + e + mesh < δ₀) (_hpq : ∀ v, dist (p v) (q v) ≤ a)
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
      (∀ i < L, ∀ k j, choice i k = some j →
      ∀ w : V, q w ∈ E i k → ∀ y ∈ E i k, ∀ l,
      |(((N.discreteHarmonicMeasure (B j) (hB j) w).map q) (E (i + 1) l)).toReal -
        (((stoppedBrownianLaw (W j) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E (i + 1) l)).toReal| ≤
          b / (m (i + 1) + 1)) ∧
      (∀ i, |(((N.discreteHarmonicMeasure (B initial) (hB initial) v).map q)
        (E 0 i)).toReal - (((stoppedBrownianLaw (W initial) (q v) μ).map BouRabeeGwynne.CurveSpace.endPoint)
          (E 0 i)).toReal| ≤ b / (m 0 + 1)))
    (_hballC : ∀ j, closure (ball (center j) (rad j)) ⊆ C) (_hzU : q v ∈ U)
    (_hTD : thickening δ₀ U ⊆ D)
    (_hφ : Isometry φ) (Wmesh : Set Plane)
    (diameter : ℝ) (_hscale : 0 ≤ scale) (_hdiameter : 0 ≤ diameter)
    (_hcellBuffer : ∀ x ∈ φ ⁻¹' U, Metric.closedBall x (scale * diameter) ⊆ Wmesh)
    (_hcellMesh : ∀ C : (areaCellConfig h hε (S.mult ε ω)).cells, (∃ z ∈ (C.1 : Set Plane), scale • z ∈ Wmesh) →
      Metric.diam (C.1 : Set Plane) ≤ diameter)
    (_hstepMesh : 2 * (scale * diameter) ≤ mesh)
    (r : ℝ≥0)
    (_hbudget : ((L + 1 : ℝ≥0∞) * ENNReal.ofReal b +
      (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
      (ENNReal.ofReal τ + (L + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤ (r : ℝ≥0∞))
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
    μ {ω | (brownianSkeletonClock W (q v) initial (brownianSelectorForWalk (fun i => cellSelector (E i) (choice i))) L ω).1 =
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
          ((r : ℝ≥0∞) + ENNReal.ofReal τ)) ∧
    ∃ (R : ∀ n, Set (areaCellConfig h (hε n) (S.mult (ε n) ω)).cells)
      (hR : ∀ n, (R n).Finite) (q : ∀ n, R n → Plane) (N : ℕ),
      (∀ n, Function.Injective (fun v : R (n + N) => φ (q (n + N) v))) ∧
      (∀ n (v : R (n + N)), ∃ x ∈ (v.1.1 : Set Plane), q (n + N) v = (scale : ℝ) • x) ∧
      (∀ n, letI := (hR (n + N)).fintype
       let A : Set (R (n + N)) := {v | (scale : ℝ) •
         areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v ∈ W}
       let net := finiteConductanceRestriction
          (fun v w : (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).cells =>
            (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).c v w)
          (areaCellConfig_conductance_symm h (hε (n + N)) (S.mult (ε (n + N)) ω)
            (S.mult_symm (ε (n + N)) ω))
          (areaCellConfig_conductance_nonneg h (hε (n + N)) (S.mult (ε (n + N)) ω))
          (areaCellConfig_conductance_self h (hε (n + N)) (S.mult (ε (n + N)) ω)
            (S.mult_self (ε (n + N)) ω)) (R (n + N))
       (∀ v ∈ A, 0 < net.totalConductance v) ∧ net.BoundaryAccessible A ∧
       (∀ j, (fun v : R (n + N) => φ ((scale : ℝ) •
           areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v)) ⁻¹'
             Metric.ball (center j) (rad j) ⊆ A) ∧
       (∀ j, (fun v : R (n + N) => φ (q (n + N) v)) ⁻¹'
             Metric.ball (center j) (rad j) ⊆ A)) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop, ∀ v : R (n + N),
        dist (φ ((scale : ℝ) • areaCellRepresentative h (hε (n + N))
          (S.mult (ε (n + N)) ω) v)) (φ (q (n + N) v)) < δ) ∧
      (∀ P : ℕ → Prop, (∀ᶠ n in Filter.atTop, P n) →
        ∀ᶠ n in Filter.atTop, P (n + N)) ∧
      (let Rset := fun n => R (n + N)
       let : ∀ n, Fintype (Rset n) := fun n => (hR (n + N)).fintype
       let : ∀ n, MeasurableSpace (Rset n) := fun _ => ⊤
       let : ∀ n, MeasurableSingletonClass (Rset n) := fun _ => ⟨fun _ => trivial⟩
       let net := fun n => finiteConductanceRestriction
          (fun v w : (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).cells =>
            (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).c v w)
          (areaCellConfig_conductance_symm h (hε (n + N)) (S.mult (ε (n + N)) ω)
            (S.mult_symm (ε (n + N)) ω))
          (areaCellConfig_conductance_nonneg h (hε (n + N)) (S.mult (ε (n + N)) ω))
          (areaCellConfig_conductance_self h (hε (n + N)) (S.mult (ε (n + N)) ω)
            (S.mult_self (ε (n + N)) ω)) (Rset n)
       let p := fun n (v : Rset n) => φ ((scale : ℝ) •
          areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v)
       let q' := fun n (v : Rset n) => φ (q (n + N) v)
       let A := fun n => {v : Rset n | (scale : ℝ) •
          areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v ∈ W}
       ∃ (hA : ∀ n v, v ∈ A n → 0 < (net n).totalConductance v)
         (hball : ∀ n j (v : Rset n),
           (p n v ∈ ball (center j) (rad j) → v ∈ A n) ∧
           (q' n v ∈ ball (center j) (rad j) → v ∈ A n)),
       ∀ (_href : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : Rset n,
      ∀ _hv : p n v ∈ Ks j,
      levyProkhorovDist
        (((net n).discreteHarmonicMeasure (p n ⁻¹' ball (center j) (rad j))
          (fun w hw => hA n w ((hball n j w).1 hw)) v).map (p n))
        ((stoppedBrownianLaw (Us j) (p n v) μ).map BouRabeeGwynne.CurveSpace.endPoint) < ε)
    (_hosc : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : Rset n,
      q' n v ∈ Is j → ∃ (δ η : ℝ) (E : Set (ℕ → Rset n)),
        (∀ w, dist (p n w) (q' n w) ≤ δ) ∧ η + δ < ε / 4 ∧
        (net n).trajectoryLaw (A n) (hA n) v E ≤ (ENNReal.ofReal (ε / 4)) ∧
        (∀ᵐ ω ∂(net n).trajectoryLaw (A n) (hA n) v, ω ∉ E →
          exitTime (p n ⁻¹' ball (center j) (rad j + δ)) ω ≠ ⊤ ∧
          ∀ i ∈ Icc ((exitTime (p n ⁻¹' ball (center j) (rad j - δ)) ω).untopD 0)
              ((exitTime (p n ⁻¹' ball (center j) (rad j + δ)) ω).untopD 0),
            ∀ k ∈ Icc ((exitTime (p n ⁻¹' ball (center j) (rad j - δ)) ω).untopD 0)
                ((exitTime (p n ⁻¹' ball (center j) (rad j + δ)) ω).untopD 0),
              dist (p n (ω i)) (p n (ω k)) ≤ η))
    (_hinner : ∀ j : J, ball (center j) (margin / 2) ⊆ Is j)
    (_hR : ∀ j : J, margin ≤ rad j)
    (_hUball : ∀ j : J, Us j = ball (center j) (rad j))
    (_hIball : ∀ j : J, Is j ⊆ ball (center j) (rad j)),
    ∃ (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set (LatticeProb.Euc 2))
      (δ : Fin (L + 1) → ℝ) (choice : ∀ i, Fin (m i) → Option J),
      (∀ i, 0 < δ i) ∧
      (∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l))) ∧
      (∀ i, C ⊆ ⋃ k, E i k) ∧
      (∀ i k, MeasurableSet (E i k)) ∧
      (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a) ∧
      (∀ i k j, choice i k = some j → E i k ⊆ Is j) ∧
      (∀ i k j, choice i k = some j → E i k ⊆ ball (center j) (rad j)) ∧
      (∀ i j, closure (ball (center j) (rad j)) ⊆ ⋃ k, E i k) ∧
      (∀ i, Measurable (cellSelector (E i) (choice i))) ∧
      (∀ i x, x ∈ (thickening δ₀ U) → cellSelector (E i) (choice i) x ≠ none) ∧
      (∀ i x j, cellSelector (E i) (choice i) x = some j →
        ball x (margin / 2) ⊆ ball (center j) (rad j)) ∧
      (∀ᶠ n in atTop, ∀ (initial : J) (v₀ : Rset n) (z : LatticeProb.Euc 2),
        q' n v₀ ∈ Is initial → z ∈ Is initial →
        dist (q' n v₀) z ≤ δ ⟨0, Nat.zero_lt_succ L⟩ →
        let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
        let m' : ℕ → ℕ := fun t => m (ix t)
        let E' : ∀ t, Fin (m' t) → Set (LatticeProb.Euc 2) := fun t => E (ix t)
        let choice' : ∀ t, Fin (m' t) → Option J := fun t => choice (ix t)
        (∀ t < L, ∀ k j, choice' t k = some j →
          ∀ v : Rset n, q' n v ∈ E' t k → ∀ y ∈ E' t k, ∀ l,
            |(((net n).discreteHarmonicMeasure (q' n ⁻¹' ball (center j) (rad j)) (fun w hw => hA n w ((hball n j w).2 hw)) v).map (q' n) (E' (t + 1) l)).toReal -
              (((stoppedBrownianLaw (ball (center j) (rad j)) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E' (t + 1) l)).toReal| ≤
                b / (m' (t + 1) + 1)) ∧
        (∀ k, |(((net n).discreteHarmonicMeasure (q' n ⁻¹' ball (center initial) (rad initial)) (fun w hw => hA n w ((hball n initial w).2 hw)) v₀).map (q' n)
            (E' 0 k)).toReal -
          (((stoppedBrownianLaw (ball (center initial) (rad initial)) z μ).map BouRabeeGwynne.CurveSpace.endPoint) (E' 0 k)).toReal| ≤
            b / (m' 0 + 1)) ) ∧
    let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
    let m := fun t => m (ix t)
    let E := fun t => E (ix t)
    let choice := fun t => choice (ix t)
    ((∀ t, Pairwise (fun k l => Disjoint (E t k) (E t l))) ∧
    (∀ t k, MeasurableSet (E t k)) ∧
    (∀ t k, ∀ x ∈ E t k, ∀ y ∈ E t k, dist x y ≤ a) ∧
    (∀ t k j, choice t k = some j → E t k ⊆ ball (center j) (rad j)) ∧
    (∀ t j, closure (ball (center j) (rad j)) ⊆ ⋃ k, E t k) ∧
    (∀ t, Measurable (cellSelector (E t) (choice t))) ∧
    (∀ t x j, cellSelector (E t) (choice t) x = some j →
      ball x (margin / 2) ⊆ ball (center j) (rad j)) ∧
    (∀ t x, cellSelector (E t) (choice t) x = none → x ∉ (thickening δ₀ U))) ∧
    (∀ᶠ n in atTop, (∀ v : Rset n, dist (p n v) (q' n v) ≤ a) ∧
      ∀ v : Rset n, q' n v ∈ U →
      dist (p n v) (q' n v) ≤ a ∧
      ∃ j, cellSelector (E 0) (choice 0) (q' n v) = some j ∧ q' n v ∈ Is j ∧
      (∀ t < L, ∀ k l, choice t k = some l →
        ∀ w : Rset n, q' n w ∈ E t k → ∀ y ∈ E t k, ∀ r,
          |(((net n).discreteHarmonicMeasure (q' n ⁻¹' ball (center l) (rad l))
              (fun u hu => hA n u ((hball n l u).2 hu)) w).map (q' n) (E (t + 1) r)).toReal -
            (((stoppedBrownianLaw (ball (center l) (rad l)) y μ).map
              BouRabeeGwynne.CurveSpace.endPoint) (E (t + 1) r)).toReal| ≤
              b / (m (t + 1) + 1)) ∧
      (∀ k, |(((net n).discreteHarmonicMeasure (q' n ⁻¹' ball (center j) (rad j))
          (fun u hu => hA n u ((hball n j u).2 hu)) v).map (q' n) (E 0 k)).toReal -
        (((stoppedBrownianLaw (ball (center j) (rad j)) (q' n v) μ).map
          BouRabeeGwynne.CurveSpace.endPoint) (E 0 k)).toReal| ≤ b / (m 0 + 1))) ∧
    (∀ᶠ n in atTop, ∀ (v : Rset n), q' n v ∈ U →
      ∃ (hinj : Function.Injective (q' n))
        (hs : ∀ i, Measurable (cellSelector (E i) (choice i)))
        (hE : ∀ i k, MeasurableSet (E i k))
        (hdE : ∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l)))
        (hUpos : ∀ w ∈ p n ⁻¹' U, 0 < (net n).totalConductance w),
      let B := fun j => q' n ⁻¹' ball (center j) (rad j)
      let hB := fun j w hw => hA n w ((hball n j w).2 hw)
      let Wj := fun j => ball (center j) (rad j)
      let hWj : ∀ j, IsOpen (Wj j) := fun _ => isOpen_ball
      ∀ (R₀ S₀ : ℝ), R₀ + a + S₀ ≤ e →
        (∀ initial : J, cellSelector (E 0) (choice 0) (q' n v) = some initial →
          ∀ᵐ ω ∂(net n).trajectoryLaw (A n) (hA n) v, ∀ i,
            ClockedWalkExcursion.curve (FiniteConductanceNetwork.actualWalkExcursionSequence
              (q' n) B initial (fun i => cellSelector (E i) (choice i)) ω i).2 ∈ curveOscillationLe R₀) →
        (∀ initial : J, cellSelector (E 0) (choice 0) (q' n v) = some initial →
          ∀ᵐ ω ∂μ, ∀ i,
            (brownianSkeletonExcursion Wj (q' n v) initial
              (brownianSelectorForWalk (fun i => cellSelector (E i) (choice i))) i ω).2 ∈
                curveOscillationLe S₀) →
        ∀ (Wmesh : Set Plane) (diameter : ℝ), 0 ≤ diameter →
          (∀ x ∈ φ ⁻¹' U, Metric.closedBall x ((scale : ℝ) * diameter) ⊆ Wmesh) →
          (∀ cell : (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).cells,
            (∃ z ∈ (cell.1 : Set Plane), (scale : ℝ) • z ∈ Wmesh) →
              Metric.diam (cell.1 : Set Plane) ≤ diameter) →
          2 * ((scale : ℝ) * diameter) ≤ mesh →
          (∀ (ν : Measure (BouRabeeGwynne.CurveSpace 2)) (s₀ : ℝ≥0) (τ₀ : ℝ),
            levyProkhorovEDist
              (((net n).trajectoryLaw (p n ⁻¹' U) hUpos v).map
                (stoppedPolygonalCurve (p n) (p n ⁻¹' U))) ν ≤
                (s₀ : ℝ≥0∞) + ENNReal.ofReal τ₀ →
            levyProkhorovEDist
              ((srwLaw (S.mult (ε (n + N)) ω)
                  ((euclideanCellEquiv h (hε (n + N))).symm v.1)).map
                (fun x => CurveSpaceComparison.isometryEquiv 2
                  (normalizedPrefixCurve
                    (complexToEuclideanPath ((α : ℝ) • interpPathCM
                      (vertexPoint (ε (n + N)) (S.η ω)) hm₀.le x))
                    (pathExitTime Uc ((α : ℝ) • interpPathCM
                      (vertexPoint (ε (n + N)) (S.η ω)) hm₀.le x)).toNNReal)))
              ν ≤ ENNReal.ofReal (4 * ((α : ℝ) * d)) +
                ((s₀ : ℝ≥0∞) + ENNReal.ofReal τ₀)) →
          ∃ initial : J, cellSelector (E 0) (choice 0) (q' n v) = some initial ∧
            μ {ω | (brownianSkeletonClock Wj (q' n v) initial
              (brownianSelectorForWalk (fun i => cellSelector (E i) (choice i))) L ω).1 =
                false} ≤ ENNReal.ofReal τ ∧
          ∃ ρ : Measure ((ℕ → Rset n) × C(unitInterval, LatticeProb.Euc 2)),
            IsProbabilityMeasure ρ ∧ ρ.fst = (net n).trajectoryLaw (A n) (hA n) v ∧
            ρ.map (fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
              (q' n) B initial (fun i => cellSelector (E i) (choice i)) x.1, x.2)) =
              ((net n).walkBrownianJointLaw (q' n) hinj B hB Wj hWj μ
                (fun i => cellSelector (E i) (choice i)) hs m E
                hE hdE initial v (q' n v)).map
                  (fun x => (x.1, pastedBrownianCurve (TimePartition.uniform L) x.2)) ∧
            ρ.snd = (μ.map (fun ω k => brownianSkeletonExcursion Wj (q' n v) initial
              (brownianSelectorForWalk (fun i => cellSelector (E i) (choice i))) k ω)).map
                (pastedBrownianCurve (TimePartition.uniform L)) ∧
            levyProkhorovEDist
              (((net n).trajectoryLaw (p n ⁻¹' U) hUpos v).map
                (stoppedPolygonalCurve (p n) (p n ⁻¹' U)))
              (stoppedBrownianLaw U (q' n v) μ) ≤ (r : ℝ≥0∞) + ENNReal.ofReal τ ∧
            levyProkhorovEDist
              ((srwLaw (S.mult (ε (n + N)) ω)
                  ((euclideanCellEquiv h (hε (n + N))).symm v.1)).map
                (fun x => CurveSpaceComparison.isometryEquiv 2
                  (normalizedPrefixCurve
                    (complexToEuclideanPath ((α : ℝ) • interpPathCM
                      (vertexPoint (ε (n + N)) (S.η ω)) hm₀.le x))
                    (pathExitTime Uc ((α : ℝ) • interpPathCM
                      (vertexPoint (ε (n + N)) (S.η ω)) hm₀.le x)).toNNReal)))
              (stoppedBrownianLaw U (q' n v) μ) ≤ ENNReal.ofReal (4 * ((α : ℝ) * d)) +
                ((r : ℝ≥0∞) + ENNReal.ofReal τ))
) := by
  classical
  obtain ⟨η, τ, c, a, e, δ, mesh, C, hη, hτ, hc, ha, he, hδ, hmesh,
    hae, hδc, hbuffer, hsmall, hC, hUC, hcover, hballC, L, b, hb, hn,
    R, hR, q, N, hqi, hqc, hgeometry, hclose, hshift, hselect⟩ :=
    S.exists_covered_shifted_areaCell_selectors ω h α hm₀ Uc d hL hU hUb μ hμ
      J center rad margin hmargin r ε hε hlf hlfg H hH hscale hUW hW t ht ht0
      φ hφ hO hKO hOW Us Is Ks hUs hUsb hIs hIUs hKs hKUs radius hradius hcollar hparams
  obtain ⟨hb, hbudget⟩ := hb
  have hUD : U ⊆ thickening δ U := Metric.self_subset_thickening hδ U
  have hcover' : ∀ x ∈ thickening δ U, ∃ j, x ∈ ball (center j) (margin / 4) := by
    intro x hx
    simpa only [Set.mem_iUnion] using hcover hx
  refine ⟨η, τ, c, a, e, δ, mesh, C, hη, hτ, hc, ha, he, hδ, hmesh,
    hae, hδc, hbuffer, hsmall, hC, hUC, hcover, hballC, L, b, ⟨hb, hbudget⟩, hn,
    R, hR, q, N, hqi, hqc, hgeometry, hclose, hshift, ?_⟩
  dsimp only at hselect ⊢
  obtain ⟨hA, hball, hselect⟩ := hselect
  refine ⟨hA, hball, ?_⟩
  intro href hosc hinner hR hUball hIball
  have hUO : U ⊆ O := by
    intro x hx
    obtain ⟨j, hj⟩ := hcover' x (hUD hx)
    apply hKO j
    rw [Metric.mem_closedBall]
    have hdist : dist x (center j) < margin / 4 := hj
    linarith [hR j]
  have hUambient : φ ⁻¹' U ⊆ W := Set.Subset.trans (Set.preimage_mono hUO) hOW
  obtain ⟨m, E, δs, choice, hδs, hdisj, hcoverC, hmeas, hdiam, hinsideI,
    hinside, hcoverBall, hselector, hnone, hballmargin, hest, hgeom, hev⟩ :=
    hselect href hosc hinner hR hUball hIball
  refine ⟨m, E, δs, choice, hδs, hdisj, hcoverC, hmeas, hdiam, hinsideI,
    hinside, hcoverBall, hselector, hnone, hballmargin, hest, hgeom, hev, ?_⟩
  filter_upwards [hev] with n hchosen
  intro v hv
  let : Fintype (R (n + N)) := (‹∀ n, (R n).Finite› (n + N)).fintype
  let : MeasurableSpace (R (n + N)) := ⊤
  let : MeasurableSingletonClass (R (n + N)) := ⟨fun _ => trivial⟩
  let hUpos := fun w hw => hA n w (hUambient hw)
  refine ⟨hqi n, hgeom.2.2.2.2.2.1, hgeom.2.1, hgeom.1, hUpos, ?_⟩
  intro R₀ S₀
  obtain ⟨hglobal, hstarts⟩ := hchosen
  obtain ⟨_, hselected⟩ := hstarts v hv
  let A : Set (R (n + N)) := {v | (scale : ℝ) •
    areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v ∈ W}
  have hconf := S.areaCellConfig_isCellConfiguration ω (hε (n + N)) h
    (hlfg (n + N)) (H (n + N)) (hH (n + N))
  have haccess := (hgeometry n).2.1
  have hball' : ∀ j, (fun v : R (n + N) => φ (q (n + N) v)) ⁻¹'
      ball (center j) (rad j) ⊆ A := fun j v hv => (hball n j v).2 hv
  have htr := hn (hε (n + N)) (R (n + N)) hconf
    (fun v => φ (q (n + N) v)) (hqi n) A (hA n) hball'
    (thickening δ U) _ _ _ hgeom haccess v (TimePartition.uniform L)
    (fun v => φ ((scale : ℝ) • areaCellRepresentative h (hε (n + N))
      (S.mult (ε (n + N)) ω) v)) φ W (scale : ℝ) (fun _ hv => hv) hUambient rfl (mesh := mesh) (R := R₀) (Srange := S₀)
  have hpartial := htr hmesh.le hbuffer hglobal
  have happly := fun hpoint hwrange hbrange => hpartial hpoint hwrange hbrange
    hb.le Is hIball hselected hballC hv (Subset.rfl) hφ
  have hfull := fun hpoint hwrange hbrange Wmesh diameter hdiameter hcellBuffer
      hcellMesh hstepMesh hpaper =>
    happly hpoint hwrange hbrange Wmesh diameter (NNReal.coe_nonneg scale) hdiameter
      hcellBuffer hcellMesh hstepMesh r hbudget hsmall hpaper
  exact hfull

end MatedCRT
end
