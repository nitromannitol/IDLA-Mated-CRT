import MatedCRT.FirstPass.Derived.AreaCellDUniformPackage
import MatedCRT.FirstPass.Derived.AreaCellMeshSet

/-! # Shifted area-cell transfer for a convex region, uniform in the scale, with the cell mesh discharged

The covering package of `AreaCellDUniformPackage` for a proper area parametrized curve and mesh
parameters tending to `0`: the four cell-mesh premises on the set `Wmesh` of the transfer (the
two buffer premises, the diameter bound of the cells meeting `Wmesh`, and the step bound) are
replaced by the conditions `scale * d ≤ K` and `2 * (scale * d) ≤ mesh` on the scale `d`, and the
transfer holds eventually in the mesh index, for every scale `d` with `0 < d ≤ d₀`. -/
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

/-- The covering package for the shifted area-cell transfer on a convex region, uniform in the scale,
for a proper area parametrized curve and mesh parameters `ε n → 0`: for every scale `d` with
`0 < d ≤ d₀`, `scale * d ≤ K` and `2 * (scale * d) ≤ mesh`, the transfer holds for all large indices,
without any hypothesis on a set `Wmesh` or on the diameters of the cells. -/
theorem MatedCRTEnv.exists_common_radius_package_transfer_convex_dUniform_mesh

{Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    (α : ℝ≥0) {m₀ : ℝ≥0} (hm₀ : 0 < m₀) (Uc : Set ℂ) (d₀ : ℝ)
    {U : Set (LatticeProb.Euc 2)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (LatticeProb.BrownianPath 2)) [IsProbabilityMeasure μ] (hμ : LatticeProb.IsStandardBrownianLaw μ)
    (r : ℝ≥0) (hr : 0 < r)
    (hUc : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) (hUconv : Convex ℝ U) :
  ∃ (J : Type u) (_ : Fintype J) (center : J → LatticeProb.Euc 2) (rad : J → ℝ)
      (margin rho K : ℝ) (Us Is Ks : J → Set (LatticeProb.Euc 2)) (radius : J → ℝ),
    0 < margin ∧ margin ≤ rho ∧ 0 < K ∧ 0 < rho ∧ (∀ j, rad j = rho) ∧
    (∀ j, Us j = ball (center j) (rad j)) ∧ (∀ j, ball (center j) (margin / 2) ⊆ Is j) ∧
    (∀ j, Is j ⊆ ball (center j) (rad j)) ∧ (∀ j, IsOpen (Us j)) ∧
    (∀ j, Bornology.IsBounded (Us j)) ∧ (∀ j, IsCompact (Is j)) ∧ (∀ j, Is j ⊆ Us j) ∧
    (∀ j, IsCompact (Ks j)) ∧ (∀ j, Ks j ⊆ Us j) ∧ (∀ j, 0 < radius j) ∧
    (∀ j x, x ∈ Is j → ∀ y, dist y x < radius j → y ∈ Ks j) ∧
    ∀ [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hηp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (_hlf : ∀ n, IsLocallyFiniteMult (S.mult (ε n) ω))
    (hlfg : ∀ n, MatedCRTHarmonic.MatedCRT.IsLocallyFinite (ε n) (S.bm ω))
    (H : ∀ n, CellularEmbedding
      (MatedCRTHarmonic.MatedCRT.graph (ε n) (S.bm ω) (hlfg n)) (0 : ℤ))
    (_hH : ∀ n, (H n).cell = cell (ε n) (S.η ω))
    {scale : ℝ≥0} (_hscale : 0 < scale) {U₀ W : Set Plane} (_hUW : U₀ ⊆ W)
    (_hW : Bornology.IsBounded W)
    (t : ℕ → ℝ) (_ht : ∀ n, 0 < t n) (_ht0 : Filter.Tendsto t Filter.atTop (𝓝 0))
    (φ : Plane → LatticeProb.Euc 2) (_hφ : Isometry φ)
    {O : Set (LatticeProb.Euc 2)} (_hO : IsOpen O)
    (_hKO : ∀ j, Metric.closedBall (center j) (rad j) ⊆ O) (_hOW : φ ⁻¹' O ⊆ W)
    (_hφid : φ = id) (_hscale_eq : scale = α),
    ∃ (η τ c a e δ₀ mesh : ℝ) (C : Set (LatticeProb.Euc 2)),
      0 < η ∧ 0 < τ ∧ 0 < c ∧ 0 < a ∧ 0 < e ∧ 0 < δ₀ ∧ 0 < mesh ∧
      a + e ≤ c ∧ δ₀ ≤ c ∧ a + e + mesh < δ₀ ∧
      ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞) ∧ IsCompact C ∧
      thickening δ₀ U ⊆ C ∧
      thickening δ₀ U ⊆ ⋃ j, ball (center j) (margin / 4) ∧
      (∀ j, closure (ball (center j) (rad j)) ⊆ C) ∧
      4 * rho + 3 * a + 2 * K ≤ e ∧
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
    (d : ℝ) (_hdd : d ≤ d₀)
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
      (∀ n (v : (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).cells),
        (scale : ℝ) • areaCellRepresentative h (hε (n + N)) (S.mult (ε (n + N)) ω) v ∈ W →
        ∀ w, w ∉ R (n + N) →
          (areaCellConfig h (hε (n + N)) (S.mult (ε (n + N)) ω)).c v w = 0) ∧
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
    (∀ d : ℝ, 0 < d → d ≤ d₀ → (scale : ℝ) * d ≤ K → 2 * ((scale : ℝ) * d) ≤ mesh →
      ∀ᶠ n in atTop, ∀ (v : Rset n), q' n v ∈ U →
      ∃ (hinj : Function.Injective (q' n))
        (hs : ∀ i, Measurable (cellSelector (E i) (choice i)))
        (hE : ∀ i k, MeasurableSet (E i k))
        (hdE : ∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l)))
        (hUpos : ∀ w ∈ p n ⁻¹' U, 0 < (net n).totalConductance w),
      let B := fun j => q' n ⁻¹' ball (center j) (rad j)
      let hB := fun j w hw => hA n w ((hball n j w).2 hw)
      let Wj := fun j => ball (center j) (rad j)
      let hWj : ∀ j, IsOpen (Wj j) := fun _ => isOpen_ball
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
)
 := by
  classical
  have hpkg := MatedCRTEnv.exists_common_radius_package_transfer_convex_dUniform.{u}
    S ω h α hm₀ Uc d₀ hL hU hUb μ hμ r hr hUc hUconv
  obtain ⟨J, hJ, center, rad, margin, rho, K, Us, Is, Ks, radius, p1, p2, p3, p4, p5, p6, p7, p8,
    p9, p10, p11, p12, p13, p14, p15, p16, hrest⟩ := hpkg
  refine ⟨J, hJ, center, rad, margin, rho, K, Us, Is, Ks, radius, p1, p2, p3, p4, p5, p6, p7, p8,
    p9, p10, p11, p12, p13, p14, p15, p16, ?_⟩
  intro _ _ ε hε hε0 hηp _hlf hlfg H _hH scale _hscale U₀ W _hUW _hW t _ht _ht0 φ _hφ O _hO _hKO
    _hOW _hφid _hscale_eq
  obtain ⟨η, τ, c, a, e, δ₀, mesh, C, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14,
    q15, q16, L, b, hbb, htr, R, hR, q, N, c1, c2, c3, c4, c5, c6, hlet⟩ :=
    hrest ε hε _hlf hlfg H _hH _hscale _hUW _hW t _ht _ht0 φ _hφ _hO _hKO _hOW _hφid _hscale_eq
  refine ⟨η, τ, c, a, e, δ₀, mesh, C, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14,
    q15, q16, L, b, hbb, htr, R, hR, q, N, c1, c2, c3, c4, c5, c6, ?_⟩
  obtain ⟨hA, hball, hmain⟩ := hlet
  refine ⟨hA, hball, ?_⟩
  intro href hosc hinner hR' hUball' hIball'
  obtain ⟨m, E, δ, choice, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, hlet2⟩ :=
    hmain href hosc hinner hR' hUball' hIball'
  refine ⟨m, E, δ, choice, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, ?_⟩
  obtain ⟨hgeom, hcpl, hlast⟩ := hlet2
  refine ⟨hgeom, hcpl, ?_⟩
  intro d hd hdd hK hmesh
  subst _hφid
  have hε' : ∀ n, 0 < ε (n + N) := fun n => hε (n + N)
  have hε0' : Tendsto (fun n => ε (n + N)) atTop (𝓝 0) := (tendsto_add_atTop_iff_nat N).2 hε0
  have hU1b : Bornology.IsBounded (U ∪ ⋃ j, ball (center j) (rho + a) : Set ReflectedGMS.Plane) :=
    hUb.union (Bornology.isBounded_iUnion.2 fun j => Metric.isBounded_ball)
  obtain ⟨Wm, -, hsub, hev⟩ := exists_meshSet_eventually_diam_cell_le h hηp hε' hε0'
    (fun n => S.mult (ε (n + N)) ω) hU1b (scale := (scale : ℝ)) (NNReal.coe_pos.2 _hscale) hd
  filter_upwards [hlast, hev] with n h1 h2 v hv
  obtain ⟨hinj, hs, hE, hdE, hUpos, hrest'⟩ := h1 v hv
  refine ⟨hinj, hs, hE, hdE, hUpos, ?_⟩
  exact hrest' d hdd hd.le Wm hK (fun x hx => hsub x (Or.inl hx))
    (fun x hx => hsub x (Or.inr hx)) h2 hmesh

end MatedCRT
