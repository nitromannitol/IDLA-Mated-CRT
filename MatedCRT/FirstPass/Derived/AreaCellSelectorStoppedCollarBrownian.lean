import MatedCRT.FirstPass.Derived.AreaCellStoppedCollarPaperTransfer

/-! # Stopped-collar comparison for an area-cell selector network -/

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

/-- A single finite selector network supports the stopped-collar comparison and
its transfer to the continuous paper path, under the stated local estimates. -/
theorem MatedCRTEnv.exists_areaCell_selector_stopped_collar_brownian
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hc_ : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (hpos : ∀ K, 0 < (areaCellConfig h hε (S.mult ε ω)).holding K)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hlfg : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlfg) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    {α : ℝ≥0} (hα : 0 < α) {W : Set Plane} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (centers : Finset Plane) (s : ℝ)
    (hballs : ∀ c ∈ centers, closedBall c s ⊆ W)
    (start : (areaCellConfig h hε (S.mult ε ω)).cells)
    (Uc : Set ℂ) (hUopen : IsOpen Uc)
    (hconv : Convex ℝ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    {m : ℝ≥0} (hm : 0 < m) (r d : ℝ) (hd : 0 ≤ d)
    (hUW : Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc ⊆ W)
    (hU : Uc ⊆ ball 0 r) (hmargin : r + (α : ℝ) * d ≤ α)
    (hdiam : ∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
      diam (cell ε (S.η ω) k) ≤ d)
    (hL : HasLipschitzBoundary (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    (hUb : Bornology.IsBounded (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))
    (μ : Measure (LatticeProb.BrownianPath 2)) [IsProbabilityMeasure μ]
    (hμ : LatticeProb.IsStandardBrownianLaw μ) {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ c > 0, ∀ a e δ : ℝ, 0 < a → 0 < e → a + e ≤ c → 0 < δ → δ ≤ c →
    ∀ T : Set (LatticeProb.Euc 2), Bornology.IsBounded T →
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) ⊆ T →
    ∀ margin : ℝ, 0 < margin →
    ∀ [MeasurableSpace (Option centers)] [MeasurableSingletonClass (Option centers)],
    ∃ n : ℕ, ∃ (V : Set (areaCellConfig h hε (S.mult ε ω)).cells) (hV : V.Finite),
    start ∈ V ∧
    (∀ v, (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ W → v ∈ V) ∧
    (∀ v, (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v ∈ W →
      ∀ w, w ∉ V → (areaCellConfig h hε (S.mult ε ω)).c v w = 0) ∧
    (∀ v : (areaCellConfig h hε (S.mult ε ω)).cells,
      ∃ w, (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) w ∉
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) ∧
        Relation.ReflTransGen
          (fun x y : (areaCellConfig h hε (S.mult ε ω)).cells =>
            0 < (areaCellConfig h hε (S.mult ε ω)).c x y) v w) ∧
    (letI := hV.fintype
     let N := finiteConductanceRestriction
       (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
         (areaCellConfig h hε (S.mult ε ω)).c v w)
       (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
       (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
       (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) V
     let p : V → Plane := fun v => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) v
     let A := p ⁻¹' W
     let U := Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc
     ∃ (hA : ∀ v ∈ A, 0 < N.totalConductance v) (q : V → Plane)
       (hB : ∀ j : centers, ∀ v ∈ q ⁻¹' ball j.val s, 0 < N.totalConductance v)
       (hinj : Function.Injective q),
       N.BoundaryAccessible A ∧
       (∀ v, ∃ x ∈ (v.1.1 : Set Plane), q v = (α : ℝ) • x) ∧
       (∀ v, dist (p v) (q v) < a) ∧
       (∀ j : centers, q ⁻¹' ball j.val s ⊆ A) ∧
       (p ⁻¹' U ⊆ A) ∧
       (let B : centers → Set V := fun j => q ⁻¹' ball j.val s
        let W : centers → Set Plane := fun j => ball j.val s
        let hballopen : ∀ j, IsOpen (W j) := fun _ => isOpen_ball
        let hUpos : ∀ v ∈ p ⁻¹' U, 0 < N.totalConductance v := fun v hv => hA v (hUW hv)
        ∀ [MeasurableSpace V] [MeasurableSingletonClass V]
    (select : ℕ → LatticeProb.Euc 2 → Option centers) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (LatticeProb.Euc 2))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    (initial : centers) (v : V) (z : LatticeProb.Euc 2) (P : TimePartition n)
    (_hv : v ∈ p ⁻¹' U)
    {mesh Rrange Srange : ℝ} (_hmesh : 0 ≤ mesh)
    (_hbuffer : a + e + mesh < δ)
    (_hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (_hnear : dist (q v) z ≤ a) (_hpoint : Rrange + a + Srange ≤ e)
    (_hwrange : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial select ω i).2 ∈ curveOscillationLe Rrange)
    (_hbrange : ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion W z initial (brownianSelectorForWalk select) i ω).2 ∈
        curveOscillationLe Srange)
    (choice : ∀ i, Fin (m i) → Option centers)
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
    (_hWT : ∀ j, W j ⊆ T) (_hzU : z ∈ U)
    (_hmargin : ∀ k x j, select k x = some j → ball x (margin / 2) ⊆ W j)
    (_hnone : ∀ k x, select k x = none → x ∉ thickening δ U)
    (_hstepMesh : 2 * ((α : ℝ) * d) ≤ mesh)
    (r₀ : ℝ≥0)
    (_hbudget : ((n + 1 : ℝ≥0∞) * ENNReal.ofReal b +
      (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
      (ENNReal.ofReal τ + (n + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤ (r₀ : ℝ≥0∞))
    (_hsmall : ENNReal.ofReal (a + e + η) < (r₀ : ℝ≥0∞)),
    μ {ω | (brownianSkeletonClock W z initial (brownianSelectorForWalk select) n ω).1 =
      false} ≤ ENNReal.ofReal τ ∧
    ∃ ρ : Measure ((ℕ → V) × C(unitInterval, LatticeProb.Euc 2)),
      IsProbabilityMeasure ρ ∧ ρ.fst = N.trajectoryLaw A hA v ∧
      ρ.map (fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial select x.1, x.2)) =
        (N.walkBrownianJointLaw q hinj B hB W hballopen μ select hs m E hE hdE initial v z).map
          (fun x => (x.1, pastedBrownianCurve P x.2)) ∧
      ρ.snd = (μ.map (fun ω k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω)).map (pastedBrownianCurve P) ∧
      levyProkhorovEDist
        ((N.trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
        (stoppedBrownianLaw U z μ) ≤ (r₀ : ℝ≥0∞) + ENNReal.ofReal τ ∧
      levyProkhorovEDist
        ((srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1)).map
          (fun x => CurveSpaceComparison.isometryEquiv 2
            (normalizedPrefixCurve
              (complexToEuclideanPath ((α : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm.le x))
              (pathExitTime Uc ((α : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm.le x)).toNNReal)))
        (stoppedBrownianLaw U z μ) ≤ ENNReal.ofReal (4 * ((α : ℝ) * d)) +
          ((r₀ : ℝ≥0∞) + ENNReal.ofReal τ))) := by
  classical
  have hUopen' : IsOpen (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) :=
    hUopen.preimage Complex.orthonormalBasisOneI.repr.symm.continuous
  obtain ⟨c, hc, hcprop⟩ :=
    S.uniform_areaCell_stopped_collar_transfer ω h hε α hm Uc d hL hUopen' hUb μ hμ hη hτ
  refine ⟨c, hc, ?_⟩
  intro a e δ ha he hae hδ hδc T hT hUT margin hmarginpos _ _
  obtain ⟨n, hn⟩ := hcprop centers a e δ (le_of_lt ha) he hae hδ hδc T hT hUT margin hmarginpos
  obtain ⟨V, hV, hs, hcontain, hretain, hpaths, hA, q, haccess, hqinj, hqcell,
    hqnear, hsel, hsub, hBpos, hUpos, hrep, hedge, hbuffer, hcellmesh, hstep, hcomparison⟩ :=
    S.exists_areaCell_selector_network_comparison_geometry ω h hε hc_ hpos hlf hlfg H hH
      hα hW hWb centers s hballs start ha Uc hUopen hconv hm r d hd hUW hU hmargin hdiam
  let : Fintype V := hV.fintype
  refine ⟨n, V, hV, hs, hcontain, hretain, hpaths, hA, q, hBpos, hqinj,
    haccess, hqcell, hqnear, hsel, hsub, ?_⟩
  dsimp only
  intro _ _ select hselectMeas m E hE hdE initial v z P hv mesh Rrange Srange hmesh hbuffer'
    hdiam' hnear hpoint hwrange hbrange choice hselect b hb hinside hcover herror hz hinit
    hWT hzU hmargin' hnone hstepMesh r₀ hbudget hsmall
  apply hn V (areaCellConfig h hε (S.mult ε ω)) hc_ _ hrep Subtype.val _ hedge q hqinj
    (fun j : centers => q ⁻¹' ball j.val s) hBpos (fun j : centers => ball j.val s)
    (fun _ => isOpen_ball) (fun _ => isBounded_ball) select hselectMeas m E hE hdE
    hsel hA haccess initial v z P _ hsub hUpos hmesh hbuffer' (fun v => le_of_lt (hqnear v)) hdiam' hnear hpoint
    hwrange hbrange choice hselect hb hinside hcover herror hz hinit hWT hzU hmargin' hnone
    id isometry_id (ball 0 (α : ℝ)) (α : ℝ) d (by exact_mod_cast hα.le) hd rfl
    hbuffer hcellmesh hstepMesh r₀ hbudget hsmall
  exact hcomparison v hv

end MatedCRT
end
