import MatedCRT.FirstPass.Derived.AreaCellStoppedCollarPaperTransfer
import MatedCRT.FirstPass.Derived.AreaCellStoppedPathExitCurve
import LatticeProb.Walk.AccessibleRestrictedPrefixCurveLaw
import LatticeProb.Walk.StoppedCurveRelabel
import MatedCRT.FirstPass.Derived.AreaCellNonisolated

/-! # Diameter-controlled curve comparison for accessible restricted cell walks -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ProbabilityTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open MatedCRTHarmonic.Markov LatticeProb _root_.HarmonicBalls
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open BouRabeeGwynne.FiniteConductanceNetwork
open LatticeProb.CellConfigInterpolation
open scoped NNReal ENNReal

/-- Boundary accessibility passes to subsets of the active set. -/
theorem boundaryAccessible_mono {V : Type*} [Fintype V] (N : BouRabeeGwynne.FiniteConductanceNetwork V)
    {A A' : Set V} (hA : N.BoundaryAccessible A) (hsub : A' ⊆ A) :
    N.BoundaryAccessible A' := fun v hv => by
  obtain ⟨w, hw, hr⟩ := hA v (hsub hv)
  exact ⟨w, fun hw' => hw (hsub hw'), hr⟩

/-- Two cells that are adjacent in a cell configuration, the first of which has its scaled
representative in `U`, lie in the mesh region: both have diameter at most `d`. -/
theorem cell_diam_pair_le (H : CellConfig) (hH : H.IsCellConfiguration)
    (rep : H.cells → Plane) (hrep : ∀ C, rep C ∈ (C.1 : Set Plane))
    {α d : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d) (U Wmesh : Set Plane)
    (hbuf : ∀ x ∈ U, closedBall x (α * d) ⊆ Wmesh)
    (hmesh : ∀ C : H.cells, (∃ z ∈ (C.1 : Set Plane), α • z ∈ Wmesh) →
      Metric.diam (C.1 : Set Plane) ≤ d)
    (K K' : H.cells) (hK : α • rep K ∈ U) (hadj : H.Adj K K') :
    Metric.diam (K.1 : Set Plane) ≤ d ∧ Metric.diam (K'.1 : Set Plane) ≤ d := by
  have h1 : Metric.diam (K.1 : Set Plane) ≤ d :=
    hmesh K ⟨rep K, hrep K, hbuf _ hK (mem_closedBall_self (mul_nonneg hα hd))⟩
  refine ⟨h1, hmesh K' ?_⟩
  obtain ⟨z, hzK, hzK'⟩ := hH.adj_inter _ _ hadj
  refine ⟨z, hzK', hbuf _ hK ?_⟩
  rw [mem_closedBall, dist_smul₀, Real.norm_of_nonneg hα]
  exact mul_le_mul_of_nonneg_left
    ((Metric.dist_le_diam_of_mem K.1.isCompact.isBounded hzK (hrep K)).trans h1) hα

/-- **Diameter-controlled comparison.** For an accessible restricted cell walk started in the
active region, the continuous exit curve is within `4 ε d` (plus the source distance) of the
target law, when every cell met by a step across the exit has diameter at most `d`. -/
theorem levyProkhorov_continuousExitCurve_le_of_accessible_restricted_prefix_diam
    (H : CellConfig)
    [Countable H.cells] [MeasurableSpace H.cells] [MeasurableSingletonClass H.cells]
    (hH : H.IsCellConfiguration)
    (hsymm : ∀ v w : H.cells, H.c v w = H.c w v)
    (hnonneg : ∀ v w : H.cells, 0 ≤ H.c v w)
    (hloop : ∀ v : H.cells, H.c v v = 0)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (hpos : ∀ K, 0 < H.holding K) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m)
    {U : Set Plane} (hU : IsOpen U) (hconv : Convex ℝ U)
    (R : Set H.cells) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (A : Set R)
    (hAB : ∀ v : R, v ∈ A ↔ (ε : ℝ) • p v ∈ U)
    (hA : ∀ v ∈ A, 0 < (finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).totalConductance v)
    (haccess : (finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).BoundaryAccessible A)
    (v : R) (hv : v ∈ A) {Wmesh : Set Plane} {d : ℝ} (hd : 0 ≤ d)
    (hbuf : ∀ x ∈ U, closedBall x ((ε : ℝ) * d) ⊆ Wmesh)
    (hmesh : ∀ C : H.cells, (∃ z ∈ (C.1 : Set Plane), (ε : ℝ) • z ∈ Wmesh) →
      Metric.diam (C.1 : Set Plane) ≤ d)
    (ν : Measure (BouRabeeGwynne.CurveSpace 2)) (s : ℝ≥0)
    (hsource : levyProkhorovEDist
      ((((finiteConductanceRestriction
        (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw A hA v).map
        (fun q n => (q n : H.cells))).map
        (stoppedPolygonalCurve (fun K => (ε : ℝ) • p K)
          {K : H.cells | (ε : ℝ) • p K ∈ U})) ν ≤ (s : ℝ≥0∞)) :
    levyProkhorovEDist
      ((((finiteConductanceRestriction
        (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw A hA v).map
        (fun q n => (q n : H.cells))).map (fun ω : ℕ → H.cells =>
        let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
        CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve g (LatticeProb.continuousExitTime U 0 g).toNNReal))) ν ≤
      ENNReal.ofReal (4 * ((ε : ℝ) * d)) + (s : ℝ≥0∞) := by
  classical
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  set r : ℝ≥0 := (4 * ((ε : ℝ) * d)).toNNReal + δ with hr
  have hlt : ENNReal.ofReal (4 * ((ε : ℝ) * d)) < (r : ℝ≥0∞) := by
    rw [hr, ENNReal.coe_add]
    exact ENNReal.lt_add_right ENNReal.ofReal_ne_top (by exact_mod_cast hδ.ne')
  have key := levyProkhorov_continuousExitCurve_le_of_accessible_restricted_prefix H hH hsymm
    hnonneg hloop p hp hpos hε hm hU hconv R A hAB hA haccess v _ rfl ∅ r s (by simp) ?_ ν hsource
  · refine key.trans (le_of_eq ?_)
    rw [hr, ENNReal.coe_add]
    simp only [ENNReal.ofReal]
    ring
  · have hmeas : MeasurableSet {ω : ℕ → H.cells | ω ∉ (∅ : Set (ℕ → H.cells)) →
        (ε : ℝ) • p (ω 0) ∈ U ∧ ∀ n : ℕ,
          MatedCRTHarmonic.Markov.hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω =
            ((n + 1 : ℕ) : WithTop ℕ) →
          ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
            Metric.diam ((ω (n + 1)).1 : Set Plane)))) < (r : ℝ≥0∞)} := by
      have hS : MeasurableSet {K : H.cells | (ε : ℝ) • p K ∉ U} := MeasurableSet.of_discrete
      have hht := MatedCRTHarmonic.Markov.measurable_hitTime hS
      simp only [mem_empty_iff_false, not_false_eq_true, true_imp_iff]
      rw [Set.ofPred_and]
      refine MeasurableSet.inter ?_ ?_
      · exact (measurable_pi_apply (X := fun _ : ℕ => H.cells) 0)
          (MeasurableSet.of_discrete (s := {K : H.cells | (ε : ℝ) • p K ∈ U}))
      · rw [Set.ofPred_forall]
        refine MeasurableSet.iInter fun n => ?_
        have e : {ω : ℕ → H.cells |
            MatedCRTHarmonic.Markov.hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω =
              ((n + 1 : ℕ) : WithTop ℕ) →
            ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
              Metric.diam ((ω (n + 1)).1 : Set Plane)))) < (r : ℝ≥0∞)} =
            {ω : ℕ → H.cells | MatedCRTHarmonic.Markov.hitTime
              {K : H.cells | (ε : ℝ) • p K ∉ U} ω = ((n + 1 : ℕ) : WithTop ℕ)}ᶜ ∪
            {ω : ℕ → H.cells | ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
              Metric.diam ((ω (n + 1)).1 : Set Plane)))) < (r : ℝ≥0∞)} := by
          ext ω; simp [imp_iff_not_or]
        rw [e]
        refine MeasurableSet.union (MeasurableSet.compl ?_) ?_
        · exact hht (measurableSet_singleton _)
        · have g : Measurable (fun K : H.cells => Metric.diam (K.1 : Set Plane)) :=
            measurable_of_countable _
          have hm : Measurable (fun ω : ℕ → H.cells => ENNReal.ofReal (2 * ((ε : ℝ) *
              (Metric.diam ((ω n).1 : Set Plane) + Metric.diam ((ω (n + 1)).1 : Set Plane))))) :=
            ENNReal.measurable_ofReal.comp
              (measurable_const.mul (measurable_const.mul
                ((g.comp (measurable_pi_apply n)).add (g.comp (measurable_pi_apply (n + 1))))))
          exact hm measurableSet_Iio
    have hf : Measurable (fun (q : ℕ → R) (n : ℕ) => (q n : H.cells)) :=
      measurable_pi_iff.2 fun n =>
        (measurable_of_countable (Subtype.val : R → H.cells)).comp (measurable_pi_apply n)
    refine (ae_map_iff hf.aemeasurable hmeas).2 ?_
    filter_upwards [FiniteConductanceNetwork.trajectoryLaw_ae_start _ A hA v,
      FiniteConductanceNetwork.trajectoryLaw_ae_edge_or_constant _ A hA v] with q hq0 hedge
    intro _
    refine ⟨?_, fun n hn => ?_⟩
    · show (ε : ℝ) • p (q 0 : H.cells) ∈ U
      rw [hq0]
      exact (hAB v).1 hv
    · obtain ⟨hn1, hn0⟩ := MatedCRTHarmonic.Markov.hitTime_eq_coe_iff.1 hn
      have hqn : q n ∈ A := (hAB _).2 (by simpa using hn0 n (Nat.lt_succ_self n))
      have hqn1 : q (n + 1) ∉ A := fun h => hn1 ((hAB _).1 h)
      have hne : q (n + 1) ≠ q n := fun h => hqn1 (h ▸ hqn)
      have hadj : H.Adj (q n : H.cells) (q (n + 1) : H.cells) := by
        rcases hedge n with h1 | h1
        · exact h1
        · exact absurd h1 hne
      obtain ⟨d1, d2⟩ := cell_diam_pair_le H hH p hp ε.2 hd U Wmesh hbuf hmesh _ _
        ((hAB _).1 hqn) hadj
      refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hlt
      calc _ ≤ 2 * ((ε : ℝ) * (d + d)) := by gcongr
        _ = 4 * ((ε : ℝ) * d) := by ring

/-- The finite restriction of the area-cell network to a finite set of cells. -/
abbrev MatedCRTEnv.areaCellRestriction {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ω : Ω) {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (V : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype V] :
    BouRabeeGwynne.FiniteConductanceNetwork V :=
  LatticeProb.finiteConductanceRestriction
    (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
    (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
    (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
    (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) V

/-- A constant vertex path starting outside the open region `U` has the same stopped polygonal
curve and continuous exit curve: both are the constant curve at its position. -/
theorem exitCurve_eq_stopped_of_const_start {X : Type*} (pos : X → EuclideanSpace ℝ (Fin 2))
    (a m : ℝ) (U : Set (EuclideanSpace ℝ (Fin 2))) (x : X) (hx : a • pos x ∉ U) :
    CurveSpaceComparison.isometryEquiv 2
      (normalizedPrefixCurve
        (ConstantStepInterpolation.continuousPlanePath m (fun _ : ℕ => a • pos x))
        (LatticeProb.continuousExitTime U 0
          (ConstantStepInterpolation.continuousPlanePath m (fun _ : ℕ => a • pos x))).toNNReal) =
    stoppedPolygonalCurve (fun K => a • pos K) {K | a • pos K ∈ U} (fun _ : ℕ => x) := by
  have hg0 : ConstantStepInterpolation.continuousPlanePath m (fun _ : ℕ => a • pos x) 0 =
      a • pos x := constantStepPath_knot (fun _ : ℕ => a • pos x) 0 0 (by simp)
  have hT : LatticeProb.continuousExitTime U 0
      (ConstantStepInterpolation.continuousPlanePath m (fun _ : ℕ => a • pos x)) = 0 := by
    unfold LatticeProb.continuousExitTime
    refine le_antisymm ?_ bot_le
    exact iInf_le_of_le ⟨0, by simpa [hg0] using hx⟩ (by simp)
  have hpre : normalizedPathPrefix
      (ConstantStepInterpolation.continuousPlanePath m (fun _ : ℕ => a • pos x)) 0 =
      ContinuousMap.const _ (a • pos x) := by
    refine ContinuousMap.ext fun u => ?_
    have hz : (⟨(u : ℝ) * ((0 : ℝ≥0) : ℝ), mul_nonneg u.property.1 (0 : ℝ≥0).property⟩ : ℝ≥0) =
        0 := Subtype.ext (by simp)
    show ConstantStepInterpolation.continuousPlanePath m (fun _ : ℕ => a • pos x)
      ⟨(u : ℝ) * ((0 : ℝ≥0) : ℝ), mul_nonneg u.property.1 (0 : ℝ≥0).property⟩ = a • pos x
    rw [hz]
    exact hg0
  have hexit : FiniteConductanceNetwork.exitTime {K | a • pos K ∈ U} (fun _ : ℕ => x) = 0 :=
    FiniteConductanceNetwork.exitTime_eq_zero_of_not_mem hx
  rw [hT]
  simp only [ENNReal.toNNReal_zero, normalizedPrefixCurve, hpre, stoppedPolygonalCurve, hexit]
  simp

/-- **Paper comparison for a convex region.** The finite-prefix comparison of a restricted
area-cell walk with the Brownian law transfers to the integer walk with the paper's normalized
exit curve, for a convex open region and cells of diameter at most `d` near it. -/
theorem MatedCRTEnv.areaCell_paperComparison_convex
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hH : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (α : ℝ≥0) (hα : 0 < α) {m₀ : ℝ≥0} (hm₀ : 0 < m₀)
    (Uc : Set ℂ) (d : ℝ) (hd : 0 ≤ d)
    {U : Set (LatticeProb.Euc 2)} (hUc : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)
    (hUo : IsOpen U) (hUconv : Convex ℝ U)
    (V : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (hretain : ∀ x : V, (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1 ∈ U →
      ∀ w, w ∉ V → (areaCellConfig h hε (S.mult ε ω)).c x.1 w = 0)
    (p : V → LatticeProb.Euc 2)
    (hp : p = fun x : V => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1)
    (hUpos : ∀ v ∈ p ⁻¹' U, 0 < (S.areaCellRestriction ω h hε V).totalConductance v)
    (haccess : (S.areaCellRestriction ω h hε V).BoundaryAccessible (p ⁻¹' U))
    (Wmesh : Set Plane)
    (hcellBuffer : ∀ x ∈ U, Metric.closedBall x ((α : ℝ) * d) ⊆ Wmesh)
    (hcellMesh : ∀ C : (areaCellConfig h hε (S.mult ε ω)).cells,
      (∃ z ∈ (C.1 : Set Plane), (α : ℝ) • z ∈ Wmesh) → Metric.diam (C.1 : Set Plane) ≤ d)
    (v : V) :
    ∀ (ν : Measure (BouRabeeGwynne.CurveSpace 2)) (s₀ : ℝ≥0) (τ₀ : ℝ),
      levyProkhorovEDist
        (((S.areaCellRestriction ω h hε V).trajectoryLaw (p ⁻¹' U) hUpos v).map
          (stoppedPolygonalCurve p (p ⁻¹' U))) ν ≤ (s₀ : ℝ≥0∞) + ENNReal.ofReal τ₀ →
      levyProkhorovEDist
        ((srwLaw (S.mult ε ω) ((euclideanCellEquiv h hε).symm v.1)).map
          (fun x => CurveSpaceComparison.isometryEquiv 2
            (normalizedPrefixCurve
              (complexToEuclideanPath ((α : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm₀.le x))
              (pathExitTime Uc ((α : ℝ) • interpPathCM (vertexPoint ε (S.η ω)) hm₀.le x)).toNNReal)))
        ν ≤ ENNReal.ofReal (4 * ((α : ℝ) * d)) + ((s₀ : ℝ≥0∞) + ENNReal.ofReal τ₀) := by
  classical
  subst hUc
  subst hp
  intro ν s₀ τ₀ hL1
  have : Countable (areaCellConfig h hε (S.mult ε ω)).cells :=
    Countable.of_equiv ℤ (euclideanCellEquiv h hε)
  have hholding := LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hH
    (S.areaCellConfig_exists_adj ω h hε)
  have hUcOpen : IsOpen Uc := by
    have e : Uc = Complex.orthonormalBasisOneI.repr ⁻¹'
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) := by
      ext z; simp
    rw [e]
    exact hUo.preimage Complex.orthonormalBasisOneI.repr.continuous
  have hsrc :
      (((S.areaCellRestriction ω h hε V).trajectoryLaw
        ((fun x : V => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1) ⁻¹'
          (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) hUpos v).map
        (fun q n => (q n : (areaCellConfig h hε (S.mult ε ω)).cells))).map
        (stoppedPolygonalCurve (fun K => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) K)
          {K | (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) K ∈
            Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc}) =
      ((S.areaCellRestriction ω h hε V).trajectoryLaw
        ((fun x : V => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1) ⁻¹'
          (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) hUpos v).map
        (stoppedPolygonalCurve
          (fun x : V => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1)
          ((fun x : V => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1) ⁻¹'
            (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc))) :=
    (map_stoppedPolygonalCurve_relabel _
      (fun K => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) K) Subtype.val
      {K | (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) K ∈
        Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc}).symm
  have hcoe : ((s₀ + τ₀.toNNReal : ℝ≥0) : ℝ≥0∞) = (s₀ : ℝ≥0∞) + ENNReal.ofReal τ₀ := by
    rw [ENNReal.coe_add]; rfl
  have hP1 := areaCell_finite_sourceContinuousExitCurve_law_unstopped S ω h hε hlf V
    ((fun x : V => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1) ⁻¹'
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) hretain hUpos v
    (m := (m₀ : ℝ)) (by exact_mod_cast hm₀) (α : ℝ) hUcOpen (fun x hx => hx)
  by_cases hv : v ∈ (fun x : V => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1) ⁻¹'
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)
  · have hsource := hsrc.symm ▸ hL1
    have key := levyProkhorov_continuousExitCurve_le_of_accessible_restricted_prefix_diam
      (areaCellConfig h hε (S.mult ε ω)) hH
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω))
      (areaCellRepresentative h hε (S.mult ε ω))
      (fun K => areaCellRepresentative_mem h hε (S.mult ε ω) K) hholding hα hm₀ hUo hUconv V
      ((fun x : V => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1) ⁻¹'
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) (fun _ => Iff.rfl) hUpos haccess v hv hd
      hcellBuffer hcellMesh ν (s₀ + τ₀.toNNReal) (by rw [hcoe]; exact hsource)
    rw [hcoe] at key
    exact (congrArg (fun μ => levyProkhorovEDist μ ν) hP1.symm).trans_le key
  · have hcoeM : Measurable (fun (q : ℕ → V) (n : ℕ) =>
        (q n : (areaCellConfig h hε (S.mult ε ω)).cells)) :=
      measurable_pi_iff.2 fun n =>
        (measurable_of_countable
          (fun x : V => (x : (areaCellConfig h hε (S.mult ε ω)).cells))).comp
          (measurable_pi_apply n)
    have hstart := (S.areaCellRestriction ω h hε V).trajectoryLaw_ae_start _ hUpos v
    have hall := ae_all_iff.2
      (fun n => (S.areaCellRestriction ω h hε V).trajectoryLaw_ae_absorbing_step _ hUpos v n)
    have hconstT : ∀ᵐ γ ∂((S.areaCellRestriction ω h hε V).trajectoryLaw _ hUpos v),
        ∀ n, γ n = v := by
      filter_upwards [hstart, hall] with γ h0 hs
      intro n
      induction n with
      | zero => exact h0
      | succ k ih => rw [hs k (by rw [ih]; exact hv), ih]
    have hconstM : ∀ᵐ γ ∂(((S.areaCellRestriction ω h hε V).trajectoryLaw _ hUpos v).map
        (fun (q : ℕ → V) (n : ℕ) => (q n : (areaCellConfig h hε (S.mult ε ω)).cells))),
        ∀ n, γ n = (v : (areaCellConfig h hε (S.mult ε ω)).cells) := by
      have hms : MeasurableSet {γ : ℕ → (areaCellConfig h hε (S.mult ε ω)).cells |
          ∀ n, γ n = (v : (areaCellConfig h hε (S.mult ε ω)).cells)} := by
        have e : {γ : ℕ → (areaCellConfig h hε (S.mult ε ω)).cells |
            ∀ n, γ n = (v : (areaCellConfig h hε (S.mult ε ω)).cells)} =
            ⋂ n, (fun γ : ℕ → (areaCellConfig h hε (S.mult ε ω)).cells => γ n) ⁻¹'
              {(v : (areaCellConfig h hε (S.mult ε ω)).cells)} := by
          ext γ; simp
        rw [e]
        exact MeasurableSet.iInter fun n => (measurable_pi_apply n) (measurableSet_singleton _)
      rw [ae_map_iff hcoeM.aemeasurable hms]
      filter_upwards [hconstT] with γ hγ n
      exact congrArg Subtype.val (hγ n)
    refine le_trans (le_of_eq ?_) (hL1.trans le_add_self)
    congr 1
    refine hP1.symm.trans (Eq.trans ?_ hsrc)
    refine Measure.map_congr ?_
    filter_upwards [hconstM] with γ hγ
    have e : γ = fun _ => (v : (areaCellConfig h hε (S.mult ε ω)).cells) := funext hγ
    subst e
    exact exitCurve_eq_stopped_of_const_start (areaCellRepresentative h hε (S.mult ε ω))
      (α : ℝ) (m₀ : ℝ) _ (v : (areaCellConfig h hε (S.mult ε ω)).cells) hv


universe u

/-- **Stopped-collar transfer to the paper path for a convex region**: the transfer theorem for
the area-cell network, with the paper comparison hypothesis proved for a convex region. -/
theorem MatedCRTEnv.uniform_areaCell_stopped_collar_transfer_convex
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hH : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (α : ℝ≥0) (hα : 0 < α) {m₀ : ℝ≥0} (hm₀ : 0 < m₀) (Uc : Set ℂ) (d : ℝ) (hd : 0 ≤ d)
    {U : Set (LatticeProb.Euc 2)} (hUc : U = Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)
    (hUconv : Convex ℝ U) (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (LatticeProb.BrownianPath 2)) [IsProbabilityMeasure μ] (hμ : LatticeProb.IsStandardBrownianLaw μ)
    {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ c > 0, ∀ (J : Type u) [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)],
    ∀ a e δ : ℝ, 0 ≤ a → 0 < e → a + e ≤ c → 0 < δ → δ ≤ c →
    ∀ T : Set (LatticeProb.Euc 2), Bornology.IsBounded T → U ⊆ T → ∀ margin : ℝ, 0 < margin →
    ∃ n : ℕ, ∀ (V : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (q : V → LatticeProb.Euc 2) (hinj : Function.Injective q)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < (S.areaCellRestriction ω h hε V).totalConductance v)
    (W : J → Set (LatticeProb.Euc 2)) (hW : ∀ j, IsOpen (W j))
    (_hWb : ∀ j, Bornology.IsBounded (W j))
    (select : ℕ → LatticeProb.Euc 2 → Option J) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (LatticeProb.Euc 2))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    {A : Set V} (_hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < (S.areaCellRestriction ω h hε V).totalConductance v) (_haccess : (S.areaCellRestriction ω h hε V).BoundaryAccessible A)
    (initial : J) (v : V) (z : LatticeProb.Euc 2) (P : TimePartition n)
    (p : V → LatticeProb.Euc 2)
    (_hsub : p ⁻¹' U ⊆ A) (hUpos : ∀ v ∈ p ⁻¹' U, 0 < (S.areaCellRestriction ω h hε V).totalConductance v)
    {mesh R Srange : ℝ} (_hmesh : 0 ≤ mesh)
    (_hbuffer : a + e + mesh < δ) (_hpq : ∀ v, dist (p v) (q v) ≤ a)
    (_hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (_hnear : dist (q v) z ≤ a) (_hpoint : R + a + Srange ≤ e)
    (_hwrange : ∀ᵐ ω ∂(S.areaCellRestriction ω h hε V).trajectoryLaw A hA v, ∀ i,
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
      |((((S.areaCellRestriction ω h hε V).discreteHarmonicMeasure (B j) (hB j) w).map q) (E (i + 1) l)).toReal -
        (((stoppedBrownianLaw (W j) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E (i + 1) l)).toReal| ≤
          b / (m (i + 1) + 1))
    (_hz : z ∈ W initial)
    (_hinit : ∀ i, |((((S.areaCellRestriction ω h hε V).discreteHarmonicMeasure (B initial) (hB initial) v).map q)
      (E 0 i)).toReal - (((stoppedBrownianLaw (W initial) z μ).map BouRabeeGwynne.CurveSpace.endPoint)
        (E 0 i)).toReal| ≤ b / (m 0 + 1))
    (_hWT : ∀ j, W j ⊆ T) (_hzU : z ∈ U)
    (_hmargin : ∀ k x j, select k x = some j → ball x (margin / 2) ⊆ W j)
    (_hnone : ∀ k x, select k x = none → x ∉ thickening δ U)
    (Wmesh : Set Plane)
    (_hp : p = fun x : V => (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1)
    (_hcellBuffer : ∀ x ∈ U, Metric.closedBall x ((α : ℝ) * d) ⊆ Wmesh)
    (_hcellMesh : ∀ C : (areaCellConfig h hε (S.mult ε ω)).cells,
      (∃ z ∈ (C.1 : Set Plane), (α : ℝ) • z ∈ Wmesh) → Metric.diam (C.1 : Set Plane) ≤ d)
    (_hstepMesh : 2 * ((α : ℝ) * d) ≤ mesh)
    (_hretain : ∀ x : V, (α : ℝ) • areaCellRepresentative h hε (S.mult ε ω) x.1 ∈ U →
      ∀ w, w ∉ V → (areaCellConfig h hε (S.mult ε ω)).c x.1 w = 0)
    (r : ℝ≥0)
    (_hbudget : ((n + 1 : ℝ≥0∞) * ENNReal.ofReal b +
      (ENNReal.ofReal τ + ENNReal.ofReal τ)) +
      (ENNReal.ofReal τ + (n + 1 : ℝ≥0∞) * ENNReal.ofReal b) ≤ (r : ℝ≥0∞))
    (_hsmall : ENNReal.ofReal (a + e + η) < (r : ℝ≥0∞)),
    μ {ω | (brownianSkeletonClock W z initial (brownianSelectorForWalk select) n ω).1 =
      false} ≤ ENNReal.ofReal τ ∧
    ∃ ρ : Measure ((ℕ → V) × C(unitInterval, LatticeProb.Euc 2)),
      IsProbabilityMeasure ρ ∧ ρ.fst = (S.areaCellRestriction ω h hε V).trajectoryLaw A hA v ∧
      ρ.map (fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
        q B initial select x.1, x.2)) =
        ((S.areaCellRestriction ω h hε V).walkBrownianJointLaw q hinj B hB W hW μ select hs m E hE hdE initial v z).map
          (fun x => (x.1, pastedBrownianCurve P x.2)) ∧
      ρ.snd = (μ.map (fun ω k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω)).map (pastedBrownianCurve P) ∧
      levyProkhorovEDist
        (((S.areaCellRestriction ω h hε V).trajectoryLaw (p ⁻¹' U) hUpos v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
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
    uniform_vertex_cellNetwork_stopped_collar_brownian_all_indices hL hU hUb μ hμ hη hτ
  refine ⟨c, hc, ?_⟩
  intro J _ _ _ a e δ ha he hae hδ hδc T hT hUT margin hmarginpos
  obtain ⟨n, hn⟩ := hcprop J a e δ ha he hae hδ hδc T hT hUT margin hmarginpos
  refine ⟨n, ?_⟩
  intro V _ _ _ q hinj B hB W hW hWb select hs m E hE hdE A hBA hA haccess
    initial v z P p hsub hUpos mesh R S₀ hmesh hbuffer hpq hdiam hnear hpoint
    hwrange hbrange choice hselect b hb hinside hcover herror hz hinit hWT hzU
    hmargin hnone Wmesh hp hcellBuffer hcellMesh hstepMesh hretain r hbudget hsmall
  obtain ⟨htail, ρ, hρprob, hρfst, hρjoint, hρsnd, hcomparison⟩ :=
    hn V (areaCellConfig h hε (S.mult ε ω)) hH (areaCellRepresentative h hε (S.mult ε ω))
      (fun C => areaCellRepresentative_mem h hε (S.mult ε ω) C) Subtype.val
      (S.areaCellRestriction ω h hε V) (fun _ _ hvw => hvw) q hinj B hB W hW hWb select hs m E hE
      hdE hBA hA haccess initial v z P p hsub hUpos hmesh hbuffer hpq hdiam hnear
      hpoint hwrange hbrange choice hselect hb hinside hcover herror hz hinit hWT
      hzU hmargin hnone id isometry_id Wmesh (α : ℝ) d α.2 hd hp hcellBuffer
      hcellMesh hstepMesh r hbudget hsmall
  exact ⟨htail, ρ, hρprob, hρfst, hρjoint, hρsnd, hcomparison,
    S.areaCell_paperComparison_convex ω h hε hlf hH α hα hm₀ Uc d hd hUc hU hUconv V hretain p hp
      hUpos (boundaryAccessible_mono _ haccess hsub) Wmesh hcellBuffer hcellMesh v
      (stoppedBrownianLaw U z μ) r τ hcomparison⟩

end MatedCRT
end
