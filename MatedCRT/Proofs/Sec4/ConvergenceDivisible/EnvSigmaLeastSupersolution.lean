import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EnvSigmaEdge
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LaplacianMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MatedLeastMeasurable
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentCells
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentGreen

/-! # Environmental measurability of the mated discrete least supersolution

The σ-algebra-generic measurability chain of `SupersolutionMeasurable.lean` and `FiniteApproximation.lean`,
with the multigraph given by measurable data `M : Ω → ℤ → ℤ → ℕ`, and the `σ(h, η)`-measurable version
`MatedCRTEnv.IsValid.exists_envSigma_measurable_matedLeastSupersolution` of the rescaled obstacle problem
(input E-m4-1). The envSigma inputs are the edge multiplicities and cell and obstacle data of
`EnvSigmaEdge.lean`, `EnvironmentCells.lean` and `EnvironmentGreen.lean`. -/

namespace MatedCRT

open Set MeasureTheory Filter Topology Metric

/-- The set of `ω` at which a family of measurable memberships `P ω c` (indexed by `c : ℤ`) is finite. -/
theorem ls_measurableSet_finite_setOf {Ω : Type} [MeasurableSpace Ω] (P : Ω → ℤ → Prop)
    (hP : ∀ c, MeasurableSet {ω | P ω c}) : MeasurableSet {ω | {c | P ω c}.Finite} := by
  have heq : {ω | {c | P ω c}.Finite} =
      ⋃ N : ℕ, ⋂ c : ℤ, ({ω | P ω c}ᶜ ∪ {_ω | -(N : ℤ) ≤ c ∧ c ≤ (N : ℤ)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, mem_union, mem_compl_iff]
    constructor
    · intro hfin
      obtain ⟨N, hN⟩ := (hfin.image (fun c : ℤ => c.natAbs)).bddAbove
      refine ⟨N, fun c => ?_⟩
      by_cases hc : P ω c
      · right
        have h1 : c.natAbs ≤ N := hN ⟨c, hc, rfl⟩
        rcases Int.natAbs_eq c with h | h <;> constructor <;> omega
      · exact Or.inl hc
    · rintro ⟨N, hN⟩
      apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
      intro c hc
      rcases hN c with h | h
      · exact absurd hc h
      · exact h
  rw [heq]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun c =>
    (hP c).compl.union (MeasurableSet.const _)

/-- A set of `ω` at which every `b` in the random set `V ω` satisfies a measurable property is measurable. -/
theorem ls_measurableSet_forall_mem {Ω : Type} [MeasurableSpace Ω] (V : Ω → Set ℤ)
    (hVb : ∀ b, MeasurableSet {ω | b ∈ V ω}) (P : Ω → ℤ → Prop)
    (hP : ∀ b, MeasurableSet {ω | P ω b}) : MeasurableSet {ω | ∀ b ∈ V ω, P ω b} := by
  have heq : {ω | ∀ b ∈ V ω, P ω b} = ⋂ b, ({ω | b ∈ V ω}ᶜ ∪ {ω | P ω b}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, ← imp_iff_not_or]
  rw [heq]
  exact MeasurableSet.iInter fun b => (hVb b).compl.union (hP b)

/-- The degree-normalized Laplacian of measurable multigraph data and a measurable vertex function is measurable. -/
theorem ls_measurable_mLaplacian {Ω : Type} [MeasurableSpace Ω]
    (M : Ω → ℤ → ℤ → ℕ) (hM : ∀ j k, Measurable fun ω => M ω j k)
    (u : Ω → ℤ → ℝ) (hu : ∀ k, Measurable fun ω => u ω k) (j : ℤ) :
    Measurable (fun ω => mLaplacian (M ω) (u ω) j) := by
  unfold mLaplacian
  have hd : Measurable (fun ω => ((mdeg (M ω) j : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_finsum_nat (fun ω k => M ω j k) (fun k => hM j k))
  refine hd.inv.mul (measurable_finsum_real _ ?_)
  intro k
  exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hM j k)).mul
    ((hu k).sub (hu j))

/-- For a measurable candidate, the inequalities of the discrete obstacle problem form a measurable event. -/
theorem ls_measurableSet_feasible {Ω : Type} [MeasurableSpace Ω]
    (M : Ω → ℤ → ℤ → ℕ) (hM : ∀ j k, Measurable fun ω => M ω j k)
    (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (r φ u : Ω → ℤ → ℝ) (hr : ∀ b, Measurable fun ω => r ω b)
    (hφ : ∀ b, Measurable fun ω => φ ω b) (hu : ∀ b, Measurable fun ω => u ω b) :
    MeasurableSet {ω | (∀ b ∈ V ω, mLaplacian (M ω) (u ω) b ≤ r ω b) ∧
      ∀ b ∈ W ω, φ ω b ≤ u ω b} := by
  have hVb : ∀ b, MeasurableSet {ω | b ∈ V ω} := fun b =>
    measurableSet_setOfPred.mpr ((measurable_set_mem b).comp hV)
  have hWb : ∀ b, MeasurableSet {ω | b ∈ W ω} := fun b =>
    measurableSet_setOfPred.mpr ((measurable_set_mem b).comp hW)
  have heq : {ω | (∀ b ∈ V ω, mLaplacian (M ω) (u ω) b ≤ r ω b) ∧
      ∀ b ∈ W ω, φ ω b ≤ u ω b} =
      (⋂ b, (({ω | b ∈ V ω})ᶜ ∪ {ω | mLaplacian (M ω) (u ω) b ≤ r ω b})) ∩
      (⋂ b, (({ω | b ∈ W ω})ᶜ ∪ {ω | φ ω b ≤ u ω b})) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
    classical
    simp only [← imp_iff_not_or]
  rw [heq]
  exact (MeasurableSet.iInter fun b => (hVb b).compl.union
    (measurableSet_le (ls_measurable_mLaplacian M hM u hu b) (hr b))).inter
    (MeasurableSet.iInter fun b => (hWb b).compl.union (measurableSet_le (hφ b) (hu b)))

/-- The event on which the data satisfy the standing hypotheses of the finite discrete obstacle problem. -/
theorem ls_measurableSet_good {Ω : Type} [MeasurableSpace Ω]
    (M : Ω → ℤ → ℤ → ℕ) (hM : ∀ j k, Measurable fun ω => M ω j k)
    (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (r φ : Ω → ℤ → ℝ) (hr : ∀ b, Measurable fun ω => r ω b)
    (hφ : ∀ b, Measurable fun ω => φ ω b) :
    MeasurableSet {ω | V ω ⊆ W ω ∧ (∀ b, 0 ≤ r ω b) ∧ (∀ b, φ ω b ≤ 0) ∧ (V ω).Finite ∧
      (W ω).Finite ∧ (∀ b ∈ V ω, {c | M ω b c ≠ 0}.Finite) ∧ (∀ b ∈ V ω, 0 < r ω b)} := by
  have hVb : ∀ b, MeasurableSet {ω | b ∈ V ω} := fun b =>
    measurableSet_setOfPred.mpr ((measurable_set_mem b).comp hV)
  have hWb : ∀ b, MeasurableSet {ω | b ∈ W ω} := fun b =>
    measurableSet_setOfPred.mpr ((measurable_set_mem b).comp hW)
  have hsub : MeasurableSet {ω | V ω ⊆ W ω} := by
    have h := ls_measurableSet_forall_mem V hVb (fun ω b => b ∈ W ω) (fun b => hWb b)
    simpa only [Set.subset_def] using h
  have hnn : MeasurableSet {ω | ∀ b, 0 ≤ r ω b} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun b => measurableSet_le measurable_const (hr b)
  have hle : MeasurableSet {ω | ∀ b, φ ω b ≤ 0} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun b => measurableSet_le (hφ b) measurable_const
  have hfinV : MeasurableSet {ω | (V ω).Finite} :=
    ls_measurableSet_finite_setOf (fun ω c => c ∈ V ω) (fun c => hVb c)
  have hfinW : MeasurableSet {ω | (W ω).Finite} :=
    ls_measurableSet_finite_setOf (fun ω c => c ∈ W ω) (fun c => hWb c)
  have hsupp : ∀ b, MeasurableSet {ω | {c | M ω b c ≠ 0}.Finite} := fun b =>
    ls_measurableSet_finite_setOf (fun ω c => M ω b c ≠ 0) fun c =>
      ((hM b c) (measurableSet_singleton 0)).compl
  have hsuppV : MeasurableSet {ω | ∀ b ∈ V ω, {c | M ω b c ≠ 0}.Finite} :=
    ls_measurableSet_forall_mem V hVb (fun ω b => {c | M ω b c ≠ 0}.Finite) hsupp
  have hposV : MeasurableSet {ω | ∀ b ∈ V ω, 0 < r ω b} :=
    ls_measurableSet_forall_mem V hVb (fun ω b => 0 < r ω b)
      (fun b => measurableSet_lt measurable_const (hr b))
  simp only [Set.ofPred_and]
  exact hsub.inter (hnn.inter (hle.inter (hfinV.inter (hfinW.inter (hsuppV.inter hposV)))))

/-- The discrete least supersolution is measurable, for measurable multigraph data, when the standing finiteness,
positivity and nonnegativity hypotheses hold at every `ω`. Candidates are a fixed dense sequence (after
strictification), so the infimum is a countable one. -/
theorem ls_measurable_of_good {Ω : Type} [MeasurableSpace Ω]
    (M : Ω → ℤ → ℤ → ℕ) (hM : ∀ j k, Measurable fun ω => M ω j k)
    (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (r φ : Ω → ℤ → ℝ) (hr : ∀ b, Measurable fun ω => r ω b)
    (hφ : ∀ b, Measurable fun ω => φ ω b) (a : ℤ)
    (hVW : ∀ ω, V ω ⊆ W ω) (hr0 : ∀ ω b, 0 ≤ r ω b) (hφ0 : ∀ ω b, φ ω b ≤ 0)
    (hVfin : ∀ ω, (V ω).Finite) (hWfin : ∀ ω, (W ω).Finite)
    (hlf : ∀ ω, ∀ b ∈ V ω, {c | M ω b c ≠ 0}.Finite)
    (hrpos : ∀ ω, ∀ b ∈ V ω, 0 < r ω b) :
    Measurable fun ω => discreteLeastSupersolution (M ω) (V ω) (W ω) (r ω) (φ ω) a := by
  classical
  let d : ℕ → (ℤ → ℝ) := TopologicalSpace.denseSeq (ℤ → ℝ)
  have hd : Dense (range d) := TopologicalSpace.denseRange_denseSeq (ℤ → ℝ)
  have hWa : MeasurableSet {ω | a ∈ W ω} :=
    measurableSet_setOfPred.mpr ((measurable_set_mem a).comp hW)
  have happrox : ∀ ω, ∀ v : ℤ → ℝ,
      ((∀ b ∈ V ω, mLaplacian (M ω) v b ≤ r ω b) ∧ ∀ b ∈ W ω, φ ω b ≤ v b) →
      ∀ q : ℝ, v a < q → ∃ n, ((∀ b ∈ V ω, mLaplacian (M ω) (d n) b ≤ r ω b) ∧
        ∀ b ∈ W ω, φ ω b ≤ d n b) ∧ d n a < q := by
    intro ω v hv q hvq
    obtain ⟨v', hv'V, hv'W, hv'q⟩ := exists_strict_discreteSupersolution (M ω) (V ω) (W ω)
      (hWfin ω) (r ω) (φ ω) (hrpos ω) v hv.1 hv.2 a q hvq
    obtain ⟨u, ⟨n, rfl⟩, huV, huW, huq⟩ := exists_dense_strict_discreteSupersolution (M ω) (V ω)
      (W ω) (hVfin ω) (hWfin ω) (hlf ω) (r ω) (φ ω) a q (range d) hd v' hv'V hv'W hv'q
    exact ⟨n, ⟨fun b hb => (huV b hb).le, fun b hb => (huW b hb).le⟩, huq⟩
  apply measurable_of_Iio
  intro q
  have heq : {ω | discreteLeastSupersolution (M ω) (V ω) (W ω) (r ω) (φ ω) a < q} =
      ({ω | a ∈ W ω} ∩ ⋃ n, ({ω | (∀ b ∈ V ω, mLaplacian (M ω) (d n) b ≤ r ω b) ∧
        ∀ b ∈ W ω, φ ω b ≤ d n b} ∩ {_ω | d n a < q})) ∪
      ({ω | a ∈ W ω}ᶜ ∩ {_ω | (0 : ℝ) < q}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iUnion, mem_compl_iff]
    by_cases ha : a ∈ W ω
    · simp only [ha, true_and, not_true_eq_false, false_and, or_false]
      have hne : ((fun v : ℤ → ℝ => v a) ''
          {v | (∀ b ∈ V ω, mLaplacian (M ω) v b ≤ r ω b) ∧
            ∀ b ∈ W ω, φ ω b ≤ v b}).Nonempty := by
        refine ⟨0, ⟨fun _ => 0, ⟨?_, ?_⟩, rfl⟩⟩
        · intro b _
          simpa [mLaplacian] using hr0 ω b
        · exact fun b _ => hφ0 ω b
      have hbdd : BddBelow ((fun v : ℤ → ℝ => v a) ''
          {v | (∀ b ∈ V ω, mLaplacian (M ω) v b ≤ r ω b) ∧
            ∀ b ∈ W ω, φ ω b ≤ v b}) := by
        refine ⟨φ ω a, ?_⟩
        rintro _ ⟨v, hv, rfl⟩
        exact hv.2 a ha
      rw [discreteLeastSupersolution, csInf_lt_iff hbdd hne]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, hlt⟩
        exact happrox ω v hv q hlt
      · rintro ⟨n, hn, hlt⟩
        exact ⟨d n a, ⟨d n, hn, rfl⟩, hlt⟩
    · simp only [ha, false_and, not_false_eq_true, true_and, false_or]
      rw [Equibounded.discreteLeastSupersolution_eq_zero_of_not_mem
        (fun h => ha (hVW ω h)) ha]
  change MeasurableSet {ω | discreteLeastSupersolution (M ω) (V ω) (W ω) (r ω) (φ ω) a < q}
  rw [heq]
  exact (hWa.inter (MeasurableSet.iUnion fun n =>
    (ls_measurableSet_feasible M hM V W hV hW r φ (fun _ => d n) hr hφ
      (fun _ => measurable_const)).inter (MeasurableSet.const _))).union
    (hWa.compl.inter (MeasurableSet.const _))


/-- **Environmental least supersolution (input E-m4-1).** For each vertex `a` and `t > 0`, the discrete least
supersolution of the mated map has a `σ(h, η)`-measurable version, equal to
`matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a` almost surely. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_matedLeastSupersolution
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε) (ρ t : ℝ) (ht : 0 < t) (a : ℤ)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite) :
    ∃ G : Ω → ℝ, Measurable[S.envSigma] G ∧
      ∀ᵐ ω ∂S.P, G ω = matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a := by
  classical
  choose M hM hMa using fun (j k : ℤ) => hS.exists_envSigma_measurable_mult ε j k
  have hMall : ∀ᵐ ω ∂S.P, ∀ j k, M j k ω = S.mult ε ω j k :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hMa j k
  obtain ⟨V, hV, hVa⟩ := hS.exists_envSigma_measurable_interiorCellVertices ε (ball 0 ρ)
    (Or.inl isOpen_ball)
  obtain ⟨W, hW, hWa⟩ := hS.exists_envSigma_measurable_cellVertices ε (closedBall 0 ρ)
    (Or.inr isClosed_closedBall)
  obtain ⟨g, hg, hga⟩ := hS.exists_envSigma_measurable_greenKernel ε (ball 0 ρ) (Or.inl isOpen_ball)
    (fun _ => (0 : ℤ)) measurable_const
  let Mp : Ω → ℤ → ℤ → ℕ := fun ω j k => M j k ω
  have hMp : ∀ j k, Measurable[S.envSigma] fun ω => Mp ω j k := fun j k => hM j k
  let r : Ω → ℤ → ℝ := fun ω b => ((mdeg (Mp ω) b : ℕ) : ℝ)⁻¹
  let φ : Ω → ℤ → ℝ := fun ω b => -(t / ε) * g ω b
  have hrm : ∀ b, Measurable[S.envSigma] fun ω => r ω b := by
    intro b
    have hd : Measurable[S.envSigma] (fun ω => (mdeg (Mp ω) b : ℕ)) :=
      @measurable_finsum_nat Ω ℤ S.envSigma _ (fun ω k => Mp ω b k) (fun k => hMp b k)
    exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hd).inv
  have hφm : ∀ b, Measurable[S.envSigma] fun ω => φ ω b := fun b => (hg b).const_mul _
  have hgood : ∀ᵐ ω ∂S.P, V ω ⊆ W ω ∧ (∀ b, 0 ≤ r ω b) ∧ (∀ b, φ ω b ≤ 0) ∧ (V ω).Finite ∧
      (W ω).Finite ∧ (∀ b ∈ V ω, {c | Mp ω b c ≠ 0}.Finite) ∧ (∀ b ∈ V ω, 0 < r ω b) := by
    filter_upwards [hVa, hWa, hga, hMall, hS.isAreaParametrized,
      etaProperStep_holds 𝒮 γ hγ hγ' Ω S hS, hlf] with ω hv hw hgω hMω hη hp hωlf
    have hMeq : Mp ω = S.mult ε ω := funext fun j => funext fun k => hMω j k
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv, hw]
      exact fun b hb => cellVertices_ball_subset_closedBall (ballInterior_subset_cellVertices_ball hb)
    · intro b
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · intro b
      show -(t / ε) * g ω b ≤ 0
      rw [hgω b]
      exact matedObstacle_nonpos ht.le hε.le b
    · rw [hv]
      exact ballInterior_finite hη.1 hp hε
    · rw [hw]
      exact cellVertices_finite_of_isBounded hη.1 hp hε isBounded_closedBall
    · intro b _
      rw [hMeq]
      exact hωlf b
    · intro b _
      show 0 < ((mdeg (Mp ω) b : ℕ) : ℝ)⁻¹
      rw [hMeq]
      exact inv_pos.mpr (Nat.cast_pos.mpr (mdeg_pos_of_ne_zero hωlf (S.mult_succ_ne_zero hε.le ω b)))
  -- the event on which the envSigma data are admissible; it has full measure
  let G : Set Ω := {ω | V ω ⊆ W ω ∧ (∀ b, 0 ≤ r ω b) ∧ (∀ b, φ ω b ≤ 0) ∧ (V ω).Finite ∧
    (W ω).Finite ∧ (∀ b ∈ V ω, {c | Mp ω b c ≠ 0}.Finite) ∧ (∀ b ∈ V ω, 0 < r ω b)}
  have hGm : ∀ ω, ω ∈ G → V ω ⊆ W ω ∧ (∀ b, 0 ≤ r ω b) ∧ (∀ b, φ ω b ≤ 0) ∧ (V ω).Finite ∧
      (W ω).Finite ∧ (∀ b ∈ V ω, {c | Mp ω b c ≠ 0}.Finite) ∧ (∀ b ∈ V ω, 0 < r ω b) :=
    fun ω h => h
  have hG : MeasurableSet[S.envSigma] G :=
    @ls_measurableSet_good Ω S.envSigma Mp hMp V W hV hW r φ hrm hφm
  -- the data modified off `G`: empty vertex sets, zero graph and thresholds
  let Mq : Ω → ℤ → ℤ → ℕ := fun ω j k => if ω ∈ G then Mp ω j k else 0
  let Vq : Ω → Set ℤ := fun ω => if ω ∈ G then V ω else ∅
  let Wq : Ω → Set ℤ := fun ω => if ω ∈ G then W ω else ∅
  let rq : Ω → ℤ → ℝ := fun ω b => if ω ∈ G then r ω b else 0
  let φq : Ω → ℤ → ℝ := fun ω b => if ω ∈ G then φ ω b else 0
  have hMq : ∀ j k, Measurable[S.envSigma] fun ω => Mq ω j k := fun j k => by
    show Measurable[S.envSigma] fun ω => if ω ∈ G then Mp ω j k else 0
    exact Measurable.ite hG (hMp j k) measurable_const
  have hVq : Measurable[S.envSigma] Vq := by
    show Measurable[S.envSigma] fun ω => if ω ∈ G then V ω else ∅
    exact Measurable.ite hG hV measurable_const
  have hWq : Measurable[S.envSigma] Wq := by
    show Measurable[S.envSigma] fun ω => if ω ∈ G then W ω else ∅
    exact Measurable.ite hG hW measurable_const
  have hrq : ∀ b, Measurable[S.envSigma] fun ω => rq ω b := fun b => by
    show Measurable[S.envSigma] fun ω => if ω ∈ G then r ω b else 0
    exact Measurable.ite hG (hrm b) measurable_const
  have hφq : ∀ b, Measurable[S.envSigma] fun ω => φq ω b := fun b => by
    show Measurable[S.envSigma] fun ω => if ω ∈ G then φ ω b else 0
    exact Measurable.ite hG (hφm b) measurable_const
  have hVWq : ∀ ω, Vq ω ⊆ Wq ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [Vq, Wq, hω, ↓reduceIte]
      exact (hGm ω hω).1
    · simp only [Vq, Wq, hω, ↓reduceIte, Set.empty_subset]
  have hr0q : ∀ ω b, 0 ≤ rq ω b := by
    intro ω b
    by_cases hω : ω ∈ G
    · simp only [rq, hω, ↓reduceIte]
      exact (hGm ω hω).2.1 b
    · simp only [rq, hω, ↓reduceIte, le_refl]
  have hφ0q : ∀ ω b, φq ω b ≤ 0 := by
    intro ω b
    by_cases hω : ω ∈ G
    · simp only [φq, hω, ↓reduceIte]
      exact (hGm ω hω).2.2.1 b
    · simp only [φq, hω, ↓reduceIte, le_refl]
  have hVfinq : ∀ ω, (Vq ω).Finite := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [Vq, hω, ↓reduceIte]
      exact (hGm ω hω).2.2.2.1
    · simp only [Vq, hω, ↓reduceIte, Set.finite_empty]
  have hWfinq : ∀ ω, (Wq ω).Finite := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [Wq, hω, ↓reduceIte]
      exact (hGm ω hω).2.2.2.2.1
    · simp only [Wq, hω, ↓reduceIte, Set.finite_empty]
  have hlfq : ∀ ω, ∀ b ∈ Vq ω, {c | Mq ω b c ≠ 0}.Finite := by
    intro ω b hb
    by_cases hω : ω ∈ G
    · simp only [Vq, hω, ↓reduceIte] at hb
      simp only [Mq, hω, ↓reduceIte]
      exact (hGm ω hω).2.2.2.2.2.1 b hb
    · simp [Vq, hω, ↓reduceIte] at hb
  have hrposq : ∀ ω, ∀ b ∈ Vq ω, 0 < rq ω b := by
    intro ω b hb
    by_cases hω : ω ∈ G
    · simp only [Vq, hω, ↓reduceIte] at hb
      simp only [rq, hω, ↓reduceIte]
      exact (hGm ω hω).2.2.2.2.2.2 b hb
    · simp [Vq, hω, ↓reduceIte] at hb
  have hF : Measurable[S.envSigma] fun ω =>
      discreteLeastSupersolution (Mq ω) (Vq ω) (Wq ω) (rq ω) (φq ω) a :=
    @ls_measurable_of_good Ω S.envSigma Mq hMq Vq Wq hVq hWq rq φq hrq hφq a hVWq hr0q hφ0q
      hVfinq hWfinq hlfq hrposq
  refine ⟨fun ω => discreteLeastSupersolution (Mq ω) (Vq ω) (Wq ω) (rq ω) (φq ω) a, hF, ?_⟩
  filter_upwards [hgood, hMall, hVa, hWa, hga] with ω hωG hMω hv hw hgω
  have hωG' : ω ∈ G := hωG
  have hq1 : Mq ω = S.mult ε ω := by
    funext j k
    simp only [Mq, hωG', ↓reduceIte]
    exact hMω j k
  have hq2 : Vq ω = ballInterior ε (S.η ω) ρ := by
    simp only [Vq, hωG', ↓reduceIte]
    exact hv
  have hq3 : Wq ω = cellVertices ε (S.η ω) (closedBall 0 ρ) := by
    simp only [Wq, hωG', ↓reduceIte]
    exact hw
  have hq4 : rq ω = fun b => ((mdeg (S.mult ε ω) b : ℕ) : ℝ)⁻¹ := by
    funext b
    have hMeq : Mp ω = S.mult ε ω := funext fun j => funext fun k => hMω j k
    simp only [rq, hωG', ↓reduceIte]
    show ((mdeg (Mp ω) b : ℕ) : ℝ)⁻¹ = _
    rw [hMeq]
  have hq5 : φq ω = matedObstacle (S.mult ε ω) ε (S.η ω) ρ t := by
    funext b
    simp only [φq, hωG', ↓reduceIte]
    exact congrArg (fun x => -(t / ε) * x) (hgω b)
  show discreteLeastSupersolution (Mq ω) (Vq ω) (Wq ω) (rq ω) (φq ω) a =
    matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a
  rw [hq1, hq2, hq3, hq4, hq5]
  rfl
end MatedCRT
