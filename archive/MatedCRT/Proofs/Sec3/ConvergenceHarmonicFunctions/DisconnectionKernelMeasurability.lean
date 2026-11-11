import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.DisconnectionStateMeasurability

/-!
# Measurability of the simple-random-walk law in the edge multiplicities and the start

Task `z1-steps2-disconnection-kernel-measurability`. Source: steps2-r3:414-420, the written countable-state
Markov-kernel integration argument ("the walk probabilities of the disconnection event ... integration against the
countable-state Markov kernel preserves measurability").

Route. Mathlib's `ProbabilityTheory.Kernel.traj` is measurable in its initial condition (`measurable_trajFun`), but its
transition kernels are not parametrised. The edge multiplicities `m` are therefore carried in the state: the enlarged
chain on `WalkState = (ℤ → ℤ → ℕ) × ℤ` keeps its first coordinate constant. Its walk coordinate has the law
`srwLaw m a` (projection identity, proved below). Measurability in `(m, a)` then follows from the measurability
of the enlarged trajectory kernel in its initial condition.

Contents. (1) `measurable_srwStep_singleton`, `measurable_srwStep_section`: the one-step law `srwStep` is measurable in
`(m, a)`, at singletons and on the parametric sections `{c | (m, c) ∈ T}`. (2) `enlargedStep`, `enlargedHistoryKernel`,
`enlargedTraj`: the enlarged chain with the multiplicities carried in the state. (3) `partialTraj_enlarged_lift`,
`partialTraj_enlarged_proj`: the finite marginals of the enlarged chain from a lifted start are the lifts of the walk
marginals (induction on `Kernel.partialTraj_succ_eq_comp`). (4) `enlargedTraj_map_proj`: the projection of the enlarged
trajectory is `srwLaw m a` (`MeasureTheory.IsProjectiveLimit.unique`). (5)
`measurable_srwLaw_walkDisconnectsBeforeHit`: the walk probability of the disconnection event is measurable in
`(m, target code, y, start)` (`ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`).

Not claimed here: the all-centre/radius events and the coanalytic envelope of steps2-r3 (outside the task).
-/

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.Kernel
open scoped ENNReal

namespace MatedCRT

noncomputable section

/-- The enlarged state space: the edge multiplicities (kept constant along a path) and the walk coordinate. -/
abbrev WalkState : Type := (ℤ → ℤ → ℕ) × ℤ

/-- The walk coordinate `(m, a) ↦ m a c` read at a point, measurable in the parameter pair. -/
lemma measurable_eval_eval (c : ℤ) : Measurable fun p : WalkState => p.1 p.2 c :=
  measurable_from_prod_countable_left fun y => (measurable_pi_apply c).comp (measurable_pi_apply y)

/-- The total edge mass `deg(a) = ∑_b m(a,b)` is measurable in `(m, a)`. -/
lemma measurable_edgeMeasure_univ :
    Measurable fun p : WalkState => edgeMeasure p.1 p.2 Set.univ := by
  have h : (fun p : WalkState => edgeMeasure p.1 p.2 Set.univ)
      = fun p => ∑' b : ℤ, ((p.1 p.2 b : ℕ) : ℝ≥0∞) := by
    funext p
    rw [edgeMeasure, Measure.sum_apply _ MeasurableSet.univ]
    simp
  rw [h]
  exact Measurable.tsum fun b => (measurable_from_nat.comp (measurable_eval_eval b))

/-- The mass of a singleton under `edgeMeasure m a` is the multiplicity `m(a,c)`. -/
lemma edgeMeasure_singleton (m : ℤ → ℤ → ℕ) (a c : ℤ) :
    edgeMeasure m a {c} = ((m a c : ℕ) : ℝ≥0∞) := by
  rw [edgeMeasure, Measure.sum_apply _ (measurableSet_singleton c)]
  simp [Measure.dirac_apply', Set.indicator_apply]

/-- The singleton mass of the one-step law is measurable in `(m, a)`. -/
lemma measurable_srwStep_singleton (c : ℤ) :
    Measurable fun p : WalkState => srwStep p.1 p.2 {c} := by
  have hf : Measurable fun p : WalkState => edgeMeasure p.1 p.2 Set.univ := measurable_edgeMeasure_univ
  have hP : MeasurableSet {p : WalkState | edgeMeasure p.1 p.2 Set.univ ≠ 0 ∧
      edgeMeasure p.1 p.2 Set.univ ≠ ⊤} :=
    ((hf (measurableSet_singleton 0)).compl).inter ((hf (measurableSet_singleton ⊤)).compl)
  have key : ∀ p : WalkState, srwStep p.1 p.2 {c} =
      if edgeMeasure p.1 p.2 Set.univ ≠ 0 ∧ edgeMeasure p.1 p.2 Set.univ ≠ ⊤ then
        (edgeMeasure p.1 p.2 Set.univ)⁻¹ * edgeMeasure p.1 p.2 {c}
      else Measure.dirac p.2 {c} := by
    intro p
    unfold srwStep
    split_ifs with h
    · rw [cond_apply MeasurableSet.univ, Set.univ_inter]
    · rfl
  have hfun : (fun p : WalkState => srwStep p.1 p.2 {c}) = fun p : WalkState =>
      if edgeMeasure p.1 p.2 Set.univ ≠ 0 ∧ edgeMeasure p.1 p.2 Set.univ ≠ ⊤ then
        (edgeMeasure p.1 p.2 Set.univ)⁻¹ * edgeMeasure p.1 p.2 {c}
      else Measure.dirac p.2 {c} := funext key
  have hcond : Measurable fun p : WalkState => (edgeMeasure p.1 p.2 Set.univ)⁻¹ * edgeMeasure p.1 p.2 {c} := by
    have hs : Measurable fun p : WalkState => edgeMeasure p.1 p.2 {c} := by
      have : (fun p : WalkState => edgeMeasure p.1 p.2 {c}) = fun p => ((p.1 p.2 c : ℕ) : ℝ≥0∞) := by
        funext p
        exact edgeMeasure_singleton p.1 p.2 c
      rw [this]
      exact measurable_from_nat.comp (measurable_eval_eval c)
    exact hf.inv.mul hs
  have hdirac : Measurable fun p : WalkState => Measure.dirac p.2 {c} := by
    have : (fun p : WalkState => Measure.dirac p.2 {c}) = fun p : WalkState => ({c} : Set ℤ).indicator 1 p.2 := by
      funext p
      exact Measure.dirac_apply' _ (measurableSet_singleton c)
    rw [this]
    exact ((measurable_const : Measurable fun _ : ℤ => (1 : ℝ≥0∞)).indicator (measurableSet_singleton c)).comp
      measurable_snd
  rw [hfun]
  exact Measurable.ite hP hcond hdirac

/-- Measurability of the parametric section masses: `(m, a) ↦ srwStep m a {c | (m, c) ∈ T}` for measurable `T`. -/
lemma measurable_srwStep_section {T : Set WalkState} (hT : MeasurableSet T) :
    Measurable fun p : WalkState => srwStep p.1 p.2 (Prod.mk p.1 ⁻¹' T) := by
  have hdec : ∀ p : WalkState, srwStep p.1 p.2 (Prod.mk p.1 ⁻¹' T)
      = ∑' c : ℤ, (Prod.mk p.1 ⁻¹' T).indicator (fun c' => srwStep p.1 p.2 {c'}) c := by
    intro p
    exact (Measure.tsum_indicator_apply_singleton _ _ (hT.preimage measurable_prodMk_left)).symm
  simp_rw [hdec]
  refine Measurable.tsum fun c => ?_
  have hS : MeasurableSet {p : WalkState | (p.1, c) ∈ T} :=
    hT.preimage (measurable_fst.prodMk measurable_const)
  have hind : (fun p : WalkState => (Prod.mk p.1 ⁻¹' T).indicator (fun c' => srwStep p.1 p.2 {c'}) c)
      = {p : WalkState | (p.1, c) ∈ T}.indicator (fun p => srwStep p.1 p.2 {c}) := by
    classical
    funext p
    simp [Set.indicator_apply]
  rw [hind]
  exact (measurable_srwStep_singleton c).indicator hS

/-- The enlarged one-step kernel: from `(m, a)` the chain moves to `(m, c)` with `c` drawn from `srwStep m a`. -/
noncomputable def enlargedStep : Kernel WalkState WalkState where
  toFun s := (srwStep s.1 s.2).map (fun c => (s.1, c))
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun T hT => ?_)
    have hfun : (fun s : WalkState => ((srwStep s.1 s.2).map (fun c => (s.1, c))) T)
        = fun s : WalkState => srwStep s.1 s.2 (Prod.mk s.1 ⁻¹' T) := by
      funext s
      have hm : Measurable fun c : ℤ => ((s.1, c) : WalkState) := measurable_const.prodMk measurable_id
      rw [Measure.map_apply hm hT]
    rw [hfun]
    exact measurable_srwStep_section hT

instance isMarkovKernel_enlargedStep : IsMarkovKernel enlargedStep :=
  ⟨fun s => by
    have hm : Measurable fun c : ℤ => ((s.1, c) : WalkState) := measurable_const.prodMk measurable_id
    change IsProbabilityMeasure ((srwStep s.1 s.2).map (fun c => (s.1, c)))
    exact ⟨by rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩⟩

/-- The enlarged history kernel at step `n`: reads the last state of the history and applies `enlargedStep`. -/
noncomputable def enlargedHistoryKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → WalkState) WalkState :=
  enlargedStep.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance isMarkovKernel_enlargedHistoryKernel (n : ℕ) : IsMarkovKernel (enlargedHistoryKernel n) := by
  unfold enlargedHistoryKernel; infer_instance

/-- The enlarged trajectory law from the initial history `x₀`: the chain with constant edge multiplicities. -/
noncomputable def enlargedTraj : Kernel ((i : Finset.Iic 0) → WalkState) ((n : ℕ) → WalkState) :=
  Kernel.traj (X := fun _ => WalkState) enlargedHistoryKernel 0

instance isMarkovKernel_enlargedTraj : IsMarkovKernel enlargedTraj := by
  unfold enlargedTraj
  infer_instance

/-! ### Lifts of walk histories with constant edge multiplicities -/

/-- The lift of a walk history to an enlarged history whose states all carry the edge multiplicities `m`. -/
def liftHist (m : ℤ → ℤ → ℕ) (N : ℕ) : ((i : Finset.Iic N) → ℤ) → (i : Finset.Iic N) → WalkState :=
  fun g i => (m, g i)

lemma measurable_liftHist (m : ℤ → ℤ → ℕ) (N : ℕ) : Measurable (liftHist m N) :=
  Measurable.of_eval fun i => measurable_const.prodMk (measurable_pi_apply i)

/-- The projection of an enlarged history to its walk coordinates. -/
def projHist (N : ℕ) : ((i : Finset.Iic N) → WalkState) → (i : Finset.Iic N) → ℤ :=
  fun h i => (h i).2

lemma measurable_projHist (N : ℕ) : Measurable (projHist N) :=
  Measurable.of_eval fun i => measurable_snd.comp (measurable_pi_apply i)

lemma projHist_comp_liftHist (m : ℤ → ℤ → ℕ) (N : ℕ) : projHist N ∘ liftHist m N = id := rfl

lemma enlargedHistoryKernel_liftHist (m : ℤ → ℤ → ℕ) (N : ℕ) (g : (i : Finset.Iic N) → ℤ) :
    enlargedHistoryKernel N (liftHist m N g) = (srwHistoryKernel m N g).map (fun c => (m, c)) := rfl

/-- A singleton-indexed section of the constant family: `piSingleton` returns the value at every index. -/
lemma piSingleton_apply_const {α : Type} [MeasurableSpace α] (N : ℕ) (x : α) (i : Finset.Ioc N (N + 1)) :
    (MeasurableEquiv.piSingleton (X := fun _ => α) N x) i = x := by
  obtain ⟨j, hj⟩ := i
  have hj' : j = N + 1 := by
    rw [Finset.mem_Ioc] at hj
    omega
  subst hj'
  rfl

lemma measurable_IicProdIoc_walk (N : ℕ) :
    Measurable (IicProdIoc (X := fun _ => WalkState) N (N + 1)) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : (i : ℕ) ≤ N
  · simp only [IicProdIoc, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [IicProdIoc, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_snd

lemma measurable_IicProdIoc_int (N : ℕ) :
    Measurable (IicProdIoc (X := fun _ => ℤ) N (N + 1)) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : (i : ℕ) ≤ N
  · simp only [IicProdIoc, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [IicProdIoc, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_snd

/-- The one-step compatibility of the lift: the joined history of a lifted history and a lifted new state is the lift of
the joined walk history. -/
lemma IicProdIoc_liftHist (m : ℤ → ℤ → ℕ) (N : ℕ) (g : (i : Finset.Iic N) → ℤ) (c : ℤ) :
    IicProdIoc (X := fun _ => WalkState) N (N + 1)
        (liftHist m N g, MeasurableEquiv.piSingleton (X := fun _ => WalkState) N (m, c))
      = liftHist m (N + 1)
          (IicProdIoc (X := fun _ => ℤ) N (N + 1) (g, MeasurableEquiv.piSingleton (X := fun _ => ℤ) N c)) := by
  funext i
  by_cases h : (i : ℕ) ≤ N
  · simp only [IicProdIoc, h, ↓reduceDIte, liftHist]
  · simp only [IicProdIoc, h, ↓reduceDIte, liftHist]
    rw [piSingleton_apply_const, piSingleton_apply_const]

/-- Pointwise one-step compatibility: from a lifted history the enlarged one-step law is the lift of the walk one-step
law. -/
lemma partialTraj_succ_liftHist (m : ℤ → ℤ → ℕ) (N : ℕ) (g : (i : Finset.Iic N) → ℤ) :
    partialTraj (X := fun _ => WalkState) enlargedHistoryKernel N (N + 1) (liftHist m N g)
      = (partialTraj (X := fun _ => ℤ) (srwHistoryKernel m) N (N + 1) g).map (liftHist m (N + 1)) := by
  rw [partialTraj_succ_self, partialTraj_succ_self,
    Kernel.map_apply _ (measurable_IicProdIoc_int N),
    Kernel.map_apply _ (measurable_IicProdIoc_walk N),
    Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply, Kernel.id_apply,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ => WalkState) N).measurable,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ => ℤ) N).measurable,
    enlargedHistoryKernel_liftHist, Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map (measurable_IicProdIoc_walk N) measurable_prodMk_left,
    Measure.map_map (measurable_IicProdIoc_int N) measurable_prodMk_left]
  have hpair : Measurable (fun c : ℤ => ((m, c) : WalkState)) := measurable_const.prodMk measurable_id
  have hpSW : Measurable (MeasurableEquiv.piSingleton (X := fun _ => WalkState) N) :=
    (MeasurableEquiv.piSingleton (X := fun _ => WalkState) N).measurable
  have hpSZ : Measurable (MeasurableEquiv.piSingleton (X := fun _ => ℤ) N) :=
    (MeasurableEquiv.piSingleton (X := fun _ => ℤ) N).measurable
  have hIW : Measurable (IicProdIoc (X := fun _ => WalkState) N (N + 1) ∘ Prod.mk (liftHist m N g)) :=
    (measurable_IicProdIoc_walk N).comp measurable_prodMk_left
  have hIZ : Measurable (IicProdIoc (X := fun _ => ℤ) N (N + 1) ∘ Prod.mk g) :=
    (measurable_IicProdIoc_int N).comp measurable_prodMk_left
  have hL : Measurable (liftHist m (N + 1)) := measurable_liftHist m (N + 1)
  rw [Measure.map_map hIW hpSW, Measure.map_map (hIW.comp hpSW) hpair,
    Measure.map_map hL hIZ, Measure.map_map (hL.comp hIZ) hpSZ]
  congr 1
  funext c
  exact IicProdIoc_liftHist m N g c

/-- Kernel form of the lift: the finite marginals of the enlarged chain started from a lifted point are the lifts of the
walk marginals. -/
lemma partialTraj_enlarged_lift (m : ℤ → ℤ → ℕ) (N : ℕ) :
    Kernel.partialTraj (X := fun _ => WalkState) enlargedHistoryKernel 0 N ∘ₖ
        Kernel.deterministic (liftHist m 0) (measurable_liftHist m 0)
      = Kernel.deterministic (liftHist m N) (measurable_liftHist m N) ∘ₖ
        Kernel.partialTraj (X := fun _ => ℤ) (srwHistoryKernel m) 0 N := by
  induction N with
  | zero =>
    rw [Kernel.partialTraj_self, Kernel.partialTraj_self, Kernel.id_comp, Kernel.comp_id]
  | succ N ih =>
    have hstep : Kernel.partialTraj (X := fun _ => WalkState) enlargedHistoryKernel N (N + 1) ∘ₖ
        Kernel.deterministic (liftHist m N) (measurable_liftHist m N)
        = Kernel.deterministic (liftHist m (N + 1)) (measurable_liftHist m (N + 1)) ∘ₖ
          Kernel.partialTraj (X := fun _ => ℤ) (srwHistoryKernel m) N (N + 1) := by
      refine Kernel.ext fun g => ?_
      rw [Kernel.comp_apply, Kernel.deterministic_apply,
        Measure.dirac_bind (Kernel.partialTraj (X := fun _ => WalkState) enlargedHistoryKernel N (N + 1)).measurable,
        Kernel.deterministic_comp_eq_map, Kernel.map_apply _ (measurable_liftHist m (N + 1))]
      exact partialTraj_succ_liftHist m N g
    rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le N), Kernel.partialTraj_succ_eq_comp (Nat.zero_le N),
      Kernel.comp_assoc, ih, ← Kernel.comp_assoc, hstep, Kernel.comp_assoc]

/-- The finite marginal of the enlarged chain from `(m, a)`, projected to the walk coordinates, is the walk marginal. -/
lemma partialTraj_enlarged_proj (m : ℤ → ℤ → ℕ) (a : ℤ) (N : ℕ) :
    (Kernel.partialTraj (X := fun _ => WalkState) enlargedHistoryKernel 0 N (fun _ => (m, a))).map (projHist N)
      = Kernel.partialTraj (X := fun _ => ℤ) (srwHistoryKernel m) 0 N (fun _ => a) := by
  have h := DFunLike.congr_fun (partialTraj_enlarged_lift m N) (fun _ => a)
  rw [Kernel.comp_apply, Kernel.deterministic_apply,
    Measure.dirac_bind (Kernel.partialTraj (X := fun _ => WalkState) enlargedHistoryKernel 0 N).measurable,
    Kernel.deterministic_comp_eq_map, Kernel.map_apply _ (measurable_liftHist m N)] at h
  have hlift : liftHist m 0 (fun _ => a) = fun _ => (m, a) := rfl
  rw [hlift] at h
  rw [h, Measure.map_map (measurable_projHist N) (measurable_liftHist m N), projHist_comp_liftHist, Measure.map_id]

/-- The enlarged trajectory from `(m, a)`, projected to its walk coordinate, is the walk law `srwLaw m a`. -/
lemma enlargedTraj_map_proj (m : ℤ → ℤ → ℕ) (a : ℤ) :
    (enlargedTraj (fun _ => (m, a))).map (fun y n => (y n).2) = srwLaw m a := by
  refine MeasureTheory.IsProjectiveLimit.unique
    (P := fun J : Finset ℕ => (srwLaw m a).map J.restrict) ?_ (fun J => rfl)
  intro J
  obtain ⟨N, hJN⟩ : ∃ N : ℕ, ∀ j ∈ J, j ≤ N := ⟨J.sup id, fun j hj => Finset.le_sup (f := id) hj⟩
  let R : ((i : Finset.Iic N) → ℤ) → ((j : J) → ℤ) :=
    fun g j => g ⟨j.1, Finset.mem_Iic.2 (hJN j.1 j.2)⟩
  have hR : Measurable R := Measurable.of_eval fun j => measurable_pi_apply _
  have hπ : Measurable (fun y : ℕ → WalkState => fun n => (y n).2) :=
    Measurable.of_eval fun n => measurable_snd.comp (measurable_pi_apply n)
  have hfr : Measurable (Preorder.frestrictLe (π := fun _ => WalkState) N) :=
    Preorder.measurable_frestrictLe N
  have hfr' : Measurable (Preorder.frestrictLe (π := fun _ => ℤ) N) := Preorder.measurable_frestrictLe N
  have hJr : Measurable (J.restrict : (ℕ → ℤ) → ((j : J) → ℤ)) := Finset.measurable_restrict J
  have hp : Measurable (projHist N) := measurable_projHist N
  have hJπ : (J.restrict : (ℕ → ℤ) → ((j : J) → ℤ)) ∘ (fun y : ℕ → WalkState => fun n => (y n).2)
      = R ∘ projHist N ∘ Preorder.frestrictLe (π := fun _ => WalkState) N := rfl
  have hRfr : R ∘ Preorder.frestrictLe (π := fun _ => ℤ) N = J.restrict := rfl
  dsimp only
  unfold enlargedTraj srwLaw
  rw [Measure.map_map hJr hπ, hJπ, ← hRfr, ← Measure.map_map hR (hp.comp hfr), ← Measure.map_map hR hfr',
    ← Measure.map_map hp hfr]
  simp only [Kernel.traj_map_frestrictLe_apply]
  rw [partialTraj_enlarged_proj]

/-! ### Measurability of the walk probability in the parameters -/

/-- The joint disconnection set of parameters and paths: the event `walkDisconnectsBeforeHit` for the edge
multiplicities, the target set (Bool code), the vertex `y` and the path. -/
def walkDisconSet : Set ((((ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × ℤ) × (ℕ → ℤ))) :=
  {p | walkDisconnectsBeforeHit p.1.1 {v | p.1.2.1 v = true} p.1.2.2.1 p.2}

lemma measurableSet_walkDisconSet : MeasurableSet walkDisconSet := by
  have hΦ : Measurable fun p : ((ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × ℤ) × (ℕ → ℤ) =>
      ((p.1.1, p.1.2.1, p.1.2.2.1, p.2) : (ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × (ℕ → ℤ)) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd))
  unfold walkDisconSet
  exact measurableSet_walkDisconnectsBeforeHit_comp hΦ

/-- **Measurability of the walk probability of the disconnection event, in the edge multiplicities, the target set,
the vertex `y` and the starting vertex.** The map `θ ↦ srwLaw θ.1 θ.2.2.2 {x | walkDisconnectsBeforeHit θ.1 {v | θ.2.1 v
= true} θ.2.2.1 x}` is measurable on `(ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × ℤ`. Source: steps2-r3:414-420; the proof is
the enlarged-chain argument of the module docstring. -/
theorem measurable_srwLaw_walkDisconnectsBeforeHit :
    Measurable fun θ : (ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × ℤ =>
      srwLaw θ.1 θ.2.2.2 {x : ℕ → ℤ | walkDisconnectsBeforeHit θ.1 {v | θ.2.1 v = true} θ.2.2.1 x} := by
  have hθ : Measurable fun θ : (ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × ℤ => fun _ : Finset.Iic 0 => (θ.1, θ.2.2.2) :=
    Measurable.of_eval fun _ =>
      measurable_fst.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hπ : Measurable (fun y : ℕ → WalkState => fun n => (y n).2) :=
    Measurable.of_eval fun n => measurable_snd.comp (measurable_pi_apply n)
  let L : Kernel ((ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × ℤ) (ℕ → ℤ) :=
    (enlargedTraj.comap (fun θ : (ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × ℤ => fun _ : Finset.Iic 0 => (θ.1, θ.2.2.2)) hθ).map
      (fun y n => (y n).2)
  have hL : ∀ θ : (ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × ℤ, L θ = srwLaw θ.1 θ.2.2.2 := by
    intro θ
    dsimp only [L]
    rw [Kernel.map_apply _ hπ, Kernel.comap_apply]
    exact enlargedTraj_map_proj θ.1 θ.2.2.2
  have hmeas := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := L) measurableSet_walkDisconSet
  have key : (fun θ : (ℤ → ℤ → ℕ) × (ℤ → Bool) × ℤ × ℤ => L θ (Prod.mk θ ⁻¹' walkDisconSet))
      = fun θ => srwLaw θ.1 θ.2.2.2 {x : ℕ → ℤ | walkDisconnectsBeforeHit θ.1 {v | θ.2.1 v = true} θ.2.2.1 x} := by
    funext θ
    rw [hL θ]
    rfl
  rw [key] at hmeas
  exact hmeas

end

end MatedCRT
