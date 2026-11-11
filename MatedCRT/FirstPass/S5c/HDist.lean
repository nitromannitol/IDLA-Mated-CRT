import MatedCRT.FirstPass.S5c.DistFrontier
import MatedCRT.FirstPass.S5c.SuccessEvent
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Proofs.Infra.MatingOfTrees

/-!
# FIRST PASS, Lemma 5.3 (three-inputs §7): the distance events `hdist`

Proves the per-vertex distance event of `SuccessEvent.lean`, in the conditional form
`{ω | a ∈ Λ ω → δ < infDist (vertexPoint ε (η ω) a) (frontier (fillCells ε (η ω) (Λ ω)))}`, where
`Λ ω = matedDiscreteCluster (mult ε ω) ε (η ω) ρ t`.

* Almost surely `η` is continuous and proper (`ae_continuous_eta_of`, `IsValid.ae_tendsto_cocompact`), so the
  cluster is finite (`cellVertices_finite_of_isCompact`) and `fillCells ε η Λ` is compact.
* Deterministic: for `a ∈ Λ`, `lt_infDist_frontier_fillCells` turns the distance test into a countable rational test
  (`lt_infDist_frontier_iff`, DistFrontier.lean).
* Measurability: `x ∈ η '' Icc a b` is a countable condition on rational sample times (`mem_image_Icc_iff_rat`);
  hence `nullMeasurableSet_mem_image_Icc`, and then countable unions and intersections.
-/

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT.S5c

variable {Ω : Type} [MeasurableSpace Ω]

/-! ### Deterministic topology -/

/-- For a continuous curve `f` and a nondegenerate interval `[a,b]`, a point `x` lies on `f '' [a,b]` iff for every
`n` some rational sample time `q ∈ [a,b]` has `dist x (f q) < 1/(n+1)`. -/
theorem mem_image_Icc_iff_rat {f : ℝ → ℂ} (hf : Continuous f) {a b : ℝ} (hab : a < b) (x : ℂ) :
    x ∈ f '' Icc a b ↔ ∀ n : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc a b ∧ dist x (f (q : ℝ)) < 1 / ((n : ℝ) + 1) := by
  constructor
  · rintro ⟨y, hy, rfl⟩ n
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hf y (1 / ((n : ℝ) + 1)) (by positivity)
    have hclose : ∃ q : ℚ, (q : ℝ) ∈ Icc a b ∧ dist (q : ℝ) y < δ := by
      rcases lt_or_eq_of_le hy.2 with h | h
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min h (by linarith : y < y + δ))
        have hqb : (q : ℝ) < b := lt_of_lt_of_le hq2 (min_le_left _ _)
        have hqd : (q : ℝ) < y + δ := lt_of_lt_of_le hq2 (min_le_right _ _)
        refine ⟨q, ⟨by linarith [hy.1], hqb.le⟩, ?_⟩
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
      · have hay : a < y := by linarith
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hay (by linarith : y - δ < y))
        have haq : a < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq1
        have hdq : y - δ < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
        have hqy : (q : ℝ) < y := hq2
        refine ⟨q, ⟨haq.le, by linarith [hy.2]⟩, ?_⟩
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
    obtain ⟨q, hqI, hqd⟩ := hclose
    exact ⟨q, hqI, by rw [dist_comm]; exact hball _ hqd⟩
  · intro h
    have hK : IsCompact (f '' Icc a b) := isCompact_Icc.image hf
    have hcl : x ∈ closure (f '' Icc a b) := by
      refine Metric.mem_closure_iff.2 fun e he => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt he
      obtain ⟨q, hq, hd⟩ := h n
      exact ⟨f (q : ℝ), ⟨(q : ℝ), hq, rfl⟩, lt_trans hd hn⟩
    rwa [hK.isClosed.closure_eq] at hcl

/-- A nonempty compact proper subset of `ℂ` has nonempty frontier (`ℂ` is connected and not compact). -/
theorem frontier_nonempty_of_isCompact {U : Set ℂ} (hU : IsCompact U) (hne : U.Nonempty) :
    (frontier U).Nonempty := by
  by_contra hfr
  rw [not_nonempty_iff_eq_empty] at hfr
  have hcl : IsClosed U := hU.isClosed
  rw [hcl.frontier_eq, sdiff_eq_empty] at hfr
  have hop : IsOpen U := by
    have hint : interior U = U := Subset.antisymm interior_subset hfr
    rw [← hint]
    exact isOpen_interior
  rcases isClopen_iff.1 (⟨hcl, hop⟩ : IsClopen U) with h0 | huniv
  · exact hne.ne_empty h0
  · rw [huniv] at hU
    exact noncompact_univ ℂ hU

/-- The rational test for the distance from the vertex `a` (a point of its own cell) to the frontier of the union of
the cells of a finite set `C ∋ a` (`lt_infDist_frontier_iff` for `U = fillCells ε η C`). -/
theorem lt_infDist_frontier_fillCells {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε) {C : Set ℤ}
    (hC : C.Finite) {a : ℤ} (ha : a ∈ C) {δ : ℝ} :
    δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η C)) ↔
      ∃ r : ℚ, δ < (r : ℝ) ∧
        ∀ q : ℚ × ℚ, ‖gaussRat q‖ < (r : ℝ) → vertexPoint ε η a + gaussRat q ∈ fillCells ε η C := by
  have hcpt : IsCompact (fillCells ε η C) := by
    unfold fillCells
    exact hC.isCompact_biUnion fun k _ => by unfold cell; exact isCompact_Icc.image hη
  have hz : vertexPoint ε η a ∈ fillCells ε η C := by
    simp only [fillCells, mem_iUnion₂]
    refine ⟨a, ha, ?_⟩
    have h1 : ε * ((a : ℝ) - 1) ≤ ε * a := mul_le_mul_of_nonneg_left (by linarith) hε.le
    exact ⟨ε * a, ⟨h1, le_refl _⟩, rfl⟩
  exact lt_infDist_frontier_iff hcpt.isClosed (frontier_nonempty_of_isCompact hcpt ⟨_, hz⟩) hz

/-! ### Almost sure regularity of the curve -/

/-- Almost surely `η` is continuous (the `areaParam` clause of `IsValid.matingOfTrees`). -/
theorem ae_continuous_eta_of {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, Continuous (S.η ω) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  filter_upwards [hC.areaParam, htie] with ω hap hω
  obtain ⟨⟨φ, -, hφ⟩, -⟩ := hap
  have hη : S.η ω = ηL ω ∘ φ := by
    rw [← hω.1]
    funext t
    exact hφ t
  rw [hη]
  exact (ηL ω).continuous.comp φ.toHomeomorph.continuous

/-- Each evaluation `ω ↦ η ω t` is almost everywhere measurable (through the measurable coupling `η'`). -/
theorem ae_measurable_eta_eval {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (t : ℝ) : AEMeasurable (fun ω => S.η ω t) S.P := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, hae⟩ := hS.matingOfTrees
  have hη' : Measurable fun ω => η' ω t :=
    (continuous_eval_const t).measurable.comp hC.measurable_curves.2.1
  have hae' : (fun ω => η' ω t) =ᵐ[S.P] fun ω => S.η ω t :=
    hae.mono fun ω h => congrFun h.1 t
  exact hη'.aemeasurable.congr hae'

/-! ### Null measurability -/

/-- `{ω | p → ω ∈ Q}` is null measurable for a constant proposition `p`. -/
theorem nullMeasurableSet_prop_imp {P : Measure Ω} (p : Prop) {Q : Set Ω} (hQ : NullMeasurableSet Q P) :
    NullMeasurableSet {ω | p → ω ∈ Q} P := by
  have heq : {ω : Ω | p → ω ∈ Q} = {_ω : Ω | ¬p} ∪ Q := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, imp_iff_not_or]
  rw [heq]
  exact (MeasurableSet.const (¬p)).nullMeasurableSet.union hQ

/-- A random point lies on the image of a random continuous curve over `[a,b]` on a null measurable event. -/
theorem nullMeasurableSet_mem_image_Icc {P : Measure Ω} {η : Ω → ℝ → ℂ} (hη : ∀ᵐ ω ∂P, Continuous (η ω))
    (hev : ∀ t : ℝ, AEMeasurable (fun ω => η ω t) P) {x : Ω → ℂ} (hx : AEMeasurable x P) {a b : ℝ}
    (hab : a < b) : NullMeasurableSet {ω | x ω ∈ η ω '' Icc a b} P := by
  have hmeas : NullMeasurableSet (⋂ n : ℕ, {ω | ∃ q : ℚ, (q : ℝ) ∈ Icc a b ∧
      dist (x ω) (η ω (q : ℝ)) < 1 / ((n : ℝ) + 1)}) P := by
    refine NullMeasurableSet.iInter fun n => ?_
    have heq : {ω | ∃ q : ℚ, (q : ℝ) ∈ Icc a b ∧ dist (x ω) (η ω (q : ℝ)) < 1 / ((n : ℝ) + 1)} =
        ⋃ q : ℚ, ({ω | (q : ℝ) ∈ Icc a b} ∩ {ω | dist (x ω) (η ω (q : ℝ)) < 1 / ((n : ℝ) + 1)}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    rw [heq]
    refine NullMeasurableSet.iUnion fun q => NullMeasurableSet.inter ?_ ?_
    · exact (MeasurableSet.const _).nullMeasurableSet
    · exact nullMeasurableSet_lt (hx.dist (hev q)) aemeasurable_const
  refine NullMeasurableSet.congr hmeas (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [hη] with ω hω
  simp only [mem_iInter, mem_ofPred_eq]
  exact (mem_image_Icc_iff_rat hω hab (x ω)).symm

/-- Membership of a random point in the fillCells of a random cluster `Λ ω` (each `k ∈ Λ` null measurable). -/
theorem nullMeasurableSet_mem_fillCells {P : Measure Ω} {ε : ℝ} {η : Ω → ℝ → ℂ} (hε : 0 < ε)
    (hη : ∀ᵐ ω ∂P, Continuous (η ω)) (hev : ∀ t : ℝ, AEMeasurable (fun ω => η ω t) P)
    {x : Ω → ℂ} (hx : AEMeasurable x P) {Λ : Ω → Set ℤ} (hΛ : ∀ k : ℤ, NullMeasurableSet {ω | k ∈ Λ ω} P) :
    NullMeasurableSet {ω | x ω ∈ fillCells ε (η ω) (Λ ω)} P := by
  have heq : {ω | x ω ∈ fillCells ε (η ω) (Λ ω)} =
      ⋃ k : ℤ, ({ω | k ∈ Λ ω} ∩ {ω | x ω ∈ η ω '' Icc (ε * ((k : ℝ) - 1)) (ε * k)}) := by
    ext ω
    simp only [fillCells, cell, mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
  rw [heq]
  refine NullMeasurableSet.iUnion fun k => (hΛ k).inter ?_
  have hab : ε * ((k : ℝ) - 1) < ε * k := mul_lt_mul_of_pos_left (by linarith) hε
  exact nullMeasurableSet_mem_image_Icc hη hev hx hab

/-! ### The distance event at one vertex -/

/-- **The distance event at a vertex** (conditional form of `hdist`, SuccessEvent.lean). For a finite-valued random
cluster `Λ` of a continuous random curve, `a ∈ Λ → δ < dist(η(εa), ∂(fillCells Λ))` is null measurable. -/
theorem nullMeasurableSet_vertex_frontier {P : Measure Ω} {ε : ℝ} {η : Ω → ℝ → ℂ} (hε : 0 < ε)
    (hcont : ∀ᵐ ω ∂P, Continuous (η ω)) (hev : ∀ t : ℝ, AEMeasurable (fun ω => η ω t) P)
    {Λ : Ω → Set ℤ} (hΛm : ∀ k : ℤ, NullMeasurableSet {ω | k ∈ Λ ω} P) (hΛf : ∀ᵐ ω ∂P, (Λ ω).Finite)
    (δ : ℝ) (a : ℤ) :
    NullMeasurableSet {ω | a ∈ Λ ω →
      δ < infDist (vertexPoint ε (η ω) a) (frontier (fillCells ε (η ω) (Λ ω)))} P := by
  have hX : ∀ q : ℚ × ℚ, AEMeasurable (fun ω => vertexPoint ε (η ω) a + gaussRat q) P := fun q => by
    simp only [vertexPoint]
    exact (hev (ε * a)).add aemeasurable_const
  have hM : ∀ q : ℚ × ℚ, NullMeasurableSet
      {ω | vertexPoint ε (η ω) a + gaussRat q ∈ fillCells ε (η ω) (Λ ω)} P :=
    fun q => nullMeasurableSet_mem_fillCells hε hcont hev (hX q) hΛm
  have hE : NullMeasurableSet ({ω | a ∈ Λ ω}ᶜ ∪ ⋃ r : ℚ, ({ω | δ < (r : ℝ)} ∩
      ⋂ q : ℚ × ℚ, {ω | ‖gaussRat q‖ < (r : ℝ) →
        vertexPoint ε (η ω) a + gaussRat q ∈ fillCells ε (η ω) (Λ ω)})) P := by
    refine (hΛm a).compl.union (NullMeasurableSet.iUnion fun r => ?_)
    refine NullMeasurableSet.inter (MeasurableSet.const _).nullMeasurableSet ?_
    exact NullMeasurableSet.iInter fun q => nullMeasurableSet_prop_imp _ (hM q)
  have hEq : {ω | a ∈ Λ ω → ∃ r : ℚ, δ < (r : ℝ) ∧
      ∀ q : ℚ × ℚ, ‖gaussRat q‖ < (r : ℝ) →
        vertexPoint ε (η ω) a + gaussRat q ∈ fillCells ε (η ω) (Λ ω)} =
      ({ω | a ∈ Λ ω}ᶜ ∪ ⋃ r : ℚ, ({ω | δ < (r : ℝ)} ∩
        ⋂ q : ℚ × ℚ, {ω | ‖gaussRat q‖ < (r : ℝ) →
          vertexPoint ε (η ω) a + gaussRat q ∈ fillCells ε (η ω) (Λ ω)})) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_iUnion, mem_inter_iff, mem_iInter]
    tauto
  have hgood : {ω | a ∈ Λ ω → δ < infDist (vertexPoint ε (η ω) a) (frontier (fillCells ε (η ω) (Λ ω)))} =ᵐ[P]
      {ω | a ∈ Λ ω → ∃ r : ℚ, δ < (r : ℝ) ∧
        ∀ q : ℚ × ℚ, ‖gaussRat q‖ < (r : ℝ) →
          vertexPoint ε (η ω) a + gaussRat q ∈ fillCells ε (η ω) (Λ ω)} := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [hcont, hΛf] with ω hc hf
    by_cases ha : a ∈ Λ ω
    · simp only [ha, true_implies]
      exact lt_infDist_frontier_fillCells hc hε hf ha
    · simp [ha]
  rw [← hEq] at hE
  exact NullMeasurableSet.congr hE hgood.symm

/-- **The distance events `hdist` of the mated-CRT environment** (conditional form, the input of
`nullMeasurableSet_success`): the cluster `matedDiscreteCluster` is a.s. finite, its cells are compact, and the
vertex-`a` distance event is null measurable. -/
theorem nullMeasurableSet_hdist {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε) (ρ t δ : ℝ) (ht : 0 < t)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {x | S.mult ε ω b x ≠ 0}.Finite) (a : ℤ) :
    NullMeasurableSet {ω | a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t →
      δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)))} S.P := by
  have hcont : ∀ᵐ ω ∂S.P, Continuous (S.η ω) := ae_continuous_eta_of hS
  have hprop : ∀ᵐ ω ∂S.P, Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) := hS.ae_tendsto_cocompact
  have hfin : ∀ᵐ ω ∂S.P, (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).Finite := by
    filter_upwards [hcont, hprop] with ω hc hp
    refine (cellVertices_finite_of_isCompact hc hp hε (isCompact_closedBall (0 : ℂ) ρ)).subset ?_
    rintro k ⟨hk, -⟩
    obtain ⟨y, hy⟩ := hk
    exact ⟨y, hy.1, ball_subset_closedBall hy.2⟩
  exact nullMeasurableSet_vertex_frontier hε hcont (ae_measurable_eta_eval hS)
    (fun k => hS.nullMeasurableSet_mem_matedDiscreteCluster hγ hγ' hε ρ t ht k hlf) hfin δ a

/-- **The success event `E ε` is null measurable** (`nullMeasurableSet_success` with its distance inputs supplied
by `nullMeasurableSet_hdist`): the fixed-mesh measurability step of `MeanValueSurplusLowerStep`, §7. -/
theorem nullMeasurableSet_success_proved {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε) (ρ t δ : ℝ) (ht : 0 < t)
    (c : Ω → ℝ) (hc : Measurable[S.envSigma] c)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {x | S.mult ε ω b x ≠ 0}.Finite) :
    NullMeasurableSet {ω | ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
      δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) →
      c ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
        t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a} S.P :=
  nullMeasurableSet_success hS hγ hγ' hε ρ t δ ht c hc hlf
    (fun a => nullMeasurableSet_hdist hS hγ hγ' hε ρ t δ ht hlf a)

end MatedCRT.S5c
