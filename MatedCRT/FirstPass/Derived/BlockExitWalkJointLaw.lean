import MatedCRT.FirstPass.Derived.BlockExitWalkNext

/-!
# The joint law of a block-exit position history and the next block-exit position of the walk

Continuation of `BlockExitWalkNext`: at the step `τ_n` just after the `n`-th block exit of the
interpolated walk, the next block-exit position is `walkNextBlockExit (Y_n) (θ_{τ_n} x)`. The
future event `{walkNextBlockExit y x' ∈ A}` depends on the current position `y` only through a
countable label (whether `y ∈ F`, the grid cell of `y`, whether `y ∈ A`), so the strong Markov
property at `τ_n` applies label by label.

* `srwLaw_strong_markov_label`: the strong Markov property at a random time with a future event
  that depends on the path through a countable label, each labelled event being determined by
  the history up to the random time.
* `walkNextBlockExit_preimage_eq`: `{x' | walkNextBlockExit y x' ∈ A}` is the labelled event
  `nextBlockExitEvent (nextBlockExitLabel y)`, measurable for measurable `A`.
* `srwLaw_blockExitPositions_succ_mem`: for every set `B` of position histories and every
  measurable `A`, when `τ_n` is almost surely finite and every walk step carrying a block-exit position off `F` has length at most
  `s / 2`,
  `P^a((Y_0, …, Y_n) ∈ B, Y_{n+1} ∈ A) =
    ∑_k ∫_{{(Y_0, …, Y_n) ∈ B} ∩ {τ_n = k}} P^{x_k}(walkNextBlockExit (Y_n) · ∈ A) dP^a`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open Function
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open WalkPotential

/-- **Strong Markov property at a random time with a labelled future event.** If the future event
`G (lab x)` depends on the path through a countable label `lab`, and each event
`S ∩ {lab = ℓ} ∩ {τ = k}` is determined by the history up to time `k`, then
`P^a(S ∩ {τ < ∞, θ_τ x ∈ G (lab x)}) = ∑_k ∫_{S ∩ {τ = k}} P^{x_k}(G (lab x)) dP^a`. -/
theorem srwLaw_strong_markov_label (m : ℤ → ℤ → ℕ) (a : ℤ) (τ : (ℕ → ℤ) → ℕ∞) {L : Type*}
    [Countable L] (lab : (ℕ → ℤ) → L) (G : L → Set (ℕ → ℤ)) (hG : ∀ ℓ, MeasurableSet (G ℓ))
    {S : Set (ℕ → ℤ)}
    (hS : ∀ (ℓ : L) (k : ℕ), ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      S ∩ {x | lab x = ℓ} ∩ {x | τ x = k} = {x | pathHist k x ∈ F}) :
    srwLaw m a (S ∩ {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G (lab x)}) =
      ∑' k : ℕ, ∫⁻ x in (S ∩ {x | τ x = k}), srwLaw m (x k) (G (lab x)) ∂srwLaw m a := by
  have hmeasSk : ∀ (ℓ : L) (k : ℕ), MeasurableSet (S ∩ {x | lab x = ℓ} ∩ {x | τ x = k}) := by
    intro ℓ k
    obtain ⟨F, hF, h⟩ := hS ℓ k
    rw [h]
    exact measurable_pathHist k hF
  have hpiece : ∀ ℓ : L,
      srwLaw m a ((S ∩ {x | lab x = ℓ}) ∩ {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G ℓ}) =
        ∑' k : ℕ, ∫⁻ x in (S ∩ {x | lab x = ℓ} ∩ {x | τ x = k}), srwLaw m (x k) (G ℓ)
          ∂srwLaw m a :=
    fun ℓ => srwLaw_strong_markov_state m a τ (fun _ => G ℓ) (fun _ => hG ℓ) (hS ℓ)
  have hL : S ∩ {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G (lab x)} =
      ⋃ ℓ : L, (S ∩ {x | lab x = ℓ}) ∩ {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G ℓ} := by
    ext x
    simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hxS, hfut⟩
      exact ⟨lab x, ⟨hxS, rfl⟩, hfut⟩
    · rintro ⟨ℓ, ⟨hxS, hℓ⟩, hfut⟩
      subst hℓ
      exact ⟨hxS, hfut⟩
  have hdisj : Pairwise (Disjoint on fun ℓ : L =>
      (S ∩ {x | lab x = ℓ}) ∩ {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G ℓ}) := by
    intro ℓ ℓ' hℓℓ'
    refine Set.disjoint_left.2 fun x hx hx' => hℓℓ' ?_
    exact hx.1.2.symm.trans hx'.1.2
  have hmeas : ∀ ℓ : L,
      MeasurableSet ((S ∩ {x | lab x = ℓ}) ∩ {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G ℓ}) := by
    intro ℓ
    have h : (S ∩ {x | lab x = ℓ}) ∩ {x | ∃ k : ℕ, τ x = k ∧ pathShift k x ∈ G ℓ} =
        ⋃ k : ℕ, (S ∩ {x | lab x = ℓ} ∩ {x | τ x = k}) ∩ {x | pathShift k x ∈ G ℓ} := by
      ext x
      simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hxS, k, hk, hfut⟩
        exact ⟨k, ⟨hxS, hk⟩, hfut⟩
      · rintro ⟨k, ⟨hxS, hk⟩, hfut⟩
        exact ⟨hxS, k, hk, hfut⟩
    rw [h]
    exact MeasurableSet.iUnion fun k => (hmeasSk ℓ k).inter (walk_measurable_pathShift k (hG ℓ))
  rw [hL, measure_iUnion hdisj hmeas, tsum_congr hpiece, ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  have hU : S ∩ {x | τ x = k} = ⋃ ℓ : L, S ∩ {x | lab x = ℓ} ∩ {x | τ x = k} := by
    ext x
    simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hxS, hk⟩
      exact ⟨lab x, ⟨hxS, rfl⟩, hk⟩
    · rintro ⟨ℓ, ⟨hxS, _⟩, hk⟩
      exact ⟨hxS, hk⟩
  have hdisjk : Pairwise (Disjoint on fun ℓ : L => S ∩ {x | lab x = ℓ} ∩ {x | τ x = k}) := by
    intro ℓ ℓ' hℓℓ'
    refine Set.disjoint_left.2 fun x hx hx' => hℓℓ' ?_
    exact hx.1.2.symm.trans hx'.1.2
  rw [hU, lintegral_iUnion (fun ℓ => hmeasSk ℓ k) hdisjk]
  refine tsum_congr fun ℓ => setLIntegral_congr_fun (hmeasSk ℓ k) fun x hx => ?_
  rw [hx.1.2]

open Classical in
/-- The label of a current block-exit position `y` that the next block-exit event reads: whether
`y ∈ F`, the grid cell of `y`, and whether `y ∈ A`. -/
noncomputable def nextBlockExitLabel (s : ℝ) (F A : Set ℂ) (y : ℂ) : Bool × (ℤ × ℤ) × Bool :=
  (decide (y ∈ F), cellIndex s y, decide (y ∈ A))

/-- The future event `{x' | walkNextBlockExit y x' ∈ A}` read from the label of `y`: the restarted
interpolated walk exits the block of the label cell at a finite time and at a position in `A`
(when the label says `y ∉ F`), or else the label says `y ∈ A`. -/
def nextBlockExitEvent (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) (A : Set ℂ)
    (ℓ : Bool × (ℤ × ℤ) × Bool) : Set (ℕ → ℤ) :=
  ({_x' | ℓ.1 = false} ∩ {x' | ContinuousPath.exitTime (openBlock s ℓ.2.1.1 ℓ.2.1.2)
      (interpPathCM v hc x') < ⊤} ∩
    {x' | interpPathCM v hc x' (blockExitTimeAt s (interpPathCM v hc x', ℓ.2.1)) ∈ A}) ∪
  (({_x' | ℓ.1 = false} ∩ {x' | ContinuousPath.exitTime (openBlock s ℓ.2.1.1 ℓ.2.1.2)
      (interpPathCM v hc x') < ⊤})ᶜ ∩ {_x' | ℓ.2.2 = true})

theorem measurableSet_nextBlockExitEvent (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ)
    {A : Set ℂ} (hA : MeasurableSet A) (ℓ : Bool × (ℤ × ℤ) × Bool) :
    MeasurableSet (nextBlockExitEvent v hc s A ℓ) := by
  have hE : MeasurableSet {x' : ℕ → ℤ | ContinuousPath.exitTime (openBlock s ℓ.2.1.1 ℓ.2.1.2)
      (interpPathCM v hc x') < ⊤} :=
    measurableSet_lt ((ContinuousPath.measurable_exitTime _ (isOpen_openBlock s _ _)).comp
      (measurable_interpPathCM v hc)) measurable_const
  have hpos : Measurable fun x' : ℕ → ℤ =>
      interpPathCM v hc x' (blockExitTimeAt s (interpPathCM v hc x', ℓ.2.1)) :=
    (ContinuousPath.measurable_eval_of_measurable (fun ω => blockExitTimeAt s (ω, ℓ.2.1))
      ((measurable_blockExitTimeAt s).comp (measurable_id.prodMk measurable_const))).comp
      (measurable_interpPathCM v hc)
  unfold nextBlockExitEvent
  exact (((MeasurableSet.const _).inter hE).inter (hpos hA)).union
    (((MeasurableSet.const _).inter hE).compl.inter (MeasurableSet.const _))

/-- The event that the next block-exit position lies in `A` is the labelled event of the label of
the current position. -/
theorem walkNextBlockExit_preimage_eq (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) (F A : Set ℂ)
    (y : ℂ) :
    {x' | walkNextBlockExit v hc s F y x' ∈ A} =
      nextBlockExitEvent v hc s A (nextBlockExitLabel s F A y) := by
  ext x'
  unfold walkNextBlockExit nextBlockExitEvent nextBlockExitLabel
  by_cases hyF : y ∈ F <;>
    by_cases hfin : ContinuousPath.exitTime (openBlock s (cellIndex s y).1 (cellIndex s y).2)
      (interpPathCM v hc x') < ⊤ <;>
    simp [hyF, hfin]

/-- **Joint law of a position history and the next block-exit position.** For every set `B` of
block-exit position histories and every measurable `A ⊆ ℂ`, if the step index `τ_n` just after the
`n`-th block exit is almost surely finite and every walk step carrying a block-exit position off `F` has length at most
`s / 2` (`ExitEdgesShort`), then
`P^a((Y_0, …, Y_n) ∈ B, Y_{n+1} ∈ A) =
  ∑_k ∫_{{(Y_0, …, Y_n) ∈ B} ∩ {τ_n = k}} P^{x_k}(walkNextBlockExit (Y_n) · ∈ A) dP^a`. -/
theorem srwLaw_blockExitPositions_succ_mem (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 < c) {s : ℝ} (hs : 0 < s) (F : Set ℂ)
    (hE : ExitEdgesShort m v hc.le s F (s / 2))
    (n : ℕ) (B : Set (Fin (n + 1) → ℂ)) {A : Set ℂ} (hA : MeasurableSet A)
    (hτ : ∀ᵐ x ∂srwLaw m a, walkBlockExitStepTime v hc.le s F n x ≠ ⊤) :
    srwLaw m a ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
        {x | interpPathCM v hc.le x (blockExitTimes s F (n + 1) (interpPathCM v hc.le x)) ∈ A}) =
      ∑' k : ℕ, ∫⁻ x in ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
          {x | walkBlockExitStepTime v hc.le s F n x = k}),
        srwLaw m (x k) {x' | walkNextBlockExit v hc.le s F
          (interpPathCM v hc.le x (blockExitTimes s F n (interpPathCM v hc.le x))) x' ∈ A}
          ∂srwLaw m a := by
  set lab : (ℕ → ℤ) → Bool × (ℤ × ℤ) × Bool := fun x => nextBlockExitLabel s F A
    (interpPathCM v hc.le x (blockExitTimes s F n (interpPathCM v hc.le x))) with hlab
  have hYlast : ∀ x : ℕ → ℤ, blockExitPositions s F n (interpPathCM v hc.le x) (Fin.last n) =
      interpPathCM v hc.le x (blockExitTimes s F n (interpPathCM v hc.le x)) := by
    intro x
    rw [blockExitPositions_apply, Fin.val_last]
  have hS : ∀ (ℓ : Bool × (ℤ × ℤ) × Bool) (k : ℕ), ∃ G : Set (Fin (k + 1) → ℤ),
      MeasurableSet G ∧
        {x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
          {x | lab x = ℓ} ∩ {x | walkBlockExitStepTime v hc.le s F n x = k} =
          {x | pathHist k x ∈ G} := by
    intro ℓ k
    obtain ⟨G, hG, h⟩ := walkBlockExitStepTime_history v hc s F n
      (B ∩ {g | nextBlockExitLabel s F A (g (Fin.last n)) = ℓ}) k
    refine ⟨G, hG, ?_⟩
    rw [← h]
    ext x
    simp only [mem_inter_iff, Set.mem_ofPred_eq, hlab, hYlast]
  have hae : ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
        {x | interpPathCM v hc.le x (blockExitTimes s F (n + 1) (interpPathCM v hc.le x)) ∈ A} :
          Set (ℕ → ℤ)) =ᵐ[srwLaw m a]
      ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
        {x | ∃ k : ℕ, walkBlockExitStepTime v hc.le s F n x = k ∧
          pathShift k x ∈ nextBlockExitEvent v hc.le s A (lab x)} : Set (ℕ → ℤ)) := by
    filter_upwards [hτ, ae_interpPathCM_blockExitTimes_succ_eq m a v hc hs F hE] with x hx1 hx2
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hx1
    have hnext := hx2 n k hk.symm
    apply propext
    simp only [mem_inter_iff, Set.mem_ofPred_eq]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hA'
      refine ⟨k, hk.symm, ?_⟩
      rw [hlab, ← walkNextBlockExit_preimage_eq, Set.mem_ofPred_eq, ← hnext]
      exact hA'
    · rintro ⟨k', hk', hfut⟩
      have hkk : k' = k := by
        have h3 : (k' : ℕ∞) = (k : ℕ∞) := hk'.symm.trans hk.symm
        exact_mod_cast h3
      subst hkk
      rw [hlab, ← walkNextBlockExit_preimage_eq, Set.mem_ofPred_eq, ← hnext] at hfut
      exact hfut
  rw [measure_congr hae, srwLaw_strong_markov_label m a (walkBlockExitStepTime v hc.le s F n) lab
    (nextBlockExitEvent v hc.le s A) (measurableSet_nextBlockExitEvent v hc.le s hA) hS]
  refine tsum_congr fun k => lintegral_congr fun x => ?_
  rw [hlab, walkNextBlockExit_preimage_eq]

end BlockExit

end MatedCRT
