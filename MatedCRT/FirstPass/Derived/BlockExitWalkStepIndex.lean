import MatedCRT.FirstPass.Derived.BrownianBlockExitTimes
import MatedCRT.FirstPass.Derived.InterpolatedWalkPrefix
import MatedCRT.FirstPass.S4S6c.StrongMarkovState

/-!
# Block exits of the interpolated walk are determined by the walk up to the next step

The walk half of the chaining step in the proof of Theorem 3.10 of the Gwynne-Miller-Sheffield
invariance principle applies the strong Markov property of the random walk at the step just after
the `n`-th block exit of its linear interpolation. This file supplies the random time and its
stopping property.

* `exitTime_eq_of_eqOn_of_exitTime_le`: two continuous paths that agree up to time `u` have the
  same exit time from an open set when the first one leaves it by time `u`.
* `blockExitTimes_eq_of_eqOn`: the successive block-exit times `σ_0, …, σ_n` (frozen on `F`) of
  a path are determined by the path up to any time `u ≥ σ_n`, provided these block exits are
  attained (`BlockExitsAttained`: at each `σ_j`, `j < n`, the path is in `F` or leaves the block
  around its grid cell at a finite time).
* `walkBlockExitStepTime`: for the interpolated walk at speed `c`, the step index
  `τ_n = ⌊c σ_n⌋₊ + 1` just after the `n`-th block exit (`⊤` if a block exit is not attained).
* `walkBlockExitStepTime_history`: each event `{(Y_0, …, Y_n) ∈ B} ∩ {τ_n = k}` of the block-exit
  positions is determined by the walk up to step `k` (the stopping property in the form of
  `srwLaw_strong_markov_state`), with no measurability assumption on `B`.
* `srwLaw_strong_markov_walkBlockExit`: the strong Markov property of the walk at `τ_n` with a
  state-dependent future event.
-/

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open WalkPotential

/-- If `ω` leaves the open set `U` by time `v` and `ω' = ω` on `[0, v]`, then `ω'` leaves `U` by
time `v`. -/
theorem exitTime_le_of_eqOn {α : Type*} [PseudoMetricSpace α] {U : Set α} (hU : IsOpen U)
    {ω ω' : ContinuousPath α} {v : ℝ≥0} (h : ∀ t ≤ v, ω t = ω' t)
    (hle : ContinuousPath.exitTime U ω ≤ v) : ContinuousPath.exitTime U ω' ≤ v := by
  obtain ⟨⟨t, ht⟩, htU⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU v ω).1 hle
  have ht' : t ≤ v := ht
  have hω't : ω' t ∉ U := by
    rw [← h t ht']
    exact htU
  exact (ContinuousPath.exitTime_le_of_notMem U ω' t hω't).trans (by exact_mod_cast ht')

/-- Two continuous paths that agree up to time `u` have the same exit time from an open set `U`
when the first one leaves `U` by time `u`. -/
theorem exitTime_eq_of_eqOn_of_exitTime_le {α : Type*} [PseudoMetricSpace α] {U : Set α}
    (hU : IsOpen U) {ω ω' : ContinuousPath α} {u : ℝ≥0} (h : ∀ t ≤ u, ω t = ω' t)
    (hle : ContinuousPath.exitTime U ω ≤ u) :
    ContinuousPath.exitTime U ω' = ContinuousPath.exitTime U ω := by
  have hfin : ContinuousPath.exitTime U ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  set e : ℝ≥0 := (ContinuousPath.exitTime U ω).toNNReal with he_def
  have he : ContinuousPath.exitTime U ω = e := (ENNReal.coe_toNNReal hfin).symm
  have heu : e ≤ u := by
    rw [he] at hle
    exact_mod_cast hle
  have hle' : ContinuousPath.exitTime U ω' ≤ e :=
    exitTime_le_of_eqOn hU (fun t ht => h t (ht.trans heu)) he.le
  refine le_antisymm (hle'.trans he.ge) ?_
  by_contra hlt
  rw [not_le] at hlt
  have hfin' : ContinuousPath.exitTime U ω' ≠ ⊤ := ne_top_of_lt hlt
  set e' : ℝ≥0 := (ContinuousPath.exitTime U ω').toNNReal with he'_def
  have he' : ContinuousPath.exitTime U ω' = e' := (ENNReal.coe_toNNReal hfin').symm
  have he'e : e' ≤ e := by
    rw [← ENNReal.coe_le_coe, ← he']
    exact hle'
  have hback : ContinuousPath.exitTime U ω ≤ e' :=
    exitTime_le_of_eqOn hU (fun t ht => (h t (ht.trans (he'e.trans heu))).symm) he'.le
  rw [← he'] at hback
  exact absurd hback (not_le.2 hlt)

/-- The first block-exit time read from the exit time: if the starting point is not in `F` and
the exit time from the block around its grid cell is finite, it is that exit time. -/
theorem coe_firstBlockExitTime_of_not_mem {s : ℝ} {F : Set ℂ} {ω : ContinuousPath ℂ}
    (hF : ω 0 ∉ F)
    (hfin : ContinuousPath.exitTime (openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2) ω
      < ⊤) :
    ((firstBlockExitTime s F ω : ℝ≥0) : ℝ≥0∞) =
      ContinuousPath.exitTime (openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2) ω := by
  unfold firstBlockExitTime
  simp only [hF, ↓reduceIte]
  unfold blockExitTimeAt
  rw [← ENNReal.coe_toNNReal hfin.ne]
  rfl

/-- The block around the grid cell of the starting point: two paths that agree up to time `u` have
the same exit time from it when the first one is not frozen and leaves it by time `u`. -/
theorem exitTime_openBlock_eq_of_eqOn {s : ℝ} {F : Set ℂ} {ω ω' : ContinuousPath ℂ} {u : ℝ≥0}
    (h : ∀ t ≤ u, ω t = ω' t) (hF : ω 0 ∉ F)
    (hfin : ContinuousPath.exitTime (openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2) ω
      < ⊤)
    (hle : firstBlockExitTime s F ω ≤ u) :
    ContinuousPath.exitTime (openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2) ω' =
      ContinuousPath.exitTime (openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2) ω := by
  refine exitTime_eq_of_eqOn_of_exitTime_le (isOpen_openBlock _ _ _) h ?_
  rw [← coe_firstBlockExitTime_of_not_mem hF hfin]
  exact_mod_cast hle

/-- The first block-exit time is determined by the path up to any time `u` after it, when the first
block exit is attained (the starting point is in `F`, or the exit time is finite). -/
theorem firstBlockExitTime_eq_of_eqOn {s : ℝ} {F : Set ℂ} {ω ω' : ContinuousPath ℂ} {u : ℝ≥0}
    (h : ∀ t ≤ u, ω t = ω' t)
    (hatt : ω 0 ∈ F ∨
      ContinuousPath.exitTime (openBlock s (cellIndex s (ω 0)).1 (cellIndex s (ω 0)).2) ω < ⊤)
    (hle : firstBlockExitTime s F ω ≤ u) :
    firstBlockExitTime s F ω' = firstBlockExitTime s F ω := by
  have h0 : ω' 0 = ω 0 := (h 0 zero_le).symm
  by_cases hF : ω 0 ∈ F
  · have hF' : ω' 0 ∈ F := h0 ▸ hF
    unfold firstBlockExitTime
    simp only [hF, hF', ↓reduceIte]
  · have hF' : ω' 0 ∉ F := h0 ▸ hF
    have hfin := hatt.resolve_left hF
    have hex := exitTime_openBlock_eq_of_eqOn h hF hfin hle
    have hfin' : ContinuousPath.exitTime (openBlock s (cellIndex s (ω' 0)).1
        (cellIndex s (ω' 0)).2) ω' < ⊤ := by
      rw [h0, hex]
      exact hfin
    have h1 := coe_firstBlockExitTime_of_not_mem (F := F) hF' hfin'
    have h2 := coe_firstBlockExitTime_of_not_mem (F := F) hF hfin
    rw [h0, hex, ← h2] at h1
    exact_mod_cast h1

/-- The first `n` block exits of `ω` are attained: at each block-exit time `σ_j`, `j < n`, the path
is in the frozen set `F` or leaves the open block around its grid cell at a finite time. -/
def BlockExitsAttained (s : ℝ) (F : Set ℂ) (n : ℕ) (ω : ContinuousPath ℂ) : Prop :=
  ∀ j < n, ω (blockExitTimes s F j ω) ∈ F ∨
    ContinuousPath.exitTime (openBlock s (cellIndex s (ω (blockExitTimes s F j ω))).1
      (cellIndex s (ω (blockExitTimes s F j ω))).2)
      (ContinuousPath.shift (blockExitTimes s F j ω) ω) < ⊤

theorem shift_apply_zero (a : ℝ≥0) (ω : ContinuousPath ℂ) :
    ContinuousPath.shift a ω 0 = ω a := by
  rw [ContinuousPath.shift_apply, add_zero]

/-- **Block-exit times are determined by the path up to any later time.** If the first `n` block
exits of `ω` are attained and `σ_n(ω) ≤ u`, then every path `ω'` that agrees with `ω` on `[0, u]`
has the same block-exit times `σ_0, …, σ_n`, and its first `n` block exits are attained. -/
theorem blockExitTimes_eq_of_eqOn {s : ℝ} {F : Set ℂ} {ω ω' : ContinuousPath ℂ} {u : ℝ≥0}
    (h : ∀ t ≤ u, ω t = ω' t) :
    ∀ n : ℕ, BlockExitsAttained s F n ω → blockExitTimes s F n ω ≤ u →
      (∀ j ≤ n, blockExitTimes s F j ω' = blockExitTimes s F j ω) ∧
        BlockExitsAttained s F n ω'
  | 0, _, _ => ⟨fun j hj => by
      have hj0 : j = 0 := Nat.le_zero.1 hj
      subst hj0
      rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, hatt, hle => by
    have hmono : blockExitTimes s F n ω ≤ blockExitTimes s F (n + 1) ω :=
      blockExitTimes_le_succ s F n ω
    obtain ⟨ih, ihatt⟩ := blockExitTimes_eq_of_eqOn h n (fun j hj => hatt j (by omega))
      (hmono.trans hle)
    set a := blockExitTimes s F n ω with ha_def
    have hau : a ≤ u := hmono.trans hle
    have hn : blockExitTimes s F n ω' = a := ih n le_rfl
    have hsh : ∀ t ≤ u - a, ContinuousPath.shift a ω t = ContinuousPath.shift a ω' t := by
      intro t ht
      rw [ContinuousPath.shift_apply, ContinuousPath.shift_apply]
      exact h _ ((le_tsub_iff_left hau).1 ht)
    have hattn : ContinuousPath.shift a ω 0 ∈ F ∨
        ContinuousPath.exitTime (openBlock s (cellIndex s (ContinuousPath.shift a ω 0)).1
          (cellIndex s (ContinuousPath.shift a ω 0)).2) (ContinuousPath.shift a ω) < ⊤ := by
      rw [shift_apply_zero]
      exact hatt n (Nat.lt_succ_self n)
    have hsucc : blockExitTimes s F (n + 1) ω = a + firstBlockExitTime s F (ContinuousPath.shift a ω) :=
      blockExitTimes_succ' s F n ω
    have hfirst_le : firstBlockExitTime s F (ContinuousPath.shift a ω) ≤ u - a := by
      rw [hsucc] at hle
      exact le_tsub_of_add_le_left hle
    have hfirst : firstBlockExitTime s F (ContinuousPath.shift a ω') =
        firstBlockExitTime s F (ContinuousPath.shift a ω) :=
      firstBlockExitTime_eq_of_eqOn hsh hattn hfirst_le
    have hsucc' : blockExitTimes s F (n + 1) ω' =
        blockExitTimes s F (n + 1) ω := by
      rw [blockExitTimes_succ' s F n ω', hn, hfirst, hsucc]
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
      · exact ih j (by omega)
      · have hj' : j = n + 1 := le_antisymm hj hjn
        subst hj'
        exact hsucc'
    · rcases Nat.lt_or_ge j n with hjn | hjn
      · exact ihatt j hjn
      · have hj' : j = n := le_antisymm (by omega) hjn
        subst hj'
        have hpos : ω' (blockExitTimes s F j ω') = ω a := by
          rw [hn]
          exact (h a hau).symm
        rw [hpos, hn]
        by_cases hF : ω a ∈ F
        · exact Or.inl hF
        · right
          have hfin : ContinuousPath.exitTime (openBlock s (cellIndex s (ω a)).1
              (cellIndex s (ω a)).2) (ContinuousPath.shift a ω) < ⊤ :=
            (hatt j (Nat.lt_succ_self j)).resolve_left hF
          have hF0 : ContinuousPath.shift a ω 0 ∉ F := by
            rw [shift_apply_zero]
            exact hF
          have hfin0 : ContinuousPath.exitTime (openBlock s
              (cellIndex s (ContinuousPath.shift a ω 0)).1
              (cellIndex s (ContinuousPath.shift a ω 0)).2) (ContinuousPath.shift a ω) < ⊤ := by
            rw [shift_apply_zero]
            exact hfin
          have hex := exitTime_openBlock_eq_of_eqOn hsh hF0 hfin0 hfirst_le
          rw [shift_apply_zero] at hex
          rw [hex]
          exact hfin

/-! ### The step index just after the `n`-th block exit of the interpolated walk -/

/-- The step index `τ_n = ⌊c σ_n⌋₊ + 1` of the walk just after the `n`-th block exit `σ_n` of its
linear interpolation at speed `c`, as a random time of the walk; `⊤` when one of the first `n`
block exits is not attained. -/
noncomputable def walkBlockExitStepTime (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ)
    (n : ℕ) (x : ℕ → ℤ) : ℕ∞ :=
  open Classical in
  if BlockExitsAttained s F n (interpPathCM v hc x) then
    ((⌊c * (blockExitTimes s F n (interpPathCM v hc x) : ℝ)⌋₊ + 1 : ℕ) : ℕ∞)
  else ⊤

/-- Walks that agree up to step `k` have interpolations that agree up to the step time `k / c`. -/
theorem interpPathCM_eq_of_le_stepTime (v : ℤ → ℂ) {c : ℝ} (hc : 0 < c) {k : ℕ}
    {x x' : ℕ → ℤ} (h : ∀ j ≤ k, x j = x' j) :
    ∀ t ≤ ((k / c : ℝ).toNNReal), interpPathCM v hc.le x t = interpPathCM v hc.le x' t := by
  intro t ht
  have h1 := congrArg (fun f => f t) (stopPath_interpPathCM_congr v hc k h)
  simp only [LatticeProb.stopPath_apply, min_eq_left ht] at h1
  exact h1

/-- **The `n`-th block exit is determined by the walk up to the step just after it.** If
`τ_n(x) = k` and `x' = x` up to step `k`, then `τ_n(x') = k` and the block-exit positions
`(Y_0, …, Y_n)` of the interpolations of `x` and `x'` coincide. -/
theorem walkBlockExitStepTime_determined (v : ℤ → ℂ) {c : ℝ} (hc : 0 < c) (s : ℝ) (F : Set ℂ)
    (n : ℕ) {x x' : ℕ → ℤ} {k : ℕ} (hk : walkBlockExitStepTime v hc.le s F n x = k)
    (h : ∀ j ≤ k, x j = x' j) :
    walkBlockExitStepTime v hc.le s F n x' = k ∧
      blockExitPositions s F n (interpPathCM v hc.le x') =
        blockExitPositions s F n (interpPathCM v hc.le x) := by
  set ω := interpPathCM v hc.le x with hω
  set ω' := interpPathCM v hc.le x' with hω'
  have hatt : BlockExitsAttained s F n ω := by
    by_contra hna
    unfold walkBlockExitStepTime at hk
    simp only [← hω, hna, ↓reduceIte] at hk
    exact ENat.top_ne_natCast k hk
  have hkσ : ⌊c * (blockExitTimes s F n ω : ℝ)⌋₊ + 1 = k := by
    unfold walkBlockExitStepTime at hk
    simp only [← hω, hatt, ↓reduceIte] at hk
    exact_mod_cast hk
  have hk0 : 0 ≤ (k : ℝ) / c := div_nonneg (Nat.cast_nonneg k) hc.le
  have hσu : blockExitTimes s F n ω ≤ ((k / c : ℝ).toNNReal) := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hk0, le_div_iff₀ hc, mul_comm]
    have := Nat.lt_floor_add_one (c * (blockExitTimes s F n ω : ℝ))
    rw [← hkσ]
    push_cast
    exact this.le
  have hagree : ∀ t ≤ ((k / c : ℝ).toNNReal), ω t = ω' t :=
    interpPathCM_eq_of_le_stepTime v hc h
  obtain ⟨heq, hatt'⟩ := blockExitTimes_eq_of_eqOn hagree n hatt hσu
  refine ⟨?_, ?_⟩
  · unfold walkBlockExitStepTime
    simp only [← hω', hatt', ↓reduceIte, heq n le_rfl]
    exact_mod_cast hkσ
  · funext i
    rw [blockExitPositions_apply, blockExitPositions_apply, heq i (Fin.is_le i)]
    have hmono : blockExitTimes s F i ω ≤ blockExitTimes s F n ω :=
      monotone_blockExitTimes s F ω (Fin.is_le i)
    exact (hagree _ (hmono.trans hσu)).symm

/-- **Stopping property of `τ_n`.** For every set `B` of position histories, the event
`{(Y_0, …, Y_n) ∈ B} ∩ {τ_n = k}` is determined by the walk up to step `k` (the hypothesis of
`srwLaw_strong_markov_state`). -/
theorem walkBlockExitStepTime_history (v : ℤ → ℂ) {c : ℝ} (hc : 0 < c) (s : ℝ) (F : Set ℂ)
    (n : ℕ) (B : Set (Fin (n + 1) → ℂ)) (k : ℕ) :
    ∃ G : Set (Fin (k + 1) → ℤ), MeasurableSet G ∧
      {x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
          {x | walkBlockExitStepTime v hc.le s F n x = k} = {x | pathHist k x ∈ G} := by
  set E := {x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
    {x | walkBlockExitStepTime v hc.le s F n x = k} with hE
  refine ⟨pathHist k '' E, (Set.to_countable _).measurableSet, ?_⟩
  ext x
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, ⟨hyB, hyk⟩, hyx⟩
    have hagree : ∀ j ≤ k, y j = x j := by
      intro j hj
      have := congrFun hyx ⟨j, Nat.lt_succ_of_le hj⟩
      exact this
    obtain ⟨hxk, hpos⟩ := walkBlockExitStepTime_determined v hc s F n hyk hagree
    refine ⟨?_, hxk⟩
    show blockExitPositions s F n (interpPathCM v hc.le x) ∈ B
    rw [hpos]
    exact hyB

/-- **Strong Markov property of the walk just after its `n`-th block exit**, with a
state-dependent future event: for every set `B` of position histories,
`P^a({(Y_0, …, Y_n) ∈ B} ∩ {τ_n < ∞, θ_{τ_n} x ∈ G(x_{τ_n})}) =
  ∑_k ∫_{{(Y_0, …, Y_n) ∈ B} ∩ {τ_n = k}} P^{x_k}(G(x_k)) dP^a`. -/
theorem srwLaw_strong_markov_walkBlockExit (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 < c) (s : ℝ) (F : Set ℂ) (n : ℕ) (B : Set (Fin (n + 1) → ℂ))
    (G : ℤ → Set (ℕ → ℤ)) (hG : ∀ y, MeasurableSet (G y)) :
    srwLaw m a ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
        {x | ∃ k : ℕ, walkBlockExitStepTime v hc.le s F n x = k ∧ pathShift k x ∈ G (x k)}) =
      ∑' k : ℕ, ∫⁻ x in ({x : ℕ → ℤ | blockExitPositions s F n (interpPathCM v hc.le x) ∈ B} ∩
          {x | walkBlockExitStepTime v hc.le s F n x = k}), srwLaw m (x k) (G (x k)) ∂srwLaw m a :=
  srwLaw_strong_markov_state m a (walkBlockExitStepTime v hc.le s F n) G hG
    (walkBlockExitStepTime_history v hc s F n B)

end BlockExit

end MatedCRT
