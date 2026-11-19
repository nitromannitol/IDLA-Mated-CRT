import MatedCRT.FirstPass.Derived.BlockExitWalkStepIndex
import MatedCRT.FirstPass.Derived.InterpolatedWalkShift
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk

/-!
# The next block-exit position of the interpolated walk after the step following a block exit

In the chaining step of the proof of Theorem 3.10 of the Gwynne-Miller-Sheffield invariance
principle, the walk is restarted by the strong Markov property at the step `τ_n = ⌊c σ_n⌋₊ + 1`
just after the `n`-th block exit `σ_n` of its linear interpolation at speed `c`
(`walkBlockExitStepTime`). This file shows that the next block-exit position is a function of the
current block-exit position `Y_n` and of the restarted walk `θ_{τ_n} x` alone, provided the edge
of the walk on which `Y_n` lies is short against the block size.

* `linInterp_mem_segment`: on `[j, j + 1]` the linear interpolation lies on the segment from the
  `j`-th to the `(j+1)`-th point.
* `segment_subset_closedBall_of_mem`: a segment lies in the closed ball of radius its length around
  any of its points.
* `lt_exitTime_of_forall_mem`: a continuous path inside an open set up to time `t` exits after `t`.
* `walkNextBlockExit y x'`: `y` if `y ∈ F` or if the interpolation of `x'` never leaves the open
  block around the grid cell of `y`; otherwise the exit position of the interpolation of `x'` from
  that block.
* `measurable_walkNextBlockExit`: joint measurability in `(y, x')`.
* `interpPathCM_blockExitTimes_succ_eq`: on `{τ_n = k}`, if every walk edge whose segment meets
  the complement of `F` has length at most `s / 2`, then
  `Y_{n+1} = walkNextBlockExit (Y_n) (θ_k x)`; `ae_interpPathCM_blockExitTimes_succ_eq`: the same
  almost surely under the walk law when the short-edge condition holds for the edges of `m`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open WalkPotential

/-- On `[j, j + 1]` the linear interpolation of a sequence lies on the segment from its `j`-th to
its `(j+1)`-th point. -/
theorem linInterp_mem_segment (a : ℕ → ℂ) {r : ℝ} {j : ℕ} (h1 : (j : ℝ) ≤ r)
    (h2 : r ≤ (j : ℝ) + 1) : linInterp a r ∈ segment ℝ (a j) (a (j + 1)) := by
  have hr : 0 ≤ r := (Nat.cast_nonneg j).trans h1
  rcases h2.lt_or_eq with h2 | h2
  · have hfl : ⌊r⌋₊ = j := (Nat.floor_eq_iff hr).2 ⟨h1, h2⟩
    refine ⟨1 - (r - j), r - j, by linarith, by linarith, by ring, ?_⟩
    unfold linInterp
    rw [hfl, Complex.real_smul, Complex.real_smul]
  · have hfl : ⌊r⌋₊ = j + 1 := by
      rw [h2]
      exact_mod_cast Nat.floor_natCast (j + 1)
    have hval : linInterp a r = a (j + 1) := by
      unfold linInterp
      rw [hfl, h2]
      push_cast
      simp
    rw [hval]
    exact right_mem_segment ℝ _ _

/-- On the time window `j ≤ c t ≤ j + 1` the interpolated walk at speed `c` lies on the segment
from `v (x j)` to `v (x (j+1))`. -/
theorem interpPathCM_mem_segment (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (x : ℕ → ℤ) {t : ℝ≥0}
    {j : ℕ} (h1 : (j : ℝ) ≤ c * t) (h2 : c * t ≤ (j : ℝ) + 1) :
    interpPathCM v hc x t ∈ segment ℝ (v (x j)) (v (x (j + 1))) :=
  linInterp_mem_segment (fun k => v (x k)) h1 h2

/-- A segment lies in the closed ball of radius its length around any of its points. -/
theorem segment_subset_closedBall_of_mem {p q y : ℂ} (hy : y ∈ segment ℝ p q) :
    segment ℝ p q ⊆ closedBall y (dist p q) := by
  have hp : y ∈ closedBall p (dist p q) :=
    (convex_closedBall p _).segment_subset (mem_closedBall_self dist_nonneg)
      (by rw [mem_closedBall, dist_comm]) hy
  have hq : y ∈ closedBall q (dist p q) :=
    (convex_closedBall q _).segment_subset (by rw [mem_closedBall]) (mem_closedBall_self dist_nonneg)
      hy
  exact (convex_closedBall y _).segment_subset (mem_closedBall_comm.1 hp) (mem_closedBall_comm.1 hq)

/-- A continuous path that stays in the open set `U` up to time `t` exits `U` strictly after `t`. -/
theorem lt_exitTime_of_forall_mem {α : Type*} [PseudoMetricSpace α] {U : Set α} (hU : IsOpen U)
    {ω : ContinuousPath α} {t : ℝ≥0} (h : ∀ u ≤ t, ω u ∈ U) :
    (t : ℝ≥0∞) < ContinuousPath.exitTime U ω := by
  by_contra hle
  obtain ⟨⟨u, hu⟩, huU⟩ :=
    (ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU t ω).1 (not_lt.1 hle)
  have hu' : u ≤ t := hu
  exact huU (h u hu')

/-- The next block-exit position read from the current one `y` and the restarted walk `x'`: `y` if
`y ∈ F` or if the interpolation of `x'` at speed `c` never leaves the open block around the grid
cell of `y`; otherwise the position of the interpolation of `x'` at its exit time from that
block. -/
noncomputable def walkNextBlockExit (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ)
    (y : ℂ) (x' : ℕ → ℤ) : ℂ :=
  open Classical in
  if y ∉ F ∧ ContinuousPath.exitTime (openBlock s (cellIndex s y).1 (cellIndex s y).2)
      (interpPathCM v hc x') < ⊤ then
    interpPathCM v hc x' (blockExitTimeAt s (interpPathCM v hc x', cellIndex s y))
  else y

/-- The next block-exit position is jointly measurable in the current position and the restarted
walk. -/
theorem measurable_walkNextBlockExit (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) {F : Set ℂ}
    (hF : MeasurableSet F) :
    Measurable fun p : ℂ × (ℕ → ℤ) => walkNextBlockExit v hc s F p.1 p.2 := by
  have hpair : Measurable fun p : ℂ × (ℕ → ℤ) => (interpPathCM v hc p.2, cellIndex s p.1) :=
    ((measurable_interpPathCM v hc).comp measurable_snd).prodMk
      ((measurable_cellIndex s).comp measurable_fst)
  have hexit : Measurable fun q : ContinuousPath ℂ × (ℤ × ℤ) =>
      ContinuousPath.exitTime (openBlock s q.2.1 q.2.2) q.1 :=
    measurable_from_prod_countable_left fun c =>
      ContinuousPath.measurable_exitTime _ (isOpen_openBlock s c.1 c.2)
  have hpos : Measurable fun q : ContinuousPath ℂ × (ℤ × ℤ) => q.1 (blockExitTimeAt s q) :=
    measurable_from_prod_countable_left fun c =>
      ContinuousPath.measurable_eval_of_measurable (fun ω => blockExitTimeAt s (ω, c))
        ((measurable_blockExitTimeAt s).comp (measurable_id.prodMk measurable_const))
  have hS : MeasurableSet {p : ℂ × (ℕ → ℤ) | p.1 ∉ F ∧
      ContinuousPath.exitTime (openBlock s (cellIndex s p.1).1 (cellIndex s p.1).2)
        (interpPathCM v hc p.2) < ⊤} :=
    (measurable_fst hF.compl).inter (measurableSet_lt (hexit.comp hpair) measurable_const)
  unfold walkNextBlockExit
  exact Measurable.ite hS (hpos.comp hpair) measurable_fst

/-- **Short exit edges.** Every walk step carrying a block-exit position off `F` is an edge of
length at most `θ`: for every path `x` and every `n`, if the `n`-th block-exit position `Y_n` of the
interpolation at speed `c` is off `F` and the step `j = ⌊c σ_n⌋` of `x` is an edge of `m`, then
`dist (v x_j) (v x_{j+1}) ≤ θ`. This is the only use the block-exit chain makes of a bound on the
edge lengths. -/
def ExitEdgesShort (m : ℤ → ℤ → ℕ) (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) (F : Set ℂ)
    (θ : ℝ) : Prop :=
  ∀ (x : ℕ → ℤ) (n : ℕ), interpPathCM v hc x (blockExitTimes s F n (interpPathCM v hc x)) ∉ F →
    m (x ⌊c * (blockExitTimes s F n (interpPathCM v hc x) : ℝ)⌋₊)
      (x (⌊c * (blockExitTimes s F n (interpPathCM v hc x) : ℝ)⌋₊ + 1)) ≠ 0 →
    dist (v (x ⌊c * (blockExitTimes s F n (interpPathCM v hc x) : ℝ)⌋₊))
      (v (x (⌊c * (blockExitTimes s F n (interpPathCM v hc x) : ℝ)⌋₊ + 1))) ≤ θ

/-- Short exit edges from a bound on every edge whose segment meets `Fᶜ`. -/
theorem exitEdgesShort_of_forall {m : ℤ → ℤ → ℕ} {v : ℤ → ℂ} {c : ℝ} {hc : 0 ≤ c} {s : ℝ}
    {F : Set ℂ} {θ : ℝ}
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 → (∃ z ∈ segment ℝ (v b) (v b'), z ∉ F) →
      dist (v b) (v b') ≤ θ) :
    ExitEdgesShort m v hc s F θ := by
  intro x n hYF hm
  have hnn : 0 ≤ c * (blockExitTimes s F n (interpPathCM v hc x) : ℝ) :=
    mul_nonneg hc (NNReal.coe_nonneg _)
  exact hM _ _ hm
    ⟨_, interpPathCM_mem_segment v hc x (Nat.floor_le hnn) (Nat.lt_floor_add_one _).le, hYF⟩

/-- Short exit edges are monotone in the length bound. -/
theorem ExitEdgesShort.mono {m : ℤ → ℤ → ℕ} {v : ℤ → ℂ} {c : ℝ} {hc : 0 ≤ c} {s : ℝ}
    {F : Set ℂ} {θ θ' : ℝ} (h : ExitEdgesShort m v hc s F θ) (hθ : θ ≤ θ') :
    ExitEdgesShort m v hc s F θ' :=
  fun x n hYF hm => (h x n hYF hm).trans hθ

/-- **The next block-exit position after the step following a block exit.** If the walk is at
step `k = τ_n` just after the `n`-th block exit of its interpolation, `Y_n ∉ F`, and the step
`j = ⌊c σ_n⌋` of `x` (the step carrying `Y_n`) has length at most `s / 2`, then the `(n+1)`-th block-exit
position is `walkNextBlockExit (Y_n) (θ_k x)`: the interpolation runs from `Y_n` to `v (x k)` on
the current edge inside the block around the grid cell of `Y_n`, and then continues as the
interpolation of the restarted walk. -/
theorem interpPathCM_blockExitTimes_succ_eq (v : ℤ → ℂ) {c : ℝ} (hc : 0 < c) {s : ℝ}
    (hs : 0 < s) (F : Set ℂ) {n k : ℕ} {x : ℕ → ℤ}
    (hmesh : interpPathCM v hc.le x (blockExitTimes s F n (interpPathCM v hc.le x)) ∉ F →
      dist (v (x ⌊c * (blockExitTimes s F n (interpPathCM v hc.le x) : ℝ)⌋₊))
        (v (x (⌊c * (blockExitTimes s F n (interpPathCM v hc.le x) : ℝ)⌋₊ + 1))) ≤ s / 2)
    (hk : walkBlockExitStepTime v hc.le s F n x = k) :
    interpPathCM v hc.le x (blockExitTimes s F (n + 1) (interpPathCM v hc.le x)) =
      walkNextBlockExit v hc.le s F
        (interpPathCM v hc.le x (blockExitTimes s F n (interpPathCM v hc.le x))) (pathShift k x) := by
  set ω := interpPathCM v hc.le x with hω
  set σ := blockExitTimes s F n ω with hσ
  set y := ω σ with hy
  have hkσ : ⌊c * (σ : ℝ)⌋₊ + 1 = k := by
    unfold walkBlockExitStepTime at hk
    split_ifs at hk with hatt
    · exact_mod_cast hk
    · exact absurd hk (ENat.top_ne_natCast k)
  set j := ⌊c * (σ : ℝ)⌋₊ with hj
  have hcσ0 : 0 ≤ c * (σ : ℝ) := mul_nonneg hc.le σ.2
  have hjσ : (j : ℝ) ≤ c * σ := Nat.floor_le hcσ0
  have hσj : c * (σ : ℝ) < j + 1 := Nat.lt_floor_add_one _
  rw [blockExitTimes_succ' s F n ω]
  set ω' := ContinuousPath.shift σ ω with hω'
  have hω'0 : ω' 0 = y := shift_apply_zero σ ω
  unfold walkNextBlockExit
  by_cases hyF : y ∈ F
  · have h0 : firstBlockExitTime s F ω' = 0 := by
      unfold firstBlockExitTime
      simp only [hω'0, hyF, ↓reduceIte]
    simp only [h0, add_zero, hyF, not_true_eq_false, false_and, ↓reduceIte]
    rfl
  set U := openBlock s (cellIndex s y).1 (cellIndex s y).2 with hU
  have hUo : IsOpen U := isOpen_openBlock s _ _
  have hk0 : (0 : ℝ) ≤ k / c := div_nonneg (Nat.cast_nonneg k) hc.le
  have hσk : σ ≤ (k / c : ℝ).toNNReal := by
    rw [Real.le_toNNReal_iff_coe_le hk0, le_div_iff₀ hc, mul_comm, ← hkσ]
    push_cast
    exact hσj.le
  set t : ℝ≥0 := (k / c : ℝ).toNNReal - σ with ht
  have hσt : σ + t = (k / c : ℝ).toNNReal := add_tsub_cancel_of_le hσk
  have hyseg : y ∈ segment ℝ (v (x j)) (v (x (j + 1))) :=
    interpPathCM_mem_segment v hc.le x hjσ hσj.le
  have hlen := hmesh hyF
  have hin : ∀ u ≤ t, ω' u ∈ U := by
    intro u hu
    have hseg : ω' u ∈ segment ℝ (v (x j)) (v (x (j + 1))) := by
      rw [hω', ContinuousPath.shift_apply]
      refine interpPathCM_mem_segment v hc.le x ?_ ?_
      · push_cast
        linarith [mul_nonneg hc.le (NNReal.coe_nonneg u), mul_add c (σ : ℝ) u]
      · have hle : ((σ + u : ℝ≥0) : ℝ) ≤ k / c := by
          have h' : σ + u ≤ (k / c : ℝ).toNNReal := (add_le_add le_rfl hu).trans hσt.le
          exact (Real.le_toNNReal_iff_coe_le hk0).1 h'
        rw [le_div_iff₀ hc] at hle
        rw [← hkσ] at hle
        push_cast at hle ⊢
        linarith
    exact closedBall_subset_openBlock hs (mem_closedCell_cellIndex hs y)
      (closedBall_subset_closedBall hlen (segment_subset_closedBall_of_mem hyseg hseg))
  have hlt : (t : ℝ≥0∞) < ContinuousPath.exitTime U ω' := lt_exitTime_of_forall_mem hUo hin
  have hshift : ContinuousPath.shift t ω' = interpPathCM v hc.le (pathShift k x) := by
    rw [hω', ContinuousPath.shift_add, hσt]
    ext u
    rw [ContinuousPath.shift_apply]
    exact DFunLike.congr_fun (pathShift_interpPathCM v hc x k) u
  have hsum := ContinuousPath.exitTime_shift_add U ω' t hlt
  rw [hshift] at hsum
  by_cases hfin : ContinuousPath.exitTime U (interpPathCM v hc.le (pathShift k x)) < ⊤
  · set e : ℝ≥0 := (ContinuousPath.exitTime U (interpPathCM v hc.le (pathShift k x))).toNNReal
      with he
    have hecoe : ((e : ℝ≥0) : ℝ≥0∞) =
        ContinuousPath.exitTime U (interpPathCM v hc.le (pathShift k x)) :=
      ENNReal.coe_toNNReal hfin.ne
    have hfin' : ContinuousPath.exitTime
        (openBlock s (cellIndex s (ω' 0)).1 (cellIndex s (ω' 0)).2) ω' < ⊤ := by
      rw [hω'0, ← hU, ← hsum, ← hecoe]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.coe_lt_top⟩
    have hfirst : firstBlockExitTime s F ω' = e + t := by
      have h1 := coe_firstBlockExitTime_of_not_mem (s := s) (by rw [hω'0]; exact hyF) hfin'
      rw [hω'0, ← hU, ← hsum, ← hecoe, ← ENNReal.coe_add] at h1
      exact_mod_cast h1
    have hat : blockExitTimeAt s (interpPathCM v hc.le (pathShift k x), cellIndex s y) = e := rfl
    simp only [hyF, not_false_eq_true, hfin, and_self, ↓reduceIte, hat, hfirst]
    rw [← hshift, ContinuousPath.shift_apply, hω', ContinuousPath.shift_apply, add_comm e t]
  · have htop : ContinuousPath.exitTime U (interpPathCM v hc.le (pathShift k x)) = ⊤ :=
      top_le_iff.1 (not_lt.1 hfin)
    have hfirst : firstBlockExitTime s F ω' = 0 := by
      have htop' : ContinuousPath.exitTime U ω' = ⊤ := by
        rw [← hsum, htop, top_add]
      unfold firstBlockExitTime blockExitTimeAt
      simp only [hω'0, hyF, ↓reduceIte]
      rw [← hU, htop']
      rfl
    simp only [hfirst, add_zero, hfin, and_false, ↓reduceIte]
    rfl

/-- **Almost-sure form.** If the walk steps carrying block-exit positions off `F` have length at
most `s / 2` (`ExitEdgesShort`), then almost surely under the walk law, for every
`n` and `k`, on `{τ_n = k}` the `(n+1)`-th block-exit position of the interpolated walk is
`walkNextBlockExit (Y_n) (θ_k x)`. -/
theorem ae_interpPathCM_blockExitTimes_succ_eq (m : ℤ → ℤ → ℕ) (a : ℤ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 < c) {s : ℝ} (hs : 0 < s) (F : Set ℂ)
    (hE : ExitEdgesShort m v hc.le s F (s / 2)) :
    ∀ᵐ x ∂srwLaw m a, ∀ n k : ℕ, walkBlockExitStepTime v hc.le s F n x = k →
      interpPathCM v hc.le x (blockExitTimes s F (n + 1) (interpPathCM v hc.le x)) =
        walkNextBlockExit v hc.le s F
          (interpPathCM v hc.le x (blockExitTimes s F n (interpPathCM v hc.le x)))
          (pathShift k x) := by
  have hadj : ∀ᵐ x ∂srwLaw m a, ∀ j : ℕ, x (j + 1) = x j ∨ m (x j) (x (j + 1)) ≠ 0 :=
    ae_all_iff.2 fun j => ae_iff.2 (MatedCRT.WalkSteps.srwLaw_nonadjacent_null m j a)
  filter_upwards [hadj] with x hx
  intro n k hk
  refine interpPathCM_blockExitTimes_succ_eq v hc hs F (fun hYF => ?_) hk
  rcases hx ⌊c * (blockExitTimes s F n (interpPathCM v hc.le x) : ℝ)⌋₊ with h | h
  · rw [h, dist_self]
    exact (half_pos hs).le
  · exact hE x n hYF h

end BlockExit

end MatedCRT
