import MatedCRT.FirstPass.S6j.WalkDisplacementBlocks

/-!
# Walk side of the upper tail of the exit time (BG20 Lemma 6.10): the successive exits form a chain

Let `w` be a walk path on the mated-CRT map, `σ_k` its successive exit times from the regions
`V^ε(B_δ(η(ε w_{σ_{k-1}})))` without their boundary cells (`SuccessiveExitGaps.succExit`), and `τ` its exit time from
the interior cells `V^ε(B_{r₁}(0)) \ V^ε(∂B_{r₁}(0))`. Suppose every cell meeting `B_R(0)` has diameter at most `c`
and `¬ τ ≤ σ_K` (the walk makes `K` successive exits from the small regions before leaving `B_{r₁}(0)`).
Then, for the unit-speed interpolated walk `f`:

* up to the time `σ_K` the walk stays in `B_{r₁ + c}(0)` (`f` is a convex combination of vertices embedded in that ball),
  so the walk stopped at its exit from `B_R(0)` agrees with `f` there;
* the times `τ_k = σ_k` for `k ≤ K` (and `τ_k = ∞` for `k > K`) form a monotone chain with
  `|f(τ_{k+1}) - f(τ_k)| ≥ δ - c`: the vertex reached at the `(k+1)`-st exit is outside the interior cells of the
  ball `B_δ(η(ε w_{σ_k}))`, so its cell meets the complement of the ball or its boundary sphere, and has diameter at most `c`.

Together with the greedy-versus-chain comparison of displacement times of a continuous path, this is the
deterministic part of the transfer in the proof of Berestycki-Gwynne Lemma 6.10 (arXiv:2003.10320, (6.36)).
-/

namespace MatedCRT.ExitTailUpperWalk

open Set Metric SuccessiveExitGaps WalkDisplacementBlocks
open scoped ENNReal NNReal

variable {ε : ℝ} {η : ℝ → ℂ}

/-- Convexity: if the embedded vertices `w_0, …, w_N` lie in a convex set, so does the unit-speed interpolated walk
on `[0, N]`. -/
theorem interpolatedWalk_mem_of_vertices_mem {S : Set ℂ} (hS : Convex ℝ S) {w : ℕ → ℤ} {N : ℕ}
    (hv : ∀ j ≤ N, vertexPoint ε η (w j) ∈ S) {t : ℝ≥0} (ht : (t : ℝ) ≤ N) :
    interpolatedWalk ε η 1 w t ∈ S := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [interpolatedWalk_one_of_coe_eq w h]
    exact hv N le_rfl
  · have ht0 : (0 : ℝ) ≤ t := t.2
    have hfl : ⌊(t : ℝ)⌋₊ < N := (Nat.floor_lt ht0).2 h
    exact hS.segment_subset (hv _ hfl.le) (hv (⌊(t : ℝ)⌋₊ + 1) hfl)
      (interpolatedWalk_one_mem_segment w (Nat.floor_le ht0) (Nat.lt_floor_add_one _).le)

/-- The successive exit times are nondecreasing. -/
theorem succExit_le_succ (A : ℤ → Set ℤ) (k : ℕ) (w : ℕ → ℤ) :
    succExit A k w ≤ succExit A (k + 1) w := by
  have h : succExit A (k + 1) w = SuccessiveExitStop.nextExit A (succExit A k) w := rfl
  by_cases hk : succExit A k w = ⊤
  · rw [hk]
    simp [h, SuccessiveExitStop.nextExit, hk]
  · obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hk
    rw [h, S6j.nextExit_of_eq_coe A (succExit A k) hj.symm, ← hj]
    exact le_self_add

theorem succExit_mono (A : ℤ → Set ℤ) (w : ℕ → ℤ) : Monotone fun k => succExit A k w :=
  monotone_nat_of_le_succ fun k => succExit_le_succ A k w

/-- The vertex reached at the `(k+1)`-st exit is outside the region used after the `k`-th exit. -/
theorem notMem_of_succExit_succ {A : ℤ → Set ℤ} {k : ℕ} {w : ℕ → ℤ} {j m : ℕ}
    (hj : succExit A k w = j) (hm : succExit A (k + 1) w = m) : w m ∉ A (w j) := by
  have h : succExit A (k + 1) w = SuccessiveExitStop.nextExit A (succExit A k) w := rfl
  rw [h, S6j.nextExit_of_eq_coe A (succExit A k) hj] at hm
  have hfin : vExitTime (A (w j)) (WalkPotential.pathShift j w) ≠ ⊤ := by
    intro ht
    rw [ht] at hm
    simp at hm
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hn] at hm
  have hmn : m = j + n := by exact_mod_cast hm.symm
  have := FrontierSeparation.notMem_of_vExitTime_eq hn.symm
  subst hmn
  simpa [WalkPotential.pathShift] using this

/-- A vertex whose cell has diameter at most `c` and which is not an interior cell vertex of `B_δ(v)` is embedded
at distance at least `δ - c` from `v`: its cell either misses the ball, or meets its boundary sphere. -/
theorem sub_le_dist_of_notMem_interiorCellVertices (hε : 0 ≤ ε) (hη : Continuous η) {v : ℂ} {δ c : ℝ}
    (hδ : 0 < δ) {y : ℤ} (hy : y ∉ interiorCellVertices ε η (ball v δ)) (hc : diam (cell ε η y) ≤ c) :
    δ - c ≤ dist (vertexPoint ε η y) v := by
  have hvp : vertexPoint ε η y ∈ cell ε η y := TruncatedLaws.vertexPoint_mem_cell_of_nonneg hε y
  have hbdd := TruncatedLaws.cell_isBounded_of_continuous (ε := ε) hη y
  have hc0 : 0 ≤ c := (diam_nonneg).trans hc
  by_cases h1 : (cell ε η y ∩ ball v δ).Nonempty
  · have h2 : (cell ε η y ∩ frontier (ball v δ)).Nonempty := by
      by_contra h2
      exact hy ⟨h1, h2⟩
    obtain ⟨p, hp, hpf⟩ := h2
    rw [frontier_ball v hδ.ne'] at hpf
    have hpv : dist p v = δ := hpf
    have h3 := (dist_le_diam_of_mem hbdd hvp hp).trans hc
    linarith [dist_triangle p (vertexPoint ε η y) v, dist_comm p (vertexPoint ε η y)]
  · have : vertexPoint ε η y ∉ ball v δ := fun hmem => h1 ⟨_, hvp, hmem⟩
    have h4 : δ ≤ dist (vertexPoint ε η y) v := not_lt.1 fun hlt => this (mem_ball.2 hlt)
    linarith

/-- The chain of times `τ_k = σ_k` for `k ≤ K` and `τ_k = ∞` for `k > K`, as extended nonnegative reals. -/
noncomputable def chainTime (A : ℤ → Set ℤ) (K : ℕ) (w : ℕ → ℤ) (k : ℕ) : ℝ≥0∞ :=
  if k ≤ K then ENat.toENNReal (succExit A k w) else ⊤

theorem chainTime_mono (A : ℤ → Set ℤ) (K : ℕ) (w : ℕ → ℤ) (k : ℕ) :
    chainTime A K w k ≤ chainTime A K w (k + 1) := by
  unfold chainTime
  by_cases h : k + 1 ≤ K
  · have hk : k ≤ K := by omega
    simp only [hk, h, ↓reduceIte]
    exact ENat.toENNReal_le.2 (succExit_le_succ A k w)
  · simp only [h, ↓reduceIte]
    exact le_top

/-- A finite chain time is a natural number: the exit time is that natural number. -/
theorem exists_succExit_eq_of_chainTime_eq {A : ℤ → Set ℤ} {K : ℕ} {w : ℕ → ℤ} {k : ℕ} (hk : k ≤ K)
    {s : ℝ≥0} (h : chainTime A K w k = (s : ℝ≥0∞)) : ∃ j : ℕ, succExit A k w = j ∧ (s : ℝ) = j := by
  simp only [chainTime, hk, ↓reduceIte] at h
  have hne : succExit A k w ≠ ⊤ := by
    intro ht
    rw [ht, ENat.toENNReal_top] at h
    exact ENNReal.top_ne_coe h
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hne
  refine ⟨j, hj.symm, ?_⟩
  rw [← hj, ENat.toENNReal_coe] at h
  have h2 : (j : ℝ≥0) = s := by
    rw [← ENNReal.coe_inj, ENNReal.coe_natCast]
    exact h
  rw [← h2]
  simp

/-- **Walk side of Berestycki-Gwynne Lemma 6.10.** On the event that the walk makes `K` successive exits from the
small regions before leaving the interior cells of `B_{r₁}(0)`, the interpolated walk `f` (i) stays in `B_{r₁ + c}(0)`
up to `σ_K`, (ii) agrees there with the walk stopped at its exit from `B_R(0)`, and (iii) the chain `τ_k` is
nondecreasing with `|f(τ_{k+1}) - f(τ_k)| ≥ δ - c`. -/
theorem chain_of_not_exit_le (hε : 0 ≤ ε) (hη : Continuous η) {R r₁ c δ : ℝ} (hδ : 0 < δ) (hr₁ : r₁ ≤ R)
    (hrc : r₁ + c ≤ R)
    (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c) {w : ℕ → ℤ} {K : ℕ}
    (hbad : ¬ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) r₁)) w ≤
      succExit (fun z => interiorCellVertices ε η (ball (vertexPoint ε η z) δ)) K w) :
    let A : ℤ → Set ℤ := fun z => interiorCellVertices ε η (ball (vertexPoint ε η z) δ)
    (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ chainTime A K w K → ‖interpolatedWalk ε η 1 w t‖ < r₁ + c) ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ chainTime A K w K →
      stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) t = interpolatedWalk ε η 1 w t) ∧
    (∀ k, chainTime A K w k ≤ chainTime A K w (k + 1)) ∧
    (∀ (k : ℕ) (s t : ℝ≥0), chainTime A K w k = s → chainTime A K w (k + 1) = t →
      δ - c ≤ ‖interpolatedWalk ε η 1 w t - interpolatedWalk ε η 1 w s‖) := by
  intro A
  have hlt : succExit A K w < vExitTime (interiorCellVertices ε η (ball (0 : ℂ) r₁)) w := not_le.1 hbad
  have hne : succExit A K w ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
  -- the vertices up to time `N` are interior cell vertices of `B_{r₁}(0)`, with small cells
  have hmem : ∀ j ≤ N, w j ∈ interiorCellVertices ε η (ball (0 : ℂ) r₁) := fun j hj =>
    WindowStop68.mem_of_lt_vExitTime
      (lt_of_le_of_lt (by rw [← hN]; exact_mod_cast hj : (j : ℕ∞) ≤ succExit A K w) hlt)
  have hdiam : ∀ j ≤ N, diam (cell ε η (w j)) ≤ c ∧ ‖vertexPoint ε η (w j)‖ < r₁ + c := by
    intro j hj
    have hk : w j ∈ cellVertices ε η (ball (0 : ℂ) r₁) := (hmem j hj).1
    obtain ⟨y, hyc, hyb⟩ := hk
    have hd : diam (cell ε η (w j)) ≤ c := hcell _ ⟨y, hyc, ball_subset_ball hr₁ hyb⟩
    refine ⟨hd, ?_⟩
    have := dist_vertexPoint_lt_of_mem_cellVertices hε hη (z := (0 : ℂ)) (hmem j hj).1 hd
    rwa [dist_zero_right] at this
  have hvball : ∀ j ≤ N, vertexPoint ε η (w j) ∈ ball (0 : ℂ) (r₁ + c) := fun j hj => by
    rw [mem_ball_zero_iff]
    exact (hdiam j hj).2
  have hcT : chainTime A K w K = (N : ℝ≥0∞) := by
    simp only [chainTime, le_refl, ↓reduceIte]
    rw [← hN, ENat.toENNReal_coe]
  have hstay : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ chainTime A K w K →
      interpolatedWalk ε η 1 w t ∈ ball (0 : ℂ) (r₁ + c) := by
    intro t ht
    rw [hcT] at ht
    have : (t : ℝ) ≤ N := by exact_mod_cast ht
    exact interpolatedWalk_mem_of_vertices_mem (convex_ball _ _) hvball this
  refine ⟨fun t ht => mem_ball_zero_iff.1 (hstay t ht), ?_, chainTime_mono A K w, ?_⟩
  · intro t ht
    refine stopAtExit_of_coe_le ?_
    refine le_sInf ?_
    rintro s ⟨t', rfl, hout⟩
    by_contra hlt'
    have hlt'' : t' < t := by exact_mod_cast not_le.1 hlt'
    exact hout (ball_subset_ball hrc (hstay t' ((ENNReal.coe_le_coe.2 hlt''.le).trans ht)))
  · intro k s t hs ht
    have hk1 : k + 1 ≤ K := by
      by_contra hk1
      simp only [chainTime, hk1, ↓reduceIte] at ht
      exact ENNReal.top_ne_coe ht
    obtain ⟨j, hj, hjs⟩ := exists_succExit_eq_of_chainTime_eq (by omega) hs
    obtain ⟨m, hm, hmt⟩ := exists_succExit_eq_of_chainTime_eq hk1 ht
    have hmN : m ≤ N := by
      have : succExit A (k + 1) w ≤ succExit A K w := succExit_mono A w hk1
      rw [hm, ← hN] at this
      exact_mod_cast this
    have hjN : j ≤ N := by
      have : succExit A k w ≤ succExit A K w := succExit_mono A w (by omega : k ≤ K)
      rw [hj, ← hN] at this
      exact_mod_cast this
    have hfs : interpolatedWalk ε η 1 w s = vertexPoint ε η (w j) := interpolatedWalk_one_of_coe_eq w hjs
    have hft : interpolatedWalk ε η 1 w t = vertexPoint ε η (w m) := interpolatedWalk_one_of_coe_eq w hmt
    have hout : w m ∉ A (w j) := notMem_of_succExit_succ hj hm
    have := sub_le_dist_of_notMem_interiorCellVertices hε hη hδ hout (hdiam m hmN).1
    rw [hfs, hft, ← dist_eq_norm]
    exact this

end MatedCRT.ExitTailUpperWalk
