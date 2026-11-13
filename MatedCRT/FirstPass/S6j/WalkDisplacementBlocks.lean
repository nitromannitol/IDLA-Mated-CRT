import MatedCRT.FirstPass.S3t.CellGeometry
import MatedCRT.FirstPass.Derived.SuccessiveExitWindows
import MatedCRT.FirstPass.S4S6c.WindowStop68
import MatedCRT.FirstPass.S6j.LitUniformStartInvariance

/-!
# Displacement blocks of the interpolated walk (BG20 Lemma 6.9, the deterministic transfer step)

Let `w` be a walk path on the mated-CRT map whose consecutive cells meet, `v = η(ε w_0)`, and let `n₀` be the exit
time of `w` from the vertex set `V^ε(B_δ(v))`. Suppose every cell meeting `B_R(0)` has diameter at most `c` and
`|v| + δ + 5c < R`. Then:

* up to time `n₀ + 1` the unit-speed interpolated walk `f` stays in `B_{δ+5c}(v) ⊆ B_R(0)`, so the walk stopped at
  its exit from `B_R(0)` agrees with `f` on `[0, n₀ + 1]` (`confinement`, `coe_le_pathExitTime`);
* let `σ_k` be the successive exit times of `w` from the regions `V^ε(B_q(η(ε w_{σ_{k-1}})))` and
  `m_k = min(σ_k, n₀ + 1)` (`truncExit`). On each block `[m_k, m_{k+1}]` the interpolated walk stays within
  `q + 3c` of `η(ε w_{m_k})`, hence moves less than `2q + 6c` (`norm_sub_lt_on_block`);
* `m_0 = 0`, `m_K = n₀ + 1` when `n₀ < σ_K`, and `|f(n₀) - f(0)| ≥ δ`.

These are the block hypotheses of the lower comparison of walk exit times with the displacement times of a path
(the `k`-th displacement time at scale `2q + 6c` is at least `m_k`). This is the deterministic part of the transfer in
the proof of Berestycki-Gwynne Lemma 6.9 (arXiv:2003.10320).
-/

namespace MatedCRT.WalkDisplacementBlocks

open Set Metric
open scoped ENNReal NNReal

variable {ε : ℝ} {η : ℝ → ℂ}

/-- At a natural time `j` the unit-speed interpolated walk is the `j`-th embedded vertex. -/
theorem interpolatedWalk_one_of_coe_eq (w : ℕ → ℤ) {j : ℕ} {t : ℝ≥0} (ht : (t : ℝ) = j) :
    interpolatedWalk ε η 1 w t = vertexPoint ε η (w j) := by
  have hs : (1 : ℝ) * (t : ℝ) = j := by rw [one_mul, ht]
  simp only [interpolatedWalk, hs, Nat.floor_natCast, sub_self, Complex.ofReal_zero, sub_zero,
    Complex.ofReal_one, one_mul, zero_mul, add_zero]

/-- On `[j, j + 1]` the unit-speed interpolated walk lies on the segment between the `j`-th and the `(j+1)`-st
embedded vertices. -/
theorem interpolatedWalk_one_mem_segment (w : ℕ → ℤ) {j : ℕ} {t : ℝ≥0} (h1 : (j : ℝ) ≤ t)
    (h2 : (t : ℝ) ≤ j + 1) :
    interpolatedWalk ε η 1 w t ∈ segment ℝ (vertexPoint ε η (w j)) (vertexPoint ε η (w (j + 1))) := by
  have ht0 : (0 : ℝ) ≤ t := t.2
  rcases eq_or_lt_of_le h2 with h | h
  · rw [interpolatedWalk_one_of_coe_eq w (j := j + 1) (by rw [h]; push_cast; ring)]
    exact right_mem_segment ℝ _ _
  · have hfl : ⌊(t : ℝ)⌋₊ = j := (Nat.floor_eq_iff ht0).2 ⟨h1, h⟩
    refine ⟨1 - ((t : ℝ) - j), (t : ℝ) - j, by linarith, by linarith, by ring, ?_⟩
    simp only [interpolatedWalk, one_mul, hfl, Complex.real_smul]

/-- A vertex whose cell meets `B_r(z)` and has diameter at most `c` is embedded within `r + c` of `z`. -/
theorem dist_vertexPoint_lt_of_mem_cellVertices (hε : 0 ≤ ε) (hη : Continuous η) {k : ℤ} {z : ℂ}
    {r c : ℝ} (hk : k ∈ cellVertices ε η (ball z r)) (hc : diam (cell ε η k) ≤ c) :
    dist (vertexPoint ε η k) z < r + c := by
  obtain ⟨y, hyk, hyz⟩ := hk
  have h1 : dist (vertexPoint ε η k) y ≤ c :=
    (dist_le_diam_of_mem (TruncatedLaws.cell_isBounded_of_continuous hη k)
      (TruncatedLaws.vertexPoint_mem_cell_of_nonneg hε k) hyk).trans hc
  have h2 : dist y z < r := hyz
  linarith [dist_triangle (vertexPoint ε η k) y z]

/-- `‖y‖ ≤ dist y v + ‖v‖`. -/
theorem norm_le_dist_add_norm (y v : ℂ) : ‖y‖ ≤ dist y v + ‖v‖ := by
  calc ‖y‖ = dist y 0 := (dist_zero_right y).symm
    _ ≤ dist y v + dist v 0 := dist_triangle _ _ _
    _ = dist y v + ‖v‖ := by rw [dist_zero_right]

/-- One step of the walk among small cells. If the cell of `a` has diameter at most `c`, `a` is embedded within `D`
of `v`, `‖v‖ + D + c < R`, every cell meeting `B_R(0)` has diameter at most `c`, and the cells of `a` and `b` meet,
then the cell of `b` has diameter at most `c` and `b` is embedded within `D + 2c` of `v`. -/
theorem step_of_cells_meet (hε : 0 ≤ ε) (hη : Continuous η) {R c D : ℝ}
    (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c)
    {v : ℂ} {a b : ℤ} (ha : diam (cell ε η a) ≤ c) (hav : dist (vertexPoint ε η a) v < D)
    (hD : ‖v‖ + D + c < R) (hab : (cell ε η a ∩ cell ε η b).Nonempty) :
    diam (cell ε η b) ≤ c ∧ dist (vertexPoint ε η b) v < D + 2 * c := by
  obtain ⟨y, hya, hyb⟩ := hab
  have hy : dist y (vertexPoint ε η a) ≤ c := by
    rw [dist_comm]
    exact (dist_le_diam_of_mem (TruncatedLaws.cell_isBounded_of_continuous hη a)
      (TruncatedLaws.vertexPoint_mem_cell_of_nonneg hε a) hya).trans ha
  have hyR : y ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]
    linarith [norm_le_dist_add_norm y v, dist_triangle y (vertexPoint ε η a) v]
  have hb : diam (cell ε η b) ≤ c := hcell b ⟨y, hyb, hyR⟩
  refine ⟨hb, ?_⟩
  have h2 := TruncatedLaws.dist_vertexPoint_le_two_mul_of_cells_meet hε hη ⟨y, hya, hyb⟩ ha hb
  linarith [dist_triangle (vertexPoint ε η b) (vertexPoint ε η a) v,
    dist_comm (vertexPoint ε η a) (vertexPoint ε η b)]

/-- **Confinement.** Up to one step after the exit time `n₀` of the walk from the cells of `B_δ(v)`,
`v = η(ε w_0)`, the cells visited have diameter at most `c` and the vertices are embedded within `δ + 5c` of `v`. -/
theorem confinement (hε : 0 ≤ ε) (hη : Continuous η) {R c δ : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c)
    {w : ℕ → ℤ} (hadj : ∀ j, (cell ε η (w j) ∩ cell ε η (w (j + 1))).Nonempty)
    (hconf : ‖vertexPoint ε η (w 0)‖ + δ + 5 * c < R) {n₀ : ℕ}
    (hn₀ : vExitTime (cellVertices ε η (ball (vertexPoint ε η (w 0)) δ)) w = n₀) :
    ∀ j ≤ n₀ + 1, diam (cell ε η (w j)) ≤ c ∧
      dist (vertexPoint ε η (w j)) (vertexPoint ε η (w 0)) < δ + 5 * c := by
  set v := vertexPoint ε η (w 0) with hv
  have hin : ∀ j < n₀, diam (cell ε η (w j)) ≤ c ∧ dist (vertexPoint ε η (w j)) v < δ + c := by
    intro j hj
    have hjV : w j ∈ cellVertices ε η (ball v δ) :=
      WindowStop68.mem_of_lt_vExitTime (by rw [hn₀]; exact_mod_cast hj)
    obtain ⟨y, hyc, hyb⟩ := hjV
    have hyR : y ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right]
      have : dist y v < δ := hyb
      linarith [norm_le_dist_add_norm y v]
    have hd : diam (cell ε η (w j)) ≤ c := hcell _ ⟨y, hyc, hyR⟩
    exact ⟨hd, dist_vertexPoint_lt_of_mem_cellVertices hε hη ⟨y, hyc, hyb⟩ hd⟩
  have hpos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · exfalso
      have h0V : w 0 ∈ cellVertices ε η (ball v δ) :=
        ⟨v, TruncatedLaws.vertexPoint_mem_cell_of_nonneg hε (w 0), mem_ball_self hδ⟩
      have h0 : vExitTime (cellVertices ε η (ball v δ)) w = ((0 : ℕ) : ℕ∞) := by rw [hn₀, h]
      exact FrontierSeparation.notMem_of_vExitTime_eq h0 h0V
    · exact h
  obtain ⟨hd1, hv1⟩ := hin (n₀ - 1) (by omega)
  have hadj' : (cell ε η (w (n₀ - 1)) ∩ cell ε η (w n₀)).Nonempty := by
    have := hadj (n₀ - 1)
    rwa [Nat.sub_add_cancel hpos] at this
  obtain ⟨hd2, hv2⟩ := step_of_cells_meet hε hη hcell hd1 hv1 (by linarith) hadj'
  obtain ⟨hd3, hv3⟩ := step_of_cells_meet hε hη hcell hd2 hv2 (by linarith) (hadj n₀)
  intro j hj
  rcases lt_or_ge j n₀ with h | h
  · obtain ⟨ha, hb⟩ := hin j h
    exact ⟨ha, by linarith⟩
  · rcases eq_or_lt_of_le h with h' | h'
    · subst h'
      exact ⟨hd2, by linarith⟩
    · have : j = n₀ + 1 := by omega
      subst this
      exact ⟨hd3, by linarith⟩

/-- Up to time `n₀ + 1` the unit-speed interpolated walk stays within `δ + 5c` of `v = η(ε w_0)`. -/
theorem interpolatedWalk_mem_ball_of_le (hε : 0 ≤ ε) (hη : Continuous η) {R c δ : ℝ} (hδ : 0 < δ)
    (hc : 0 ≤ c) (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c)
    {w : ℕ → ℤ} (hadj : ∀ j, (cell ε η (w j) ∩ cell ε η (w (j + 1))).Nonempty)
    (hconf : ‖vertexPoint ε η (w 0)‖ + δ + 5 * c < R) {n₀ : ℕ}
    (hn₀ : vExitTime (cellVertices ε η (ball (vertexPoint ε η (w 0)) δ)) w = n₀)
    {t : ℝ≥0} (ht : (t : ℝ) ≤ n₀ + 1) :
    interpolatedWalk ε η 1 w t ∈ ball (vertexPoint ε η (w 0)) (δ + 5 * c) := by
  have hcf := confinement hε hη hδ hc hcell hadj hconf hn₀
  set j := min ⌊(t : ℝ)⌋₊ n₀ with hj
  have hjn : j ≤ n₀ := min_le_right _ _
  have h1 : (j : ℝ) ≤ t := (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le t.2)
  have h2 : (t : ℝ) ≤ j + 1 := by
    rcases le_total ⌊(t : ℝ)⌋₊ n₀ with h | h
    · rw [hj, min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · rw [hj, min_eq_right h]
      exact ht
  exact (convex_ball _ _).segment_subset (mem_ball.2 (hcf j (by omega)).2)
    (mem_ball.2 (hcf (j + 1) (by omega)).2) (interpolatedWalk_one_mem_segment w h1 h2)

/-- The exit time of the interpolated walk from `B_R(0)` is at least `n₀ + 1`. -/
theorem coe_le_pathExitTime (hε : 0 ≤ ε) (hη : Continuous η) {R c δ : ℝ} (hδ : 0 < δ)
    (hc : 0 ≤ c) (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c)
    {w : ℕ → ℤ} (hadj : ∀ j, (cell ε η (w j) ∩ cell ε η (w (j + 1))).Nonempty)
    (hconf : ‖vertexPoint ε η (w 0)‖ + δ + 5 * c < R) {n₀ : ℕ}
    (hn₀ : vExitTime (cellVertices ε η (ball (vertexPoint ε η (w 0)) δ)) w = n₀)
    {t : ℝ≥0} (ht : (t : ℝ) ≤ n₀ + 1) :
    (t : ℝ≥0∞) ≤ _root_.HarmonicBalls.pathExitTime (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) := by
  refine le_sInf ?_
  rintro s ⟨t', rfl, hout⟩
  by_contra hlt
  have hlt' : t' < t := by exact_mod_cast not_le.1 hlt
  have ht' : (t' : ℝ) ≤ n₀ + 1 := (NNReal.coe_lt_coe.2 hlt').le.trans ht
  refine hout (ball_subset_ball' ?_ (interpolatedWalk_mem_ball_of_le hε hη hδ hc hcell hadj hconf hn₀ ht'))
  rw [dist_zero_right]
  linarith

/-- The walk stopped at its exit from `B_R(0)` agrees with the interpolated walk up to time `n₀ + 1`. -/
theorem stopAtExit_eq_of_le (hε : 0 ≤ ε) (hη : Continuous η) {R c δ : ℝ} (hδ : 0 < δ)
    (hc : 0 ≤ c) (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c)
    {w : ℕ → ℤ} (hadj : ∀ j, (cell ε η (w j) ∩ cell ε η (w (j + 1))).Nonempty)
    (hconf : ‖vertexPoint ε η (w 0)‖ + δ + 5 * c < R) {n₀ : ℕ}
    (hn₀ : vExitTime (cellVertices ε η (ball (vertexPoint ε η (w 0)) δ)) w = n₀)
    {t : ℝ≥0} (ht : (t : ℝ) ≤ n₀ + 1) :
    stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) t = interpolatedWalk ε η 1 w t :=
  stopAtExit_of_coe_le (coe_le_pathExitTime hε hη hδ hc hcell hadj hconf hn₀ ht)

/-- The `k`-th successive exit time `σ_k` of `w` from the regions `A`, truncated at `N`, as a natural number. -/
noncomputable def truncExit (A : ℤ → Set ℤ) (w : ℕ → ℤ) (N k : ℕ) : ℕ :=
  if SuccessiveExitGaps.succExit A k w = ⊤ then N else min (SuccessiveExitGaps.succExit A k w).toNat N

theorem truncExit_le (A : ℤ → Set ℤ) (w : ℕ → ℤ) (N k : ℕ) : truncExit A w N k ≤ N := by
  unfold truncExit
  split_ifs <;> omega

theorem truncExit_zero (A : ℤ → Set ℤ) (w : ℕ → ℤ) (N : ℕ) : truncExit A w N 0 = 0 := by
  simp [truncExit, SuccessiveExitGaps.succExit, S6j.nextExitSchedule]

/-- If `n₀ < σ_K`, then `min(σ_K, n₀ + 1) = n₀ + 1`. -/
theorem truncExit_of_lt (A : ℤ → Set ℤ) (w : ℕ → ℤ) {n₀ K : ℕ}
    (h : (n₀ : ℕ∞) < SuccessiveExitGaps.succExit A K w) : truncExit A w (n₀ + 1) K = n₀ + 1 := by
  unfold truncExit
  split_ifs with ht
  · rfl
  · obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.mp ht
    rw [← hi] at h ⊢
    have : n₀ < i := by exact_mod_cast h
    simp only [ENat.toNat_natCast]
    omega

/-- Below the truncation level, `min(σ_k, N) = σ_k`. -/
theorem succExit_eq_truncExit (A : ℤ → Set ℤ) (w : ℕ → ℤ) {N k : ℕ} (h : truncExit A w N k < N) :
    SuccessiveExitGaps.succExit A k w = truncExit A w N k := by
  unfold truncExit at h ⊢
  split_ifs at h ⊢ with ht
  · omega
  · obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.mp ht
    rw [← hi] at h ⊢
    simp only [ENat.toNat_natCast] at h ⊢
    have : min i N = i := by omega
    rw [this]

/-- **Block bound.** On the `k`-th truncated block `[m_k, m_{k+1}]`, `m_k = min(σ_k, n₀ + 1)`, of the successive
exits from the cells of `B_q(η(ε ·))`, the unit-speed interpolated walk stays within `q + 3c` of `η(ε w_{m_k})`. -/
theorem dist_lt_on_block (hε : 0 ≤ ε) (hη : Continuous η) {R c δ q : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    (hq : 0 < q) (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c)
    {w : ℕ → ℤ} (hadj : ∀ j, (cell ε η (w j) ∩ cell ε η (w (j + 1))).Nonempty)
    (hconf : ‖vertexPoint ε η (w 0)‖ + δ + 5 * c < R) {n₀ : ℕ}
    (hn₀ : vExitTime (cellVertices ε η (ball (vertexPoint ε η (w 0)) δ)) w = n₀) (k : ℕ) {u : ℝ≥0}
    (h1 : (truncExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) q)) w (n₀ + 1) k : ℝ) ≤ u)
    (h2 : (u : ℝ) ≤ truncExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) q)) w (n₀ + 1) (k + 1)) :
    dist (interpolatedWalk ε η 1 w u) (vertexPoint ε η
      (w (truncExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) q)) w (n₀ + 1) k))) < q + 3 * c := by
  set A : ℤ → Set ℤ := fun z => cellVertices ε η (ball (vertexPoint ε η z) q) with hA
  set m := truncExit A w (n₀ + 1) k with hm
  set M := truncExit A w (n₀ + 1) (k + 1) with hM
  have hcf := confinement hε hη hδ hc hcell hadj hconf hn₀
  have hmN : m ≤ n₀ + 1 := truncExit_le A w (n₀ + 1) k
  have hMN : M ≤ n₀ + 1 := truncExit_le A w (n₀ + 1) (k + 1)
  have hq3 : 0 < q + 3 * c := by linarith
  rcases eq_or_lt_of_le hmN with hmeq | hmlt
  · have hu : (u : ℝ) = (m : ℕ) := by
      refine le_antisymm ?_ h1
      calc (u : ℝ) ≤ M := h2
        _ ≤ (m : ℕ) := by rw [hmeq]; exact_mod_cast hMN
    rw [interpolatedWalk_one_of_coe_eq w hu, dist_self]
    exact hq3
  · have hk : SuccessiveExitGaps.succExit A k w = (m : ℕ∞) := succExit_eq_truncExit A w hmlt
    have hk1 : SuccessiveExitGaps.succExit A (k + 1) w =
        (m : ℕ∞) + vExitTime (A (w m)) (WalkPotential.pathShift m w) :=
      S6j.nextExit_of_eq_coe A (SuccessiveExitGaps.succExit A k) hk
    set E := vExitTime (A (w m)) (WalkPotential.pathShift m w) with hE
    have hwin : ∀ j, m ≤ j → ((j - m : ℕ) : ℕ∞) < E → w j ∈ A (w m) := by
      intro j hmj hj
      have h' := WindowStop68.mem_of_lt_vExitTime hj
      simp only [WalkPotential.pathShift, Nat.add_sub_of_le hmj] at h'
      exact h'
    have hEpos : ((0 : ℕ) : ℕ∞) < E := by
      apply WindowStop68.lt_vExitTime_of_forall
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [WalkPotential.pathShift, add_zero]
      exact ⟨vertexPoint ε η (w m), TruncatedLaws.vertexPoint_mem_cell_of_nonneg hε (w m), mem_ball_self hq⟩
    have pick : ∀ J : ℕ, m ≤ J → J ≤ n₀ → ((J - m : ℕ) : ℕ∞) < E → (J : ℝ) ≤ u → (u : ℝ) ≤ J + 1 →
        dist (interpolatedWalk ε η 1 w u) (vertexPoint ε η (w m)) < q + 3 * c := by
      intro J hmJ hJn hJE hJ1 hJ2
      have hdj := (hcf J (by omega)).1
      have hdj1 := (hcf (J + 1) (by omega)).1
      have e1 := dist_vertexPoint_lt_of_mem_cellVertices hε hη (hwin J hmJ hJE) hdj
      have e2 := TruncatedLaws.dist_vertexPoint_le_two_mul_of_cells_meet hε hη (hadj J) hdj hdj1
      have g1 : dist (vertexPoint ε η (w J)) (vertexPoint ε η (w m)) < q + 3 * c := by linarith
      have g2 : dist (vertexPoint ε η (w (J + 1))) (vertexPoint ε η (w m)) < q + 3 * c := by
        linarith [dist_triangle (vertexPoint ε η (w (J + 1))) (vertexPoint ε η (w J)) (vertexPoint ε η (w m)),
          dist_comm (vertexPoint ε η (w J)) (vertexPoint ε η (w (J + 1)))]
      exact mem_ball.1 ((convex_ball _ _).segment_subset (mem_ball.2 g1) (mem_ball.2 g2)
        (interpolatedWalk_one_mem_segment w hJ1 hJ2))
    have hmu : m ≤ ⌊(u : ℝ)⌋₊ := Nat.le_floor h1
    have hfl1 : ((⌊(u : ℝ)⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le u.2
    have hfl2 : (u : ℝ) ≤ ⌊(u : ℝ)⌋₊ + 1 := (Nat.lt_floor_add_one _).le
    by_cases hEt : E = ⊤
    · have hsucc : SuccessiveExitGaps.succExit A (k + 1) w = ⊤ := by rw [hk1, hEt]; exact add_top _
      have hMeq : M = n₀ + 1 := by
        show truncExit A w (n₀ + 1) (k + 1) = n₀ + 1
        unfold truncExit
        simp [hsucc]
      by_cases hfl : ⌊(u : ℝ)⌋₊ ≤ n₀
      · exact pick _ hmu hfl (by rw [hEt]; exact ENat.natCast_lt_top _) hfl1 hfl2
      · have hu : (u : ℝ) = n₀ + 1 := by
          refine le_antisymm ?_ ?_
          · have := h2; rw [hMeq] at this; push_cast at this; exact this
          · have : ((n₀ + 1 : ℕ) : ℝ) ≤ ⌊(u : ℝ)⌋₊ := by exact_mod_cast (by omega : n₀ + 1 ≤ ⌊(u : ℝ)⌋₊)
            push_cast at this
            linarith
        exact pick n₀ (by omega) le_rfl (by rw [hEt]; exact ENat.natCast_lt_top _) (by linarith) (by linarith)
    · obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hEt
      have hepos : 0 < e := by rw [← he] at hEpos; exact_mod_cast hEpos
      have hsucc : SuccessiveExitGaps.succExit A (k + 1) w = ((m + e : ℕ) : ℕ∞) := by
        rw [hk1, ← he, Nat.cast_add]
      have hMeq : M = min (m + e) (n₀ + 1) := by
        show truncExit A w (n₀ + 1) (k + 1) = min (m + e) (n₀ + 1)
        unfold truncExit
        simp only [hsucc, ENat.natCast_ne_top, ↓reduceIte, ENat.toNat_natCast]
      by_cases hfl : ⌊(u : ℝ)⌋₊ ≤ n₀ ∧ ⌊(u : ℝ)⌋₊ - m < e
      · exact pick _ hmu hfl.1 (by rw [← he]; exact_mod_cast hfl.2) hfl1 hfl2
      · have hMfl : M ≤ ⌊(u : ℝ)⌋₊ := by rw [hMeq]; omega
        have hMu : (M : ℝ) ≤ u := (Nat.cast_le.2 hMfl).trans hfl1
        have huM : (u : ℝ) = M := le_antisymm h2 hMu
        have hmM : m < M := by rw [hMeq]; omega
        have hM1 : ((M - 1 : ℕ) : ℝ) + 1 = M := by
          have : M - 1 + 1 = M := by omega
          exact_mod_cast this
        exact pick (M - 1) (by omega) (by omega) (by rw [← he]; exact_mod_cast (by omega : M - 1 - m < e))
          (by linarith) (by linarith)

/-- **The block hypotheses of the displacement-time comparison** for the walk stopped at its exit from `B_R(0)`:
with `τ_k = min(σ_k, n₀ + 1)`, on every block `τ_k ≤ s ≤ t ≤ τ_{k+1}` the stopped interpolated walk moves less than
`2q + 6c`. -/
theorem norm_sub_lt_on_block (hε : 0 ≤ ε) (hη : Continuous η) {R c δ q : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    (hq : 0 < q) (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c)
    {w : ℕ → ℤ} (hadj : ∀ j, (cell ε η (w j) ∩ cell ε η (w (j + 1))).Nonempty)
    (hconf : ‖vertexPoint ε η (w 0)‖ + δ + 5 * c < R) {n₀ : ℕ}
    (hn₀ : vExitTime (cellVertices ε η (ball (vertexPoint ε η (w 0)) δ)) w = n₀) (k : ℕ) (s t : ℝ≥0)
    (hs : ((truncExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) q)) w (n₀ + 1) k : ℕ) : ℝ≥0∞) ≤ s)
    (hst : s ≤ t)
    (ht : (t : ℝ≥0∞) ≤
      ((truncExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) q)) w (n₀ + 1) (k + 1) : ℕ) : ℝ≥0∞)) :
    ‖stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) t -
      stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) s‖ < 2 * q + 6 * c := by
  set A : ℤ → Set ℤ := fun z => cellVertices ε η (ball (vertexPoint ε η z) q) with hA
  have hs' : (truncExit A w (n₀ + 1) k : ℝ) ≤ s := by exact_mod_cast hs
  have ht' : (t : ℝ) ≤ truncExit A w (n₀ + 1) (k + 1) := by exact_mod_cast ht
  have hst' : (s : ℝ) ≤ t := hst
  have hMN : (truncExit A w (n₀ + 1) (k + 1) : ℝ) ≤ n₀ + 1 := by
    exact_mod_cast truncExit_le A w (n₀ + 1) (k + 1)
  rw [stopAtExit_eq_of_le hε hη hδ hc hcell hadj hconf hn₀ (ht'.trans hMN),
    stopAtExit_eq_of_le hε hη hδ hc hcell hadj hconf hn₀ ((hst'.trans ht').trans hMN), ← dist_eq_norm]
  have d1 := dist_lt_on_block hε hη hδ hc hq hcell hadj hconf hn₀ k (hs'.trans hst') ht'
  have d2 := dist_lt_on_block hε hη hδ hc hq hcell hadj hconf hn₀ k hs' (hst'.trans ht')
  linarith [dist_triangle_right (interpolatedWalk ε η 1 w t) (interpolatedWalk ε η 1 w s)
    (vertexPoint ε η (w (truncExit A w (n₀ + 1) k)))]

/-- The first truncated block starts at time `0`. -/
theorem coe_truncExit_zero (A : ℤ → Set ℤ) (w : ℕ → ℤ) (N : ℕ) :
    ((truncExit A w N 0 : ℕ) : ℝ≥0∞) = 0 := by
  rw [truncExit_zero, Nat.cast_zero]

/-- **The displacement at the exit time.** At the exit time `n₀` from the cells of `B_δ(η(ε w_0))`, the stopped
interpolated walk is at distance at least `δ` from its starting point. -/
theorem le_norm_stopAtExit_sub (hε : 0 ≤ ε) (hη : Continuous η) {R c δ : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c)
    {w : ℕ → ℤ} (hadj : ∀ j, (cell ε η (w j) ∩ cell ε η (w (j + 1))).Nonempty)
    (hconf : ‖vertexPoint ε η (w 0)‖ + δ + 5 * c < R) {n₀ : ℕ}
    (hn₀ : vExitTime (cellVertices ε η (ball (vertexPoint ε η (w 0)) δ)) w = n₀) :
    δ ≤ ‖stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) (n₀ : ℝ≥0) -
      stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) 0‖ := by
  rw [stopAtExit_eq_of_le hε hη hδ hc hcell hadj hconf hn₀ (t := (n₀ : ℝ≥0))
      (by rw [NNReal.coe_natCast]; linarith),
    stopAtExit_eq_of_le hε hη hδ hc hcell hadj hconf hn₀ (t := 0) (by rw [NNReal.coe_zero]; positivity),
    interpolatedWalk_one_of_coe_eq w (j := n₀) (by rw [NNReal.coe_natCast]),
    interpolatedWalk_one_of_coe_eq w (j := 0) (by rw [NNReal.coe_zero, Nat.cast_zero]), ← dist_eq_norm]
  have hout : w n₀ ∉ cellVertices ε η (ball (vertexPoint ε η (w 0)) δ) :=
    FrontierSeparation.notMem_of_vExitTime_eq hn₀
  by_contra hlt
  exact hout ⟨vertexPoint ε η (w n₀), TruncatedLaws.vertexPoint_mem_cell_of_nonneg hε (w n₀),
    mem_ball.2 (not_le.1 hlt)⟩

end MatedCRT.WalkDisplacementBlocks
