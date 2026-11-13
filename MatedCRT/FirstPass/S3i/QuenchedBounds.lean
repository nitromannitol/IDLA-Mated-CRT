import MatedCRT.FirstPass.S3i.Proof
import MatedCRT.FirstPass.S3i.LensDefs
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellWindow
import MatedCRT.FirstPass.S3i.StrongMarkov
import MatedCRT.FirstPass.S3i.LensBE
import MatedCRT.FirstPass.S3i.LensGeometry
import MatedCRT.FirstPass.S3i.BoundaryCell

/-!
# The two quenched estimates on a good environment (plan Lemma 7)

Plan section 7.
Lemmas 1, 2, 4, 5, 6 of the plan are taken as hypotheses with the plan's exact types, named
`FP36LemmaTwo`, `FP36LemmaFour`, `FP36LemmaFive`, `FP36LemmaSix`.

This file proves the start and finite-exit clause (plan steps 1-4) and the lens clause (plan steps 5-12).

Terminology: quenched and annealed laws (Armstrong-Kuusi-Mourrat); same-walk coupling and the one-sided boundary
estimate (Gwynne-Miller-Sheffield, arXiv:1807.07511); Lawler-Limic for the strong Markov property of random walk.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

open Classical in

/-! ## Deterministic geometry of the embedded walk -/

lemma vertexPoint_mem_cell_fp36 {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k := by
  unfold cell vertexPoint
  exact ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

lemma cell_subset_ball_of_mem_interiorCellVertices_fp36 {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    {z : ℂ} {r : ℝ} {k : ℤ} (hk : k ∈ interiorCellVertices ε η (ball z r)) :
    cell ε η k ⊆ ball z r := by
  have hk' : k ∈ cellVertices ε η (ball z r) ∧ k ∉ cellVertices ε η (frontier (ball z r)) := hk
  have hconn : IsPreconnected (cell ε η k) := by
    unfold cell
    exact isPreconnected_Icc.image _ hη.continuousOn
  have hne : (cell ε η k ∩ ball z r).Nonempty := hk'.1
  have hv : IsOpen (closure (ball z r))ᶜ := isClosed_closure.isOpen_compl
  refine hconn.subset_left_of_subset_union (v := (closure (ball z r))ᶜ) isOpen_ball hv ?_ ?_ hne
  · exact Set.disjoint_left.2 fun c hc hc' => hc' (subset_closure hc)
  · intro c hc
    by_cases hcb : c ∈ ball z r
    · exact Or.inl hcb
    · refine Or.inr ?_
      intro hcl
      apply hk'.2
      refine (⟨c, hc, ?_⟩ : (cell ε η k ∩ frontier (ball z r)).Nonempty)
      exact ⟨hcl, by rw [isOpen_ball.interior_eq]; exact hcb⟩

lemma vertexPoint_mem_ball_of_interior_fp36 {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) (hη : Continuous η)
    {z : ℂ} {r : ℝ} {k : ℤ} (hk : k ∈ interiorCellVertices ε η (ball z r)) :
    vertexPoint ε η k ∈ ball z r :=
  cell_subset_ball_of_mem_interiorCellVertices_fp36 hη hk (vertexPoint_mem_cell_fp36 hε η k)

lemma vertexPoint_not_mem_of_not_mem_cellVertices_fp36 {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) {U : Set ℂ}
    {k : ℤ} (hk : k ∉ cellVertices ε η U) : vertexPoint ε η k ∉ U := by
  intro h
  exact hk (show (cell ε η k ∩ U).Nonempty from ⟨vertexPoint ε η k, vertexPoint_mem_cell_fp36 hε η k, h⟩)

lemma interpolatedWalk_zero_fp36 {ε m : ℝ} {η : ℝ → ℂ} (x : ℕ → ℤ) :
    interpolatedWalk ε η m x 0 = vertexPoint ε η (x 0) := by
  simp [interpolatedWalk]

/-- If some vertex of the walk lies outside `U`, the interpolated walk leaves `U` by its vertex time
`n / mε` (Armstrong-Kuusi-Mourrat; plan step 3). -/
lemma pathExitTime_lt_top_of_vertex_not_mem_fp36 {ε mε : ℝ} {η : ℝ → ℂ} {U : Set ℂ} {x : ℕ → ℤ}
    (hm : 0 < mε) {n : ℕ} (hn : vertexPoint ε η (x n) ∉ U) :
    HarmonicBalls.pathExitTime U (interpolatedWalk ε η mε x) < ⊤ := by
  have hmem : (((n : ℝ) / mε).toNNReal : ℝ≥0∞) ∈
      {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧ interpolatedWalk ε η mε x t ∉ U} :=
    ⟨((n : ℝ) / mε).toNNReal, rfl, by rw [interpolatedWalk_natCast_div hm]; exact hn⟩
  exact lt_of_le_of_lt (sInf_le hmem) ENNReal.coe_lt_top

/-! ## Exit times of the discrete walk -/

lemma vExitTime_toNat_not_mem_fp36 {A : Set ℤ} {x : ℕ → ℤ} (h : vExitTime A x < ⊤) :
    x (vExitTime A x).toNat ∉ A := by
  classical
  unfold vExitTime at h ⊢
  split_ifs at h ⊢ with hex
  · rw [ENat.toNat_natCast]
    exact Nat.find_spec hex
  · exact absurd h (lt_irrefl _)

lemma measurableSet_vExitTime_lt_top_fp36 (A : Set ℤ) :
    MeasurableSet {x : ℕ → ℤ | vExitTime A x < ⊤} := by
  have hset : {x : ℕ → ℤ | vExitTime A x < ⊤} = ⋃ n : ℕ, (fun x : ℕ → ℤ => x n) ⁻¹' Aᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_iUnion, mem_preimage, mem_compl_iff]
    unfold vExitTime
    split_ifs with hex
    · exact ⟨fun _ => hex, fun _ => ENat.natCast_lt_top _⟩
    · exact ⟨fun h => absurd h (lt_irrefl _), fun ⟨n, hn⟩ => absurd ⟨n, hn⟩ hex⟩
  rw [hset]
  exact MeasurableSet.iUnion fun n => (measurable_pi_apply n) MeasurableSet.of_discrete

/-! ## Clause 1: the walk is good a.s. -/

/-! ## Clause 2, part 1: helpers (interval convexity, interior cells, first exit, measurability) -/

/-- Interval lemma for the interpolated walk: if the vertices `x k`, `n ≤ k ≤ K`, lie in a convex set `C`,
then `interpolatedWalk` at every time `u` with `n ≤ mε u ≤ K` lies in `C`. -/
lemma interpolatedWalk_mem_convex_fp36 {ε mε : ℝ} {η : ℝ → ℂ} {x : ℕ → ℤ} {C : Set ℂ}
    (hC : Convex ℝ C) (hm : 0 < mε) {n K : ℕ}
    (hv : ∀ k, n ≤ k → k ≤ K → vertexPoint ε η (x k) ∈ C)
    {u : ℝ≥0} (hu0 : (n : ℝ) ≤ mε * (u : ℝ)) (hu1 : mε * (u : ℝ) ≤ K) :
    interpolatedWalk ε η mε x u ∈ C := by
  have hs0 : 0 ≤ mε * (u : ℝ) := mul_nonneg hm.le u.2
  have hfl1 : ((⌊mε * (u : ℝ)⌋₊ : ℕ) : ℝ) ≤ mε * (u : ℝ) := Nat.floor_le hs0
  have hfl2 : mε * (u : ℝ) < ((⌊mε * (u : ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : n ≤ ⌊mε * (u : ℝ)⌋₊ := Nat.le_floor hu0
  have hhi : ⌊mε * (u : ℝ)⌋₊ ≤ K := by
    have : ((⌊mε * (u : ℝ)⌋₊ : ℕ) : ℝ) ≤ K := hfl1.trans hu1
    exact_mod_cast this
  unfold interpolatedWalk
  dsimp only
  rcases Nat.lt_or_ge ⌊mε * (u : ℝ)⌋₊ K with hlt | hge
  · have ha := hv _ hlo hlt.le
    have hb := hv (⌊mε * (u : ℝ)⌋₊ + 1) (by omega) hlt
    have h0 : 0 ≤ mε * (u : ℝ) - ⌊mε * (u : ℝ)⌋₊ := by linarith
    have h1 : 0 ≤ 1 - (mε * (u : ℝ) - ⌊mε * (u : ℝ)⌋₊) := by linarith
    have := hC ha hb h1 h0 (by ring)
    simpa [Complex.real_smul] using this
  · have hK : ⌊mε * (u : ℝ)⌋₊ = K := le_antisymm hhi hge
    have hK' : (K : ℝ) ≤ mε * (u : ℝ) := by
      have : ((⌊mε * (u : ℝ)⌋₊ : ℕ) : ℝ) ≤ mε * (u : ℝ) := hfl1
      rw [hK] at this
      exact this
    have hθ : mε * (u : ℝ) - (K : ℝ) = 0 := by linarith
    have hval : vertexPoint ε η (x K) ∈ C := hv K (by omega) le_rfl
    rw [hK, hθ]
    simpa using hval

/-- A cell of an interior vertex of an open set lies in that set (connectedness of the cell). -/
lemma cell_subset_of_interior_fp36 {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {U : Set ℂ} (hU : IsOpen U)
    {k : ℤ} (hk : k ∈ interiorCellVertices ε η U) : cell ε η k ⊆ U := by
  have hk' : k ∈ cellVertices ε η U ∧ k ∉ cellVertices ε η (frontier U) := hk
  have hconn : IsPreconnected (cell ε η k) := by
    unfold cell
    exact isPreconnected_Icc.image _ hη.continuousOn
  have hne : (cell ε η k ∩ U).Nonempty := hk'.1
  have hv : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  refine hconn.subset_left_of_subset_union (v := (closure U)ᶜ) hU hv ?_ ?_ hne
  · exact Set.disjoint_left.2 fun c hc hc' => hc' (subset_closure hc)
  · intro c hc
    by_cases hcb : c ∈ U
    · exact Or.inl hcb
    · refine Or.inr ?_
      intro hcl
      apply hk'.2
      refine (⟨c, hc, ?_⟩ : (cell ε η k ∩ frontier U).Nonempty)
      exact ⟨hcl, by rw [hU.interior_eq]; exact hcb⟩

/-- The first exit time of a sequence from `A`, when `y K ∉ A` and `y k ∈ A` for all `k < K`. -/
lemma vExitTime_eq_of_first_fp36 {A : Set ℤ} {y : ℕ → ℤ} {K : ℕ} (hK : y K ∉ A)
    (hlt : ∀ k < K, y k ∈ A) :
    vExitTime A y = (K : ℕ∞) ∧ vExitPosition A y = y K := by
  classical
  have hex : ∃ n, y n ∉ A := ⟨K, hK⟩
  have hv : vExitTime A y = (K : ℕ∞) := by
    unfold vExitTime
    split_ifs
    exact congrArg (Nat.cast : ℕ → ℕ∞) ((Nat.find_eq_iff hex).2 ⟨hK, fun n hn hc => hc (hlt n hn)⟩)
  refine ⟨hv, ?_⟩
  unfold vExitPosition
  rw [hv]
  simp

/-- The event that the walk uses edges of the multiplicity `M` is measurable. -/
lemma measurableSet_usesEdges_fp36 (M : ℤ → ℤ → ℕ) (a : ℤ) :
    MeasurableSet {x : ℕ → ℤ | UsesEdges M a x} := by
  have h0 : MeasurableSet ((fun x : ℕ → ℤ => x 0) ⁻¹' {a}) :=
    (measurable_pi_apply 0) (measurableSet_singleton a)
  have hn : ∀ n : ℕ, MeasurableSet {x : ℕ → ℤ | M (x n) (x (n + 1)) ≠ 0} := by
    intro n
    have hg : Measurable (fun p : ℤ × ℤ => M p.1 p.2) := Measurable.of_discrete
    have hpair : Measurable (fun x : ℕ → ℤ => (x n, x (n + 1))) :=
      (measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1))
    have hf : Measurable (fun x : ℕ → ℤ => M (x n) (x (n + 1))) := hg.comp hpair
    exact hf (measurableSet_singleton 0).compl
  have hset : {x : ℕ → ℤ | UsesEdges M a x} =
      {x : ℕ → ℤ | x 0 = a} ∩ ⋂ n : ℕ, {x : ℕ → ℤ | M (x n) (x (n + 1)) ≠ 0} := by
    ext x
    simp [UsesEdges]
  rw [hset]
  exact h0.inter (MeasurableSet.iInter hn)

/-- Grid times: `mε` times the grid time `k / mε` is `k`. -/
lemma mul_grid_fp36 {mε : ℝ} (hm : 0 < mε) (k : ℕ) :
    mε * ((((k : ℝ) / mε).toNNReal : ℝ≥0) : ℝ) = (k : ℝ) := by
  have hne : mε ≠ 0 := hm.ne'
  rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg k) hm.le)]
  field_simp

/-- At the grid time `k / mε` the interpolated walk is the vertex point of `x k`. -/
lemma interpolatedWalk_grid_fp36 {ε mε : ℝ} {η : ℝ → ℂ} (x : ℕ → ℤ) (hm : 0 < mε) (k : ℕ) :
    interpolatedWalk ε η mε x (((k : ℝ) / mε).toNNReal) = vertexPoint ε η (x k) := by
  have hcoe := mul_grid_fp36 hm k
  unfold interpolatedWalk
  dsimp only
  rw [hcoe]
  simp

/-- **Plan steps 5-9, deterministic core.** Let `x` be a vertex path whose first exit from the interior cells of
`B_r(z)` is at index `N` (a boundary vertex `x N`, reached along an edge from `x (N-1)`), and whose interpolated walk
leaves `B_r(z)` at a point `Z` with `dist Z P > s/2`, where `P` is within `δ` of `x N` and within `3δ` of `x (N-1)`
(Lemma 4). Then the post-`N` discrete walk leaves the interior cells of the lens `B_{r+4δ}(z) ∩ B_{s/4}(P)` in finite
time, at a vertex whose cell meets the far circle `∂B_{s/4}(P)` (Lens exit, Armitage-Gardiner style argument). -/
lemma farExit_pathwise_fp36 {ε mε δ s r : ℝ} {η : ℝ → ℂ} {M : ℤ → ℤ → ℕ} {x : ℕ → ℤ} {z P : ℂ} {N : ℕ}
    (hε : 0 < ε) (hη : Continuous η) (hm : 0 < mε) (hr : 0 < r) (hδ : 0 < δ)
    (hscale : 64 * δ ≤ s) (hN0 : 0 < N)
    (hN1 : ∀ k < N, x k ∈ interiorCellVertices ε η (ball z r))
    (hN2 : x N ∉ interiorCellVertices ε η (ball z r))
    (hedge : ∀ n, M (x n) (x (n + 1)) ≠ 0)
    (hadj : ∀ j k, M j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hdiam : ∀ k, (cell ε η k ∩ ball z (r + 4 * δ)).Nonempty → diam (cell ε η k) ≤ δ)
    (hq : dist (vertexPoint ε η (x N)) P ≤ δ)
    (hent : dist (vertexPoint ε η (x (N - 1))) P ≤ 3 * δ)
    (hvU : x N ∈ interiorCellVertices ε η (fp36LensDomain z r δ P s))
    (hT : HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε η mε x) < ⊤)
    (hfar : s / 2 < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x)) P) :
    vExitTime (interiorCellVertices ε η (fp36LensDomain z r δ P s)) (shiftedPath N x) < ⊤ ∧
      vExitPosition (interiorCellVertices ε η (fp36LensDomain z r δ P s)) (shiftedPath N x) ∈
        fp36LensFarCells ε η P s := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hent' : dist (vertexPoint ε η (x n)) P ≤ 3 * δ := by simpa using hent
  have hs : 0 < s := by linarith
  have h3 : 3 * δ ≤ s / 2 := by linarith
  have hUo : IsOpen (fp36LensDomain z r δ P s) := isOpen_ball.inter isOpen_ball
  have hUconv : Convex ℝ (fp36LensDomain z r δ P s) := (convex_ball _ _).inter (convex_ball _ _)
  have hXc : Continuous (interpolatedWalk ε η mε x) := continuous_interpolatedWalk ε mε η x
  have hcellbdd : ∀ k : ℤ, Bornology.IsBounded (cell ε η k) :=
    fun k => (isCompact_Icc.image hη).isBounded
  have hcellpc : ∀ k : ℤ, IsPreconnected (cell ε η k) := fun k => by
    unfold cell
    exact isPreconnected_Icc.image _ hη.continuousOn
  have hvc : ∀ k : ℤ, vertexPoint ε η k ∈ cell ε η k := fun k => vertexPoint_mem_cell_fp36 hε.le η k
  have hmul : ∀ u v : ℝ≥0, mε * (u : ℝ) < mε * (v : ℝ) → u < v := by
    intro u v h
    by_contra hc
    push Not at hc
    have := mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hc) hm.le
    linarith
  have h0 : interpolatedWalk ε η mε x 0 ∈ ball z r := by
    rw [interpolatedWalk_zero_fp36]
    exact vertexPoint_mem_ball_of_interior_fp36 hε.le hη (hN1 0 hN0)
  -- Step A: before the entrance index the walk is in the disc.
  have hstepA : ∀ u : ℝ≥0, mε * (u : ℝ) ≤ (n : ℝ) → interpolatedWalk ε η mε x u ∈ ball z r := by
    intro u hu
    refine interpolatedWalk_mem_convex_fp36 (convex_ball _ _) hm (n := 0) (K := n) ?_ ?_ hu
    · intro k _ hk
      exact vertexPoint_mem_ball_of_interior_fp36 hε.le hη (hN1 k (by omega))
    · refine Nat.cast_zero.trans_le ?_
      exact mul_nonneg hm.le u.2
  -- Step B: the exit time of the disc and the exit point.
  obtain ⟨T0, hT0⟩ : ∃ T0 : ℝ≥0, (T0 : ℝ≥0∞) = HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε η mε x) :=
    ⟨_, ENNReal.coe_toNNReal hT.ne⟩
  have hpos : pathExitPosition (ball z r) (interpolatedWalk ε η mε x) =
      interpolatedWalk ε η mε x T0 := by
    unfold pathExitPosition
    congr 1
    rw [← hT0]
    rfl
  rw [hpos] at hfar
  have hB1 : ∀ u : ℝ≥0, u < T0 → interpolatedWalk ε η mε x u ∈ ball z r := by
    intro u hu
    by_contra hc
    have hle : HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε η mε x) ≤ (u : ℝ≥0∞) := by
      unfold HarmonicBalls.pathExitTime
      exact sInf_le ⟨u, rfl, hc⟩
    rw [← hT0] at hle
    exact absurd (ENNReal.coe_le_coe.1 hle) (not_le.2 hu)
  have hZfr : interpolatedWalk ε η mε x T0 ∈ frontier (ball z r) := by
    have := pathExitPosition_mem_frontier_of_continuous isOpen_ball hXc h0 hT
    rwa [hpos] at this
  have hZnb : interpolatedWalk ε η mε x T0 ∉ ball z r := by
    have h := hZfr
    rw [frontier, isOpen_ball.interior_eq] at h
    exact h.2
  have hZcb : interpolatedWalk ε η mε x T0 ∈ closedBall z r := by
    have h := hZfr
    rw [frontier] at h
    exact closure_ball_subset_closedBall h.1
  -- the exit time of the disc is after the entrance grid time `n + 1`
  have hTn : ((n + 1 : ℕ) : ℝ) < mε * (T0 : ℝ) := by
    by_contra hc
    push Not at hc
    rcases le_total (mε * (T0 : ℝ)) (n : ℝ) with hle | hle
    · exact hZnb (hstepA T0 hle)
    · have hmem : interpolatedWalk ε η mε x T0 ∈ closedBall P (3 * δ) := by
        refine interpolatedWalk_mem_convex_fp36 (convex_closedBall _ _) hm (n := n) (K := n + 1) ?_ hle hc
        intro k hk1 hk2
        rcases (show k = n ∨ k = n + 1 by omega) with rfl | rfl
        · exact mem_closedBall.2 hent'
        · exact mem_closedBall.2 (le_trans hq (by linarith))
      have := mem_closedBall.1 hmem
      linarith
  have hXT0U : interpolatedWalk ε η mε x T0 ∉ fp36LensDomain z r δ P s := by
    intro h
    have h2 : interpolatedWalk ε η mε x T0 ∈ ball P (s / 4) := h.2
    rw [mem_ball] at h2
    linarith
  -- Step C: the first exit time `τ ≤ T0` of the walk from the lens after the entrance.
  obtain ⟨τ, ⟨hτN, hτU⟩, hτmin⟩ : ∃ τ : ℝ≥0,
      (((n + 1 : ℕ) : ℝ) ≤ mε * (τ : ℝ) ∧ interpolatedWalk ε η mε x τ ∉ fp36LensDomain z r δ P s) ∧
      ∀ u : ℝ≥0, ((n + 1 : ℕ) : ℝ) ≤ mε * (u : ℝ) →
        interpolatedWalk ε η mε x u ∉ fp36LensDomain z r δ P s → τ ≤ u := by
    have hGc : IsClosed {u : ℝ≥0 | ((n + 1 : ℕ) : ℝ) ≤ mε * (u : ℝ) ∧
        interpolatedWalk ε η mε x u ∉ fp36LensDomain z r δ P s} :=
      (isClosed_le continuous_const (continuous_const.mul NNReal.continuous_coe)).inter
        (hUo.isClosed_compl.preimage hXc)
    have hGne : ({u : ℝ≥0 | ((n + 1 : ℕ) : ℝ) ≤ mε * (u : ℝ) ∧
        interpolatedWalk ε η mε x u ∉ fp36LensDomain z r δ P s}).Nonempty :=
      ⟨T0, hTn.le, hXT0U⟩
    have hGbdd : BddBelow {u : ℝ≥0 | ((n + 1 : ℕ) : ℝ) ≤ mε * (u : ℝ) ∧
        interpolatedWalk ε η mε x u ∉ fp36LensDomain z r δ P s} := OrderBot.bddBelow _
    exact ⟨sInf _, hGc.csInf_mem hGne hGbdd, fun u hu1 hu2 => csInf_le hGbdd ⟨hu1, hu2⟩⟩
  have hτT0 : τ ≤ T0 := hτmin T0 hTn.le hXT0U
  have hC1 : ∀ u : ℝ≥0, ((n + 1 : ℕ) : ℝ) ≤ mε * (u : ℝ) → mε * (u : ℝ) < mε * (τ : ℝ) →
      interpolatedWalk ε η mε x u ∈ fp36LensDomain z r δ P s := by
    intro u hu1 hu2
    by_contra hc
    have hle := hτmin u hu1 hc
    have := mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hle) hm.le
    linarith
  have hτgt : ((n + 1 : ℕ) : ℝ) < mε * (τ : ℝ) := by
    refine lt_of_le_of_ne hτN (fun heq => hτU ?_)
    refine interpolatedWalk_mem_convex_fp36 hUconv hm (n := n + 1) (K := n + 1) ?_ heq.le heq.symm.le
    intro k hk1 hk2
    obtain rfl : k = n + 1 := by omega
    exact cell_subset_of_interior_fp36 hη hUo hvU (hvc _)
  have hceil : n + 1 < ⌈mε * (τ : ℝ)⌉₊ := Nat.lt_ceil.2 hτgt
  obtain ⟨j', hj'⟩ : ∃ j', ⌈mε * (τ : ℝ)⌉₊ = j' + 1 := ⟨⌈mε * (τ : ℝ)⌉₊ - 1, by omega⟩
  have hj1 : (j' : ℝ) < mε * (τ : ℝ) := Nat.lt_ceil.1 (by omega)
  have hj2 : mε * (τ : ℝ) ≤ ((j' + 1 : ℕ) : ℝ) := by
    rw [← hj']
    exact Nat.le_ceil _
  have hjn : n + 1 ≤ j' := by omega
  -- Step D: the first discrete exit of the lens' interior cells after the entrance.
  have hex : ∃ k : ℕ, x (n + 1 + k) ∉ interiorCellVertices ε η (fp36LensDomain z r δ P s) := by
    by_contra hall
    push Not at hall
    have hv : ∀ k, n + 1 ≤ k → k ≤ ⌈mε * (T0 : ℝ)⌉₊ →
        vertexPoint ε η (x k) ∈ fp36LensDomain z r δ P s := by
      intro k h1 _
      have := hall (k - (n + 1))
      rw [show n + 1 + (k - (n + 1)) = k by omega] at this
      exact cell_subset_of_interior_fp36 hη hUo this (hvc (x k))
    exact hXT0U (interpolatedWalk_mem_convex_fp36 hUconv hm (n := n + 1) (K := ⌈mε * (T0 : ℝ)⌉₊)
      hv hTn.le (Nat.le_ceil _))
  have hKmem := Nat.find_spec hex
  have hKmin : ∀ k < Nat.find hex,
      x (n + 1 + k) ∈ interiorCellVertices ε η (fp36LensDomain z r δ P s) :=
    fun k hk => not_not.1 (Nat.find_min hex hk)
  generalize Nat.find hex = K at hKmem hKmin
  have hfirst := vExitTime_eq_of_first_fp36 (y := shiftedPath (n + 1) x) (K := K) hKmem
    (fun k hk => hKmin k hk)
  refine ⟨?_, ?_⟩
  · rw [hfirst.1]
    exact ENat.natCast_lt_top K
  rw [hfirst.2]
  show x (n + 1 + K) ∈ fp36LensFarCells ε η P s
  -- Step E: the crossing of the far circle.
  rcases lt_or_ge (n + 1 + K) (j' + 1) with hJlt | hJge
  · -- Case J ≤ j': the discrete exit cell meets the lens and not its frontier, so it meets ∂B_{s/4}(P).
    have hwJU : vertexPoint ε η (x (n + 1 + K)) ∈ fp36LensDomain z r δ P s := by
      rw [← interpolatedWalk_grid_fp36 x hm (n + 1 + K)]
      refine hC1 _ ?_ ?_
      · rw [mul_grid_fp36 hm]
        exact Nat.cast_le.2 (by omega)
      · rw [mul_grid_fp36 hm]
        exact lt_of_le_of_lt (Nat.cast_le.2 (by omega)) hj1
    have hwJB : vertexPoint ε η (x (n + 1 + K)) ∈ ball z r := by
      rw [← interpolatedWalk_grid_fp36 x hm (n + 1 + K)]
      apply hB1
      apply hmul
      rw [mul_grid_fp36 hm]
      exact lt_of_lt_of_le (lt_of_le_of_lt (Nat.cast_le.2 (by omega)) hj1)
        (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hτT0) hm.le)
    have hmeet : (cell ε η (x (n + 1 + K)) ∩ fp36LensDomain z r δ P s).Nonempty :=
      ⟨_, hvc _, hwJU⟩
    have hfr : (cell ε η (x (n + 1 + K)) ∩ frontier (fp36LensDomain z r δ P s)).Nonempty := by
      by_contra hc
      exact hKmem ⟨hmeet, hc⟩
    obtain ⟨p, hpc, hpf⟩ := hfr
    have hfrU : frontier (fp36LensDomain z r δ P s) ⊆ sphere z (r + 4 * δ) ∪ sphere P (s / 4) := by
      intro p hp
      have hp' := frontier_inter_subset (ball z (r + 4 * δ)) (ball P (s / 4)) hp
      rw [frontier_ball z (by linarith : (0 : ℝ) < r + 4 * δ).ne',
        frontier_ball P (by linarith : (0 : ℝ) < s / 4).ne'] at hp'
      rcases hp' with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
    rcases hfrU hpf with hpz | hpP
    · exfalso
      have hbd := dist_le_diam_of_mem (hcellbdd _) hpc (hvc (x (n + 1 + K)))
      have hdl := hdiam (x (n + 1 + K))
        ⟨vertexPoint ε η (x (n + 1 + K)), hvc _, ball_subset_ball (by linarith) hwJB⟩
      have hd2 := mem_ball.1 hwJB
      rw [mem_sphere] at hpz
      have := dist_triangle p (vertexPoint ε η (x (n + 1 + K))) z
      linarith
    · show (cell ε η (x (n + 1 + K)) ∩ sphere P (s / 4)).Nonempty
      exact ⟨p, hpc, hpP⟩
  · -- Case j' + 1 ≤ J: the crossing index is j'+1 and the cell of x (j'+1) meets the far circle.
    have hE2a : s / 4 ≤ dist (vertexPoint ε η (x (j' + 1))) P := by
      by_contra hc
      push Not at hc
      have hwj' : vertexPoint ε η (x j') ∈ ball P (s / 4) := by
        rw [← interpolatedWalk_grid_fp36 x hm j']
        have hU' := hC1 (((j' : ℝ) / mε).toNNReal) (by rw [mul_grid_fp36 hm]; exact Nat.cast_le.2 hjn)
          (by rw [mul_grid_fp36 hm]; exact hj1)
        exact hU'.2
      have hmem : interpolatedWalk ε η mε x τ ∈ ball P (s / 4) := by
        refine interpolatedWalk_mem_convex_fp36 (convex_ball _ _) hm (n := j') (K := j' + 1) ?_ hj1.le hj2
        intro k hk1 hk2
        rcases (show k = j' ∨ k = j' + 1 by omega) with rfl | rfl
        · exact mem_ball.2 (mem_ball.1 hwj')
        · exact mem_ball.2 hc
      have hbig : interpolatedWalk ε η mε x τ ∈ ball z (r + 4 * δ) := by
        rcases lt_or_eq_of_le hτT0 with hlt | heq
        · exact ball_subset_ball (by linarith) (hB1 τ hlt)
        · rw [heq]
          exact closedBall_subset_ball (by linarith) hZcb
      exact hτU ⟨hbig, hmem⟩
    have hJeq : n + 1 + K = j' + 1 := by
      by_contra hne
      have hmem := hKmin (j' + 1 - (n + 1)) (by omega)
      rw [show n + 1 + (j' + 1 - (n + 1)) = j' + 1 by omega] at hmem
      have hw : vertexPoint ε η (x (j' + 1)) ∈ fp36LensDomain z r δ P s :=
        cell_subset_of_interior_fp36 hη hUo hmem (hvc _)
      have := mem_ball.1 hw.2
      linarith
    rw [hJeq]
    obtain ⟨c', hc'1, hc'2⟩ := hadj (x j') (x (j' + 1)) (hedge j')
    have hxj' : x j' ∈ interiorCellVertices ε η (fp36LensDomain z r δ P s) := by
      have := hKmin (j' - (n + 1)) (by omega)
      rwa [show n + 1 + (j' - (n + 1)) = j' by omega] at this
    have hc'P : dist c' P < s / 4 :=
      mem_ball.1 ((cell_subset_of_interior_fp36 hη hUo hxj' hc'1).2)
    have hcont : ContinuousOn (fun c : ℂ => dist c P) (cell ε η (x (j' + 1))) :=
      (continuous_id.dist continuous_const).continuousOn
    obtain ⟨p, hpc, hpd⟩ := (hcellpc (x (j' + 1))).intermediate_value hc'2 (hvc _) hcont
      ⟨hc'P.le, hE2a⟩
    show (cell ε η (x (j' + 1)) ∩ sphere P (s / 4)).Nonempty
    exact ⟨p, hpc, mem_sphere.2 hpd⟩

/-- Every index before the first exit time of `A` lies in `A`. -/
lemma mem_of_lt_vExitTime_fp36 {A : Set ℤ} {x : ℕ → ℤ} {N : ℕ} (h : vExitTime A x = (N : ℕ∞))
    {k : ℕ} (hk : k < N) : x k ∈ A := by
  classical
  by_contra hc
  have hex : ∃ n, x n ∉ A := ⟨k, hc⟩
  have hle : Nat.find hex ≤ k := Nat.find_min' hex hc
  have key : vExitTime A x = ((Nat.find hex : ℕ) : ℕ∞) := by
    unfold vExitTime
    split_ifs
    rfl
  rw [key] at h
  have h2 : Nat.find hex = N := by exact_mod_cast h
  omega

end FirstPass36
end MatedCRT
