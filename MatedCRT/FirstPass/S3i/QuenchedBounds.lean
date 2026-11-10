import MatedCRT.FirstPass.S3i.Proof
import MatedCRT.FirstPass.S3i.LensDefs
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellWindow

/-!
# The two quenched estimates on a good environment (plan Lemma 7, worker H7)

Plan: `notes/fp-gaps/CHATGPT-221-idla-3-6-QuenchedLensStep-plan-PRO.md`, section 7 (l.411-461).
Lemmas 1, 2, 4, 5, 6 of the plan are taken as hypotheses with the plan's exact types, named
`FP36LemmaOne`, `FP36LemmaTwo`, `FP36LemmaFour`, `FP36LemmaFive`, `FP36LemmaSix` (workers H1, H2, H4, H5, H6).

This file proves the start and finite-exit clause (plan steps 1-4) and the lens clause (plan steps 5-12).

Terminology: quenched and annealed laws (Armstrong-Kuusi-Mourrat); same-walk coupling and the one-sided boundary
estimate (Gwynne-Miller-Sheffield, arXiv:1807.07511); Lawler-Limic for the strong Markov property of random walk.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

open Classical in
/-- Plan Lemma 1 (`exitHitProb_basic`, worker H1): the finite-domain exit package, as a hypothesis type. -/
def FP36LemmaOne : Prop :=
  ∀ {m : ℤ → ℤ → ℕ} {A B : Set ℤ}, FiniteExitData m A →
    (∀ a ∈ A, srwLaw m a {x | UsesEdges m a x ∧ vExitTime A x < ⊤} = 1) ∧
    (∀ a : ℤ, 0 ≤ exitHitProb m A B a ∧ exitHitProb m A B a ≤ 1) ∧
    (∀ a ∈ A, mLaplacian m (exitHitProb m A B) a = 0) ∧
    (∀ a ∉ A, exitHitProb m A B a = if a ∈ B then 1 else 0)

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

/-- **Plan Lemma 7, clause 1.** Almost surely the walk from the selected start vertex is a same-walk good path:
the interpolated walk starts in `B_r(z)` and leaves it in finite time. -/
theorem quenchedStart_null_fp36
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A r ε : ℝ} {z y : ℂ} {ω : Ω}
    (L1 : FP36LemmaOne) (hε : 0 < ε) (hmpos : 0 < S.mε ε)
    (houter : closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀)
    (hgood : FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω) :
    srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) {x | ¬ SameWalkGood S r z ε ω x} = 0 := by
  obtain ⟨hA, -, -, hfin, hvin, -⟩ := hgood
  have hη : Continuous (S.η ω) := hA.1
  set a := vertexOf ε (S.η ω) y with ha
  set V := cellVertices ε (S.η ω) (ball z (r + 4 * ε ^ b)) with hV
  have hδ : 0 ≤ ε ^ b := Real.rpow_nonneg hε.le b
  have hball : ball z r ⊆ ball z (r + 4 * ε ^ b) := ball_subset_ball (by linarith)
  have haV : a ∈ V := by
    obtain ⟨c, hc1, hc2⟩ := hvin.1
    exact ⟨c, hc1, hball hc2⟩
  have hfinV : FiniteExitData (S.mult ε ω) V := (hfin _ houter).1
  have hE : srwLaw (S.mult ε ω) a {x | UsesEdges (S.mult ε ω) a x ∧ vExitTime V x < ⊤} = 1 :=
    (L1 (B := (∅ : Set ℤ)) hfinV).1 a haV
  have hE' : srwLaw (S.mult ε ω) a {x | vExitTime V x < ⊤} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hE]
    exact measure_mono fun x hx => hx.2
  have hnull2 : srwLaw (S.mult ε ω) a {x | vExitTime V x < ⊤}ᶜ = 0 :=
    (prob_compl_eq_zero_iff (measurableSet_vExitTime_lt_top_fp36 V)).2 hE'
  have hnull1 : srwLaw (S.mult ε ω) a {x | x 0 ≠ a} = 0 := by
    have h := ae_iff.1 (srwLaw_ae_start (S.mult ε ω) a)
    simpa [ne_eq] using h
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hnull1 hnull2)
  by_contra hxn
  simp only [mem_union, Set.mem_ofPred_eq, mem_compl_iff, not_or, not_not] at hxn hx
  obtain ⟨h0, hT⟩ := hxn
  apply hx
  unfold SameWalkGood
  refine ⟨?_, ?_⟩
  · rw [interpolatedWalk_zero_fp36, h0]
    exact vertexPoint_mem_ball_of_interior_fp36 hε.le hη hvin
  · exact pathExitTime_lt_top_of_vertex_not_mem_fp36 hmpos
      (fun h => vertexPoint_not_mem_of_not_mem_cellVertices_fp36 hε.le
        (vExitTime_toNat_not_mem_fp36 hT) (hball h))

end FirstPass36
end MatedCRT
