import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.BallHolderFamily

/-!
# Lemma 3.4 (E-c2-9): finite covers by null-measurable events, and density in a ball

The environment-dependent events `{ω | ∀ q ∈ Q, |f ω q - G j q| < δ}` are measurable for the environment
σ-algebra `σ(h, η)`, hence null-measurable for the probability measure (`nullMeasurableSet_of_envSigma`), but not
necessarily measurable for the ambient σ-algebra. The finite-cover argument is therefore run with null-measurable
events: continuity from above (`tendsto_measure_iInter_atTop`) replaces the ambient version. The density lemmas
reduce a uniform bound on the ball to a countable dense set of points of the ball.

Terminology: continuity from above of a finite measure; countable dense sets (Armstrong–Kuusi–Mourrat, Section 2).
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- If every point lies in one of countably many null-measurable events, finitely many of them cover all but a set of
probability less than any `κ > 0`. -/
theorem exists_finite_cover_nullMeasurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A : ℕ → Set Ω) (hA : ∀ j, NullMeasurableSet (A j) P) (hcov : ∀ ω, ∃ j, ω ∈ A j) {κ : ℝ≥0∞}
    (hκ : 0 < κ) : ∃ J : ℕ, P ((⋃ j ∈ Finset.range J, A j)ᶜ) < κ := by
  set B : ℕ → Set Ω := fun J => (⋃ j ∈ Finset.range J, A j)ᶜ with hB
  have hBm : ∀ J, NullMeasurableSet (B J) P := fun J =>
    (NullMeasurableSet.iUnion fun j => NullMeasurableSet.iUnion fun _ => hA j).compl
  have hBanti : Antitone B := by
    intro J K hJK
    apply compl_subset_compl.2
    intro ω hω
    obtain ⟨j, hj, hjω⟩ := Set.mem_iUnion₂.1 hω
    exact Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) hJK), hjω⟩
  have hint : ⋂ J, B J = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω hω
    obtain ⟨j, hj⟩ := hcov ω
    have h1 : ω ∈ B (j + 1) := Set.mem_iInter.1 hω (j + 1)
    exact h1 (Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_self j), hj⟩)
  have hlim : Tendsto (fun J => P (B J)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) hBm hBanti ⟨0, measure_ne_top P _⟩
    rw [hint, measure_empty] at h
    exact h
  obtain ⟨J, hJ⟩ := (hlim.eventually (gt_mem_nhds hκ)).exists
  exact ⟨J, hJ⟩

/-- A dense set meets every neighbourhood of a point of the open ball inside the ball. -/
lemma exists_mem_dense_inter_ball {z : ℂ} {r : ℝ} {D : Set ℂ} (hD : Dense D) {x : ℂ} (hx : x ∈ ball z r)
    {ε : ℝ} (hε : 0 < ε) : ∃ q ∈ D ∩ ball z r, dist q x < ε := by
  rw [mem_ball] at hx
  have hpos : 0 < min ε (r - dist x z) := lt_min hε (by linarith)
  obtain ⟨q, hqD, hq⟩ := hD.exists_dist_lt x hpos
  have h1 : dist x q < r - dist x z := lt_of_lt_of_le hq (min_le_right _ _)
  refine ⟨q, ⟨hqD, ?_⟩, by rw [dist_comm]; exact lt_of_lt_of_le hq (min_le_left _ _)⟩
  rw [mem_ball]
  linarith [dist_triangle q x z, dist_comm q x]

/-- A uniform bound on the open ball follows from a strict bound on a dense subset of the ball, by continuity. -/
lemma abs_sub_le_of_lt_on_dense_inter_ball {z : ℂ} {r : ℝ} {D : Set ℂ} (hD : Dense D) {F G : ℂ → ℝ}
    (hF : ContinuousOn F (ball z r)) (hG : ContinuousOn G (ball z r)) {δ : ℝ}
    (h : ∀ q ∈ D ∩ ball z r, |F q - G q| < δ) : ∀ x ∈ ball z r, |F x - G x| ≤ δ := by
  intro x hx
  by_contra hlt
  rw [not_le] at hlt
  have hc : ContinuousWithinAt (fun y => |F y - G y|) (ball z r) x :=
    continuous_abs.continuousWithinAt.comp (hF.sub hG x hx) (mapsTo_univ _ _)
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuousWithinAt_iff.1 hc (|F x - G x| - δ) (by linarith)
  obtain ⟨q, hq, hdist⟩ := exists_mem_dense_inter_ball hD hx hρ
  have h2 := hball hq.2 hdist
  rw [Real.dist_eq] at h2
  have h3 := (abs_sub_lt_iff.1 h2).2
  linarith [h q hq]

end MatedCRT
