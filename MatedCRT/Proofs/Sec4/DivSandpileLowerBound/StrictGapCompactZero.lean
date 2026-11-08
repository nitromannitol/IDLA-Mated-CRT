import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapRepresentative
import Mathlib.Topology.Order.Compact
import HarmonicBalls.Proofs.Sec5.ClusterMeasurability

/-! Countable tests for zeros of continuous nonnegative odometers. -/

namespace MatedCRT

open Set MeasureTheory Metric TopologicalSpace _root_.HarmonicBalls

/-- For a pointwise measurable family, a countable test detects zeros inside
an open ball and can only detect zeros in its compact closure, provided the
function is continuous and nonnegative there. -/
theorem exists_measurable_compactZero_test
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℂ → ℝ)
    (hfmeas : ∀ x : ℂ, Measurable (fun ω => f ω x))
    (a : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ E : Set Ω, MeasurableSet E ∧ ∀ ω,
      ContinuousOn (f ω) (closedBall a r) →
      (∀ x ∈ closedBall a r, 0 ≤ f ω x) →
      ((∃ x ∈ ball a r, f ω x = 0) → ω ∈ E) ∧
      (ω ∈ E → ∃ x ∈ closedBall a r, f ω x = 0) := by
  let E : Set Ω := {ω | ∀ k : ℕ, ∃ n : ℕ,
    denseSeq ℂ n ∈ ball a r ∧ f ω (denseSeq ℂ n) < 1 / ((k : ℝ) + 1)}
  have hE : MeasurableSet E := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.forall
    intro k
    apply Measurable.exists
    intro n
    exact measurable_const.and ((hfmeas (denseSeq ℂ n)).lt measurable_const)
  refine ⟨E, hE, ?_⟩
  intro ω hcont hnonneg
  constructor
  · rintro ⟨x, hx, hzero⟩ k
    let U := ball a r ∩ (f ω) ⁻¹' Set.Iio (1 / ((k : ℝ) + 1))
    have hU : IsOpen U := (hcont.mono ball_subset_closedBall).isOpen_inter_preimage
      isOpen_ball isOpen_Iio
    have hxU : x ∈ U := by
      exact ⟨hx, by simp only [mem_preimage, mem_Iio, hzero]; positivity⟩
    obtain ⟨n, hn⟩ := (denseRange_denseSeq ℂ).exists_mem_open hU ⟨x, hxU⟩
    exact ⟨n, hn.1, hn.2⟩
  · intro htest
    have hne : (closedBall a r).Nonempty := ⟨a, mem_closedBall_self hr.le⟩
    obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall a r).exists_isMinOn hne hcont
    have hle : f ω x ≤ 0 := by
      by_contra hn
      have hp : 0 < f ω x := lt_of_not_ge hn
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hp
      obtain ⟨n, hnball, hnval⟩ := htest k
      have hm := hmin (ball_subset_closedBall hnball)
      exact (not_lt_of_ge hm) (lt_trans hnval hk)
    exact ⟨x, hx, le_antisymm hle (hnonneg x hx)⟩

/-- A countable family of compact zero tests gives a measurable detector for
points in the regularization of an open set where its odometer vanishes. -/
theorem exists_measurable_regularization_zero_test
    {Ω : Type*} [MeasurableSpace Ω] (C : Ω → Set ℂ) (hC : Measurable C)
    (f : Ω → ℂ → ℝ) (hf : ∀ x : ℂ, Measurable (fun ω => f ω x))
    {ι : Type*} [Countable ι] (D : Set ℂ) (hD : IsOpen D) (a : ι → ℂ) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hcover : ∀ (U : Set ℂ), IsOpen U → ∀ x ∈ U,
      ∃ i, x ∈ ball (a i) (r i) ∧ ball (a i) (2 * r i) ⊆ U) :
    ∃ E : Set Ω, MeasurableSet E ∧ ∀ ω,
      IsOpen (C ω) →
      (∀ i, closedBall (a i) (r i) ⊆ D →
        ContinuousOn (f ω) (closedBall (a i) (r i)) ∧
        ∀ x ∈ closedBall (a i) (r i), 0 ≤ f ω x) →
      (∀ x ∈ D, x ∉ C ω ↔ f ω x = 0) →
      (ω ∈ E ↔ ∃ x ∈ D, x ∈ interior (closure (C ω)) ∧ x ∉ C ω) := by
  classical
  choose Z hZ hZgood using fun i => exists_measurable_compactZero_test f hf (a i) (hr i)
  let F : Ω → Set ℂ := fun ω => denseSequenceClosure (C ω)
  have hF : Measurable F := measurable_denseSequenceClosure.comp hC
  let E : Set Ω := {ω | ∃ i : ι,
    ball (a i) (2 * r i) ⊆ D ∧
    (∀ n : ℕ, denseSeq ℂ n ∈ ball (a i) (2 * r i) → denseSeq ℂ n ∈ F ω) ∧ ω ∈ Z i}
  have hE : MeasurableSet E := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro i
    apply Measurable.and measurable_const
    apply Measurable.and
    · apply Measurable.forall
      intro n
      exact measurable_const.imp ((measurable_pi_apply (denseSeq ℂ n)).comp hF)
    · exact measurableSet_setOfPred.mp (hZ i)
  refine ⟨E, hE, ?_⟩
  intro ω ho hreg hzero
  have hFeq : F ω = closure (C ω) := (closure_eq_closure_inter_denseSeq ho).symm
  constructor
  · rintro ⟨i, hDball, hall, hz⟩
    have hsmall : closedBall (a i) (r i) ⊆ ball (a i) (2 * r i) :=
      closedBall_subset_ball (by linarith [hr i])
    obtain ⟨hcont, hnonneg⟩ := hreg i (hsmall.trans hDball)
    obtain ⟨x, hx, hxzero⟩ := (hZgood i ω hcont hnonneg).2 hz
    have hball : ball (a i) (2 * r i) ⊆ closure (C ω) := by
      have hd := (denseRange_denseSeq ℂ).open_subset_closure_inter
        (isOpen_ball : IsOpen (ball (a i) (2 * r i)))
      apply hd.trans
      apply closure_minimal _ isClosed_closure
      rintro y ⟨hy, n, rfl⟩
      simpa only [hFeq] using hall n hy
    have hxint : x ∈ interior (closure (C ω)) :=
      (interior_maximal hball isOpen_ball) (hsmall hx)
    have hxD := hDball (hsmall hx)
    exact ⟨x, hxD, hxint, (hzero x hxD).2 hxzero⟩
  · rintro ⟨x, hxD, hxint, hxnot⟩
    obtain ⟨i, hxball, hball⟩ := hcover (interior (closure (C ω)) ∩ D)
      (isOpen_interior.inter hD) x ⟨hxint, hxD⟩
    have hDball : ball (a i) (2 * r i) ⊆ D := hball.trans inter_subset_right
    have hsmall : closedBall (a i) (r i) ⊆ ball (a i) (2 * r i) :=
      closedBall_subset_ball (by linarith [hr i])
    obtain ⟨hcont, hnonneg⟩ := hreg i (hsmall.trans hDball)
    refine ⟨i, hDball, ?_, (hZgood i ω hcont hnonneg).1 ⟨x, hxball, (hzero x hxD).1 hxnot⟩⟩
    intro n hn
    rw [hFeq]
    exact interior_subset (hball hn).1

/-- Balls with dense-sequence centres and reciprocal natural radii form a
countable cover whose doubled balls remain in a prescribed open set. -/
theorem exists_denseSeq_doubled_ball_subset
    (U : Set ℂ) (hU : IsOpen U) (x : ℂ) (hx : x ∈ U) :
    ∃ p : ℕ × ℕ,
      x ∈ ball (denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1)) ∧
      ball (denseSeq ℂ p.1) (2 * (1 / ((p.2 : ℝ) + 1))) ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by positivity)
  have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨m, hm⟩ := (denseRange_denseSeq ℂ).exists_mem_open
    (isOpen_ball : IsOpen (ball x (1 / ((n : ℝ) + 1))))
    ⟨x, mem_ball_self hr⟩
  refine ⟨(m, n), ?_, ?_⟩
  · simpa only [mem_ball, dist_comm] using hm
  · intro y hy
    apply hball
    simp only [mem_ball] at hm hy ⊢
    have htri := dist_triangle y (denseSeq ℂ m) x
    linarith

/-- The regularization zero test is measurable for every open domain in the
plane, with no supplied choice of a countable basis. -/
theorem exists_measurable_regularization_zero_test_of_open
    {Ω : Type*} [MeasurableSpace Ω] (C : Ω → Set ℂ) (hC : Measurable C)
    (f : Ω → ℂ → ℝ) (hf : ∀ x : ℂ, Measurable (fun ω => f ω x))
    (D : Set ℂ) (hD : IsOpen D) :
    ∃ E : Set Ω, MeasurableSet E ∧ ∀ ω,
      IsOpen (C ω) →
      (∀ (p : ℕ × ℕ), closedBall (denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ D →
        ContinuousOn (f ω) (closedBall (denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1))) ∧
        ∀ x ∈ closedBall (denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1)), 0 ≤ f ω x) →
      (∀ x ∈ D, x ∉ C ω ↔ f ω x = 0) →
      (ω ∈ E ↔ ∃ x ∈ D, x ∈ interior (closure (C ω)) ∧ x ∉ C ω) := by
  apply exists_measurable_regularization_zero_test C hC f hf D hD
    (fun p : ℕ × ℕ => denseSeq ℂ p.1) (fun p => 1 / ((p.2 : ℝ) + 1))
  · intro p
    positivity
  · exact exists_denseSeq_doubled_ball_subset

end MatedCRT
