import MatedCRT.FirstPass.Derived.ExclusiveCellStartTransfer

/-! # Vertex failures and selected-cell failures -/

set_option autoImplicit false

open Set Metric MeasureTheory

namespace MatedCRT

/-- A strict score failure at one of countably many vertices is measurable. -/
theorem measurableSet_vertexScoreFailure {X : Type*} [MeasurableSpace X]
    (score : ℂ × X → ℝ) (hscore : Measurable score) (ρ t : ℝ) :
    MeasurableSet {q : ℤ → ℂ × X |
      ∃ k, (q k).1 ∈ closedBall (0 : ℂ) ρ ∧ t < score (q k)} := by
  have h : {q : ℤ → ℂ × X |
      ∃ k, (q k).1 ∈ closedBall (0 : ℂ) ρ ∧ t < score (q k)} =
      ⋃ k : ℤ, {q | (q k).1 ∈ closedBall (0 : ℂ) ρ ∧ t < score (q k)} := by
    ext q
    simp only [mem_ofPred_eq, mem_iUnion]
  rw [h]
  refine MeasurableSet.iUnion fun k => ?_
  exact (isClosed_closedBall.measurableSet.preimage
    (measurable_fst.comp (measurable_pi_apply k))).inter
    (measurableSet_lt measurable_const (hscore.comp (measurable_pi_apply k)))

/-- Every strict vertex failure gives a selected-cell failure in a slightly larger ball. -/
theorem vertexScoreFailure_subset_selected {X : Type*} {μ : Measure ℂ} {η : ℝ → ℂ}
    (hap : IsAreaParametrized μ η) {ε ρ ρ' t : ℝ} (hε : 0 < ε) (hρ : ρ < ρ')
    (score : ℂ × X → ℝ) (hcont : ∀ x, Continuous fun z => score (z, x))
    (q : ℤ → ℂ × X) (hq : ∀ k, (q k).1 = vertexPoint ε η k) :
    (∃ k, (q k).1 ∈ closedBall (0 : ℂ) ρ ∧ t < score (q k)) →
    ∃ z ∈ closedBall (0 : ℂ) ρ', t < score (z, (q (vertexOf ε η z)).2) := by
  rintro ⟨k, hk, hfail⟩
  let x := (q k).2
  have hp : t < score (vertexPoint ε η k, x) := by
    simpa only [x, ← hq k, Prod.mk.eta] using hfail
  have hopen : IsOpen {z : ℂ | t < score (z, x)} :=
    isOpen_lt continuous_const (hcont x)
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hopen (vertexPoint ε η k) hp
  obtain ⟨z, hz, hzindex⟩ := exists_dist_lt_vertexOf_eq_of_areaParametrized hap hε k
    (lt_min hd (sub_pos.mpr hρ))
  have hzin : z ∈ closedBall (0 : ℂ) ρ' := by
    apply mem_closedBall.mpr
    have hk' : dist (vertexPoint ε η k) (0 : ℂ) ≤ ρ := by
      simpa only [hq k] using mem_closedBall.mp hk
    have hz' : dist (vertexPoint ε η k) z < ρ' - ρ :=
      lt_of_lt_of_le hz (min_le_right _ _)
    have htri := dist_triangle z (vertexPoint ε η k) (0 : ℂ)
    rw [dist_comm z (vertexPoint ε η k)] at htri
    linarith
  refine ⟨z, hzin, ?_⟩
  rw [hzindex]
  apply hball
  rw [mem_ball, dist_comm]
  exact lt_of_lt_of_le hz (min_le_left _ _)

end MatedCRT
