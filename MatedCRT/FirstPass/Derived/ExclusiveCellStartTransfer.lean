import MatedCRT.FirstPass.Derived.CellUniquePointDense
import MatedCRT.FirstPass.Derived.UniformStartStoppedLaw

/-!
# Transferring selected-cell estimates to embedded vertices

A point lying in exactly one cell can be chosen arbitrarily close to any point of the cell.
Combining this with continuity of stopped Brownian laws transfers a uniform estimate for
smallest-cell starting points to all embedded vertices at once.
-/

set_option autoImplicit false

open Set Metric MeasureTheory HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- Each embedded vertex has arbitrarily close points whose smallest containing-cell index is that vertex. -/
theorem exists_dist_lt_vertexOf_eq_of_areaParametrized {μ : Measure ℂ} {η : ℝ → ℂ}
    (hap : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (k : ℤ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z, dist (vertexPoint ε η k) z < δ ∧ vertexOf ε η z = k := by
  have hy : vertexPoint ε η k ∈ cell ε η k :=
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  obtain ⟨z, hz, hzk, hzj⟩ := exists_dist_lt_mem_cell_notMem_cell_of_ne hap hε hy hδ
  refine ⟨z, hz, S5c.vertexOf_eq_of_exclusive hzk ?_⟩
  intro j hj
  by_contra hne
  exact hzj j hne hj

/-- A uniform selected-cell bound transfers to all embedded vertices, with the stated slack in
curve distance and additive error. The left-hand side can be any set function of the starting
vertex, so the estimate applies also to outer measures of nonmeasurable path events. -/
theorem vertex_start_bound_of_selected {μ : Measure ℂ} {η : ℝ → ℂ}
    (hap : IsAreaParametrized μ η) {ε ρ ρ' R : ℝ} (hε : 0 < ε) (hρ : ρ < ρ')
    (hρ' : ρ' < R) {κ θ : ℝ≥0∞} (hκ : 0 < κ) (hθ : 0 < θ) :
    ∀ (L : ℤ → Set (ℝ≥0 → ℂ) → ℝ≥0∞) (κ₁ a : ℝ≥0∞),
      (∀ z ∈ closedBall (0 : ℂ) ρ', ∀ A : Set (ℝ≥0 → ℂ),
        L (vertexOf ε η z) A ≤
          planarBrownianMotion z {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁} + a) →
      ∀ k : ℤ, vertexPoint ε η k ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
        L k A ≤ planarBrownianMotion (vertexPoint ε η k)
          {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁ + κ} + (θ + a) := by
  obtain ⟨d, hd, hcont⟩ := StopAtExitCmp.exists_forall_planarBrownianMotion_stopAtExit_le hρ' hκ hθ
  intro L κ₁ a hsel k hk A
  obtain ⟨z, hz, hzindex⟩ := exists_dist_lt_vertexOf_eq_of_areaParametrized hap hε k
    (lt_min hd (sub_pos.mpr hρ))
  have hdist : dist z (vertexPoint ε η k) < d := by
    rw [dist_comm]
    exact lt_of_lt_of_le hz (min_le_left _ _)
  have hzin : z ∈ closedBall (0 : ℂ) ρ' := by
    apply mem_closedBall.mpr
    have hk' := mem_closedBall.mp hk
    have hz' : dist (vertexPoint ε η k) z < ρ' - ρ := lt_of_lt_of_le hz (min_le_right _ _)
    have htri := dist_triangle z (vertexPoint ε η k) (0 : ℂ)
    rw [dist_comm z (vertexPoint ε η k)] at htri
    linarith
  have hyin : vertexPoint ε η k ∈ closedBall (0 : ℂ) ρ' :=
    (closedBall_subset_closedBall hρ.le) hk
  have hbound := hsel z hzin A
  rw [hzindex] at hbound
  calc
    L k A ≤ planarBrownianMotion z
        {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁} + a := hbound
    _ ≤ (planarBrownianMotion (vertexPoint ε η k)
        {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < κ₁ + κ} + θ) + a :=
      add_le_add (hcont _ hyin z hdist κ₁ A).1 le_rfl
    _ = _ := add_assoc _ _ _

end MatedCRT
