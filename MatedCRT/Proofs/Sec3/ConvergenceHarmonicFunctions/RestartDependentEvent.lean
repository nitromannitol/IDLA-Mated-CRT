import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusDisconnection
import MatedCRT.Proofs.Infra.RandomWalk

/-! # Restarting at a random boundary cell -/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

/-- At a first hit, a continuation event may depend on the hit vertex.
The bound holds uniformly over admissible restart vertices and does not
require independence between the hit vertex and the continuation. -/
theorem srwLaw_hitTime_dependent_continuation_le
    (m : ℤ → ℤ → ℕ) (D B : Set ℤ) (E : ℤ → Set (ℕ → ℤ))
    (hE : ∀ b, MeasurableSet (E b)) (z : ℤ) (c : ℝ≥0∞)
    (hbound : ∀ b ∈ B, srwLaw m b (E b) ≤ c) :
    srwLaw m z (⋃ k : ℕ, {x | vHitTime D x = k ∧ x k ∈ B ∧
      pathShift k x ∈ E (x k)}) ≤ c := by
  classical
  let F : (ℕ → ℤ) → ℝ≥0∞ := fun x => (E (x 0)).indicator 1 x
  have hF : Measurable F := by
    have hpair : Measurable (fun p : ℤ × (ℕ → ℤ) => (E p.1).indicator 1 p.2) :=
      measurable_from_prod_countable_right (fun b => by
        exact (measurable_const : Measurable (1 : (ℕ → ℤ) → ℝ≥0∞)).indicator (hE b))
    convert hpair.comp
      ((measurable_pi_apply 0).prodMk (measurable_id : Measurable (id : (ℕ → ℤ) → (ℕ → ℤ)))) using 1
    funext x
    rfl
  have hbound' : ∀ b ∈ B, (∫⁻ x, F x ∂srwLaw m b) ≤ c := by
    intro b hb
    have heq : (∫⁻ x, F x ∂srwLaw m b) = srwLaw m b (E b) := by
      calc
        _ = ∫⁻ x, (E b).indicator 1 x ∂srwLaw m b := by
          apply lintegral_congr_ae
          filter_upwards [srwLaw_ae_start m b] with x hx
          simp [F, hx]
        _ = _ := lintegral_indicator_one (hE b)
    rw [heq]
    exact hbound b hb
  have hsum := tsum_lintegral_hitTime_indicator_continuation_le m D B hF z c hbound'
  calc
    _ ≤ ∑' k : ℕ, srwLaw m z {x | vHitTime D x = k ∧ x k ∈ B ∧
        pathShift k x ∈ E (x k)} := measure_iUnion_le _
    _ = ∑' k : ℕ, ∫⁻ x, {x | vHitTime D x = k}.indicator
        (fun x => B.indicator 1 (x k) * F (pathShift k x)) x ∂srwLaw m z := by
      apply tsum_congr
      intro k
      have hmeas : MeasurableSet {x : ℕ → ℤ | vHitTime D x = k ∧ x k ∈ B ∧
          pathShift k x ∈ E (x k)} := by
        have hcont : MeasurableSet {x : ℕ → ℤ | pathShift k x ∈ E (x k)} := by
          have hp : Measurable (fun p : ℤ × (ℕ → ℤ) => (E p.1).indicator 1 p.2) :=
            measurable_from_prod_countable_right (fun b => by
              exact (measurable_const : Measurable (1 : (ℕ → ℤ) → ℝ≥0∞)).indicator (hE b))
          have hm := hp.comp ((measurable_pi_apply k).prodMk (measurable_pathShift k))
          have heq : {x : ℕ → ℤ | pathShift k x ∈ E (x k)} =
              (fun x => (E (x k)).indicator (1 : (ℕ → ℤ) → ℝ≥0∞) (pathShift k x)) ⁻¹' {1} := by
            ext x
            by_cases hx : pathShift k x ∈ E (x k) <;> simp [hx]
          rw [heq]
          exact hm (measurableSet_singleton 1)
        exact (measurableSet_vHitTime_eq D k).inter
          (((Set.to_countable B).measurableSet.preimage (measurable_pi_apply k)).inter hcont)
      rw [← lintegral_indicator_one hmeas]
      apply lintegral_congr
      intro x
      by_cases h1 : vHitTime D x = k <;> by_cases h2 : x k ∈ B <;>
        by_cases h3 : pathShift k x ∈ E (x k) <;>
        simp [h1, h2, h3, F, pathShift, Set.indicator]
    _ ≤ c := hsum

end MatedCRT

#print axioms MatedCRT.srwLaw_hitTime_dependent_continuation_le
