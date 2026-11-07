import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusIteration
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusPowerDecay

/-! # Polynomial bound for annulus crossing events -/

namespace MatedCRT

open Set MeasureTheory
open scoped ENNReal

/-- Finite-scale disconnection estimates imply a polynomial bound on the
probability of completing the specified annulus crossings. The deterministic
separating walks remain explicit hypotheses. -/
theorem measure_annulusCrossingEvent_le_power_of_disconnection
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (m : ℤ → ℤ → ℕ) (A I U B S : ℕ → Set ℤ)
      (n : ℕ) (v : ℤ) (cutoff distance factor : ℝ),
      0 ≤ cutoff → 0 < distance → 0 ≤ factor →
      distance ≤ factor * cutoff * (2 : ℝ) ^ (n + 1) →
      (∀ i < n, B (i + 1) ⊆ S i) →
      (∀ i ≤ n, B i ⊆ A i) →
      (∀ i ≤ n, ∃ y a, y ∈ I i ∧ a ∈ A i ∧
        ∃ w : (adjGraph m).Walk y a, ∀ u ∈ w.support, u ∉ U i) →
      (∀ i ≤ n, ∀ v, v ∈ S i → ENNReal.ofReal p ≤ srwLaw m v
        {x | ∀ y ∈ I i, walkDisconnectsBeforeHit m (A i) y x}) →
      v ∈ S n →
      srwLaw m v (annulusCrossingEvent A U B (n + 1)) ≤
        ENNReal.ofReal ((factor * cutoff / distance) ^ ν) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hq1 : 1 - p < 1 := by linarith
  obtain ⟨ν, hν, hbound⟩ := dyadic_crossing_probability_le_power_ratio hq hq1
  refine ⟨ν, hν, ?_⟩
  intro m A I U B S n v cutoff distance factor hcut hdist hfactor hscale
    hnext hBA hgeom hdisc hv
  apply hbound (n + 1) _ cutoff distance factor hcut hdist hfactor hscale
  exact measure_annulusCrossingEvent_le_of_disconnection_finite m A I U B S p hp.le
    n hnext hBA hgeom hdisc v hv

end MatedCRT
