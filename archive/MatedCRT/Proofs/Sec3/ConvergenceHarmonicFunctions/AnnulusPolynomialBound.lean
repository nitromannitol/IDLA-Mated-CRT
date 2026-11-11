import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusIteration
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusPowerDecay
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusBarriers

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

/-- A uniform disconnection probability yields polynomial decay for survival
through the nested disk boundaries, once the separating walks are supplied. -/
theorem measure_nested_disk_survival_le_power_of_disconnection
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ)
      (z : ℂ) (a : ℤ) (r : ℕ → ℝ) (n : ℕ) (I U S : ℕ → Set ℤ)
      (cutoff distance factor : ℝ),
      0 ≤ cutoff → 0 < distance → 0 ≤ factor →
      distance ≤ factor * cutoff * (2 : ℝ) ^ (n + 1) →
      Continuous η → Antitone r → (∀ i ≤ n, 0 < r i) →
      a ∈ interiorCellVertices ε η (Metric.ball z (r n)) → a ∈ S n →
      (∀ v w, m v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty) →
      (∀ i ≤ n, ∀ v ∈ interiorCellVertices ε η (Metric.ball z (r i)), ∀ w,
        m v w ≠ 0 → w ∈ interiorCellVertices ε η (Metric.ball z (r i)) ∪
          cellVertices ε η (Metric.sphere z (r i))) →
      (∀ᵐ x ∂srwLaw m a,
        vExitTime (interiorCellVertices ε η (Metric.ball z (r 0))) x ≠ ⊤) →
      (∀ i < n, cellVertices ε η (Metric.sphere z (r (i + 1))) ∩
        cellVertices ε η (Metric.ball z (r (i + 1))) ⊆ S i) →
      (∀ i ≤ n, ∃ y b, y ∈ I i ∧ b ∈ cellVertices ε η (Metric.sphere z (r i)) ∧
        ∃ w : (adjGraph m).Walk y b, ∀ u ∈ w.support, u ∉ U i) →
      (∀ i ≤ n, ∀ v, v ∈ S i → ENNReal.ofReal p ≤ srwLaw m v
        {x | ∀ y ∈ I i, walkDisconnectsBeforeHit m
          (cellVertices ε η (Metric.sphere z (r i))) y x}) →
      srwLaw m a {x | ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) <
        vHitTime (cellVertices ε η (Metric.sphere z (r i))) x → x j ∈ U i} ≤
        ENNReal.ofReal ((factor * cutoff / distance) ^ ν) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hq1 : 1 - p < 1 := by linarith
  obtain ⟨ν, hν, hbound⟩ := dyadic_crossing_probability_le_power_ratio hq hq1
  refine ⟨ν, hν, ?_⟩
  intro m ε η z a r n I U S cutoff distance factor hcut hdist hfactor hscale
    hη hr hpos ha haS hadj hnb hfin hnext hgeom hdisc
  apply hbound (n + 1) _ cutoff distance factor hcut hdist hfactor hscale
  exact measure_nested_disk_survival_le_of_disconnection hη r hr n I U S p hp.le
    hpos ha haS hadj hnb hfin hnext hgeom hdisc

end MatedCRT
