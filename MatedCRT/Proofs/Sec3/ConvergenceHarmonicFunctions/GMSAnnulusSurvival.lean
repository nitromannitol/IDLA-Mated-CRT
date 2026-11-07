import MatedCRT.Proposed.GwynneMillerSheffield
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusPolynomialBound

/-! # Nested-disk survival under the GMS annulus estimate -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- On a good environment for the GMS annulus estimate, the probability of
surviving through nested disk boundaries has polynomial decay. The planar
separating walks and admissibility of the radii are kept explicit. -/
theorem measure_nested_disk_survival_le_power_of_gms
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (m : ℤ → ℤ → ℕ) (ε β ρ : ℝ) (η : ℝ → ℂ)
      (z : ℂ) (a : ℤ) (r : ℕ → ℝ) (n : ℕ) (U : ℕ → Set ℤ)
      (cutoff distance factor : ℝ),
      0 ≤ cutoff → 0 < distance → 0 ≤ factor →
      distance ≤ factor * cutoff * (2 : ℝ) ^ (n + 1) →
      Continuous η → Antitone r → (∀ i ≤ n, 0 < r i) →
      a ∈ interiorCellVertices ε η (ball z (r n)) →
      a ∈ cellVertices ε η (ball z (r n / 2)) →
      (∀ v w, m v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty) →
      (∀ i ≤ n, ∀ v ∈ interiorCellVertices ε η (ball z (r i)), ∀ w,
        m v w ≠ 0 → w ∈ interiorCellVertices ε η (ball z (r i)) ∪
          cellVertices ε η (sphere z (r i))) →
      (∀ᵐ x ∂srwLaw m a, vExitTime (interiorCellVertices ε η (ball z (r 0))) x ≠ ⊤) →
      (∀ i < n, cellVertices ε η (sphere z (r (i + 1))) ∩
        cellVertices ε η (ball z (r (i + 1))) ⊆
          cellVertices ε η (ball z (r i / 2))) →
      (∀ i ≤ n, ∃ y b, y ∈ cellVertices ε η (sphere z (r i / 4)) ∧
        b ∈ cellVertices ε η (sphere z (r i)) ∧
        ∃ w : (adjGraph m).Walk y b, ∀ u ∈ w.support, u ∉ U i) →
      z ∈ ball 0 ρ →
      (∀ i ≤ n, ε ^ β ≤ r i / 2 ∧ r i / 2 ≤ ρ ∧
        ball z (2 * (r i / 2)) ⊆ ball 0 ρ) →
      (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
        ball z (2 * s) ⊆ ball 0 ρ → ∀ v ∈ cellVertices ε η (ball z s),
        ENNReal.ofReal p ≤ srwLaw m v
          {x | ∀ y ∈ cellVertices ε η (sphere z (s / 2)),
            walkDisconnectsBeforeHit m (cellVertices ε η (sphere z (2 * s))) y x}) →
      srwLaw m a {x | ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) <
        vHitTime (cellVertices ε η (sphere z (r i))) x → x j ∈ U i} ≤
        ENNReal.ofReal ((factor * cutoff / distance) ^ ν) := by
  obtain ⟨ν, hν, hbound⟩ := measure_nested_disk_survival_le_power_of_disconnection hp hp1
  refine ⟨ν, hν, ?_⟩
  intro m ε β ρ η z a r n U cutoff distance factor hcut hdist hfactor hscale
    hη hr hpos ha haS hadj hnb hfin hnext hgeom hz hadmiss hgood
  apply hbound m ε η z a r n
    (fun i => cellVertices ε η (sphere z (r i / 4))) U
    (fun i => cellVertices ε η (ball z (r i / 2))) cutoff distance factor
    hcut hdist hfactor hscale hη hr hpos ha haS hadj hnb hfin hnext hgeom
  intro i hi v hv
  obtain ⟨hlow, hhigh, hball⟩ := hadmiss i hi
  have h := hgood z hz (r i / 2) hlow hhigh hball v hv
  convert h using 1; congr 2; ring

end MatedCRT
