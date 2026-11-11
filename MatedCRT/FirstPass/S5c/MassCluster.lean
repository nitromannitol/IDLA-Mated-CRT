import MatedCRT.Defs.Map

/-!
# FIRST PASS, Lemma 5.3: quantum mass of the filled discrete cluster

The filled cluster `U_ε = fillCells D_ε` is a finite union of cells. Each cell has quantum mass at most `ε` (area
parametrization; `measure_cell_of_area_parametrized`, Proofs/Sec3/ConvergenceNormalizedExitTime/CellIntegral.lean:19),
so `μ (U_ε) ≤ ε |D_ε| ≤ t` by the conservation of mass `|D_ε| ≤ t ε⁻¹` (`DiscreteConservationOfMassCorrectedStmt`, Draft
Lemma 4.5). Finite subadditivity only; the cell masses and the cardinality bound are hypotheses here.
-/

namespace MatedCRT.S5c

open MeasureTheory Set
open scoped ENNReal

/-- **Quantum mass of a finite union of cells** (G-5-3 eq. (7)): `μ (fillCells A) ≤ ε |A| ≤ t`. -/
theorem measure_fillCells_le_of_card {μ : Measure ℂ} {ε t : ℝ} {η : ℝ → ℂ} {A : Set ℤ}
    (hε : 0 < ε) (hA : A.Finite) (hcm : ∀ k : ℤ, μ (cell ε η k) ≤ ENNReal.ofReal ε)
    (hcard : (A.ncard : ℝ) ≤ t / ε) : μ (fillCells ε η A) ≤ ENNReal.ofReal t := by
  have hset : fillCells ε η A = ⋃ k ∈ hA.toFinset, cell ε η k := by
    ext x
    simp [fillCells]
  have h1 : μ (fillCells ε η A) ≤ ∑ k ∈ hA.toFinset, μ (cell ε η k) := by
    rw [hset]
    exact measure_biUnion_finset_le _ _
  have h2 : ∑ k ∈ hA.toFinset, μ (cell ε η k) ≤ ∑ _k ∈ hA.toFinset, ENNReal.ofReal ε :=
    Finset.sum_le_sum fun k _ => hcm k
  have h3 : ∑ _k ∈ hA.toFinset, ENNReal.ofReal ε = (A.ncard : ℝ≥0∞) * ENNReal.ofReal ε := by
    rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card A hA]
  have h4 : (A.ncard : ℝ≥0∞) * ENNReal.ofReal ε = ENNReal.ofReal ((A.ncard : ℝ) * ε) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have h5 : ENNReal.ofReal ((A.ncard : ℝ) * ε) ≤ ENNReal.ofReal t :=
    ENNReal.ofReal_le_ofReal ((le_div_iff₀ hε).1 hcard)
  exact h1.trans (h2.trans (h3 ▸ h4 ▸ h5))

end MatedCRT.S5c
