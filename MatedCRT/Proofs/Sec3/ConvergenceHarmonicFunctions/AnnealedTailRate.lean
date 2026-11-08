import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnealedTailAE

/-! Quantitative annealed bounds from environment and quenched bounds. -/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

/-- An environment exceptional-probability bound and an almost-everywhere
quenched tail bound add to an annealed outer-probability bound. -/
theorem sectionwiseOuterProb_le_of_ae_quenched_and_environment
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Ω → Measure X)
    (hκ : ∀ ω, κ ω univ ≤ 1) (E : Set (Ω × X)) (B : Set Ω)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hB : P B ≤ ENNReal.ofReal a)
    (hgood : ∀ᵐ ω ∂P, ω ∉ B → κ ω (Prod.mk ω ⁻¹' E) ≤ ENNReal.ofReal c) :
    sectionwiseOuterProb P κ E ≤ ENNReal.ofReal (a + c) := by
  calc
    _ ≤ P B + ENNReal.ofReal c :=
      sectionwiseOuterProb_le_measure_add_of_ae_quenched_le P κ hκ E B _ hgood
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal c := add_le_add_left hB _
    _ = ENNReal.ofReal (a + c) := (ENNReal.ofReal_add ha hc).symm

end MatedCRT

#print axioms MatedCRT.sectionwiseOuterProb_le_of_ae_quenched_and_environment
