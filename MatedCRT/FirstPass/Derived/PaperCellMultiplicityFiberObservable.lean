import MatedCRT.FirstPass.Derived.PaperCellMultiplicityFibers
import Mathlib.MeasureTheory.Function.AEMeasurableOrder

/-! # Multiplicity observables determined by curve fibers -/

set_option autoImplicit false

open Function MeasureTheory Topology

namespace MatedCRT

/-- Equality of curve fibers transfers almost-everywhere measurability of the
whole paper cell multiplicity array, at a common random mesh. -/
theorem aemeasurable_cellMult_of_ae_same_fibers
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ → ℂ) (ε : Ω → ℝ)
    (hf : AEMeasurable (fun ω (j k : ℤ) => cellMult (ε ω) (f ω) j k) μ)
    (hfg : ∀ᵐ ω ∂μ, IsProperMap (f ω) ∧ Surjective (f ω) ∧
      IsProperMap (g ω) ∧ Surjective (g ω) ∧
      ∀ s t, f ω s = f ω t ↔ g ω s = g ω t) :
    AEMeasurable (fun ω (j k : ℤ) => cellMult (ε ω) (g ω) j k) μ := by
  apply hf.congr
  filter_upwards [hfg] with ω hω
  funext j k
  exact cellMult_eq_of_proper_maps_same_fibers (f ω) (g ω)
    hω.1 hω.2.2.1 hω.2.1 hω.2.2.2.1 hω.2.2.2.2 (ε ω) j k

end MatedCRT
