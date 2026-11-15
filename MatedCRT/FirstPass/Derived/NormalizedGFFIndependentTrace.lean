import MatedCRT.FirstPass.Derived.NormalizedGFFCoordinateBridge
import LatticeProb.LQG.FieldIndependentInsertedTrace

/-! # Independent traces for normalized whole-plane fields -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric MatedCRTHarmonic

namespace MatedCRT

/-- The logarithmically inserted area of a normalized whole-plane field does
not charge an independent planar-null compact trace inside the unit disk. -/
theorem ae_normalizedGFF_insertedArea_trace_eq_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → DistC} (hX : IsNormalizedWPGFF X P)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < LatticeProb.LQG.lqgQ γ)
    {g : Ω → C(ℝ, ℂ)} (hgm : Measurable g) (hind : IndepFun g X P)
    {T : Set ℝ} (hT : IsCompact T) (hnull : ∀ᵐ ω ∂P, volume (g ω '' T) = 0) :
    ∀ᵐ ω ∂P, CellScaling.lqgArea γ (GMSCase.addLogSing α (X ω))
      ((g ω '' T) ∩ ball (0 : ℂ) 1) = 0 := by
  obtain ⟨hC, hcirc, hh, _, _, hcircle⟩ := exists_normalizedGFF_coordinates hX
  apply LatticeProb.LQG.ae_lqgArea_addLogSing_trace_eq_zero_of_indep_field
    hX.1 hh _ hγ0 hγ2 hα hgm hind hT hnull
  filter_upwards [hcircle] with ω hω k
  filter_upwards [hω k] with z hz
  simpa only [QuantumZipper.radius, LatticeProb.LQG.dyadicScale] using hz

end MatedCRT
