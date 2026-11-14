import MatedCRT.FirstPass.Derived.TemplateEventWalkLimit

/-! # Template disconnection under a change of clock -/

set_option autoImplicit false

namespace MatedCRT.TemplateEventWalkLimit

open MeasureTheory Filter Set Topology MarkovProcess HarmonicBalls
open MatedCRT.TemplateEventCompactOpen MatedCRT.TemplateEventOpen
open ReflectedGMS.GMS ReflectedGMS.StatementIngredients
open scoped ENNReal NNReal

/-- A path-dependent increasing change of clock preserves the template-event
probability bound obtained from weak convergence to an isotropic Brownian law. -/
theorem eventually_eventually_lt_measure_template_of_timeChange
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2}
    {Z : ℝ≥0 → Ω → ContinuousPath ℂ} {target : AnisotropicBrownianTarget}
    (h : ConvergesWeaklyInC Q Y target) {c : ℝ≥0} (hc : 0 < c)
    (hcov : target.covariance = (c : ℝ) • 1)
    (hclock : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), ∀ᵐ ω ∂Q, ∃ ψ : ℝ≥0 ≃o ℝ≥0,
      ∀ t, Z ε ω t = eucPathToComplex (Y ε ω) (ψ t))
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      1 - η < Q {ω | Z ε ω ∈ templateDisconnectionEvent r} := by
  filter_upwards [eventually_eventually_lt_measure_templateDisconnectionEvent h hc hcov hη]
    with r hr
  filter_upwards [hr, hclock] with ε hε hclockε
  refine hε.trans_le (measure_mono_ae ?_)
  filter_upwards [hclockε] with ω ⟨ψ, hψ⟩ hω
  exact comp_mem_templateDisconnectionEvent hω ψ hψ

end MatedCRT.TemplateEventWalkLimit
