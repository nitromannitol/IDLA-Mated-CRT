import MatedCRT.FirstPass.Derived.BrownianStoppedEndpointContinuity

/-! Continuity of stopped Brownian endpoint laws under parameterized starts. -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne

namespace MatedCRT.BrownianExitLawIdentification

/-- A continuous family of interior starting points has a continuous family of
stopped Brownian endpoint laws. -/
theorem continuous_stoppedBrownianEndpointProbability_comp
    {P : Type*} [TopologicalSpace P] {V : Set (Euc 2)}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ)
    (x : P → Euc 2) (hx : Continuous x) (hxV : ∀ p, x p ∈ V) :
    Continuous (fun p => stoppedBrownianEndpointProbability V hV ρ hρ (x p)) := by
  exact (continuous_stoppedBrownianEndpointProbability hV hVb ρ hρ).comp
    (hx.subtype_mk hxV)

/-- The continuous parameterized kernel has the actual stopped endpoint law. -/
theorem stoppedBrownianEndpointProbability_comp_law
    {P : Type*} [TopologicalSpace P] {V : Set (Euc 2)}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ)
    (x : P → Euc 2) (hx : Continuous x) (hxV : ∀ p, x p ∈ V) :
    Continuous (fun p => stoppedBrownianEndpointProbability V hV ρ hρ (x p)) ∧
      ∀ p, (stoppedBrownianEndpointProbability V hV ρ hρ (x p) : Measure (Euc 2)) =
        (stoppedBrownianLaw V (x p) ρ).map CurveSpace.endPoint := by
  exact ⟨continuous_stoppedBrownianEndpointProbability_comp hV hVb ρ hρ x hx hxV,
    fun _ => rfl⟩

end MatedCRT.BrownianExitLawIdentification
