import MatedCRT.FirstPass.Derived.ConeReferenceIsCone
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field

/-! # A quantum cone from an independent field sample and path -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess

namespace MatedCRT.FirstPass.Derived

/-- The reference cone construction also works on a common probability space
when the whole-plane field sample and the conditioned path are independent. -/
theorem isQuantumCone_coneRef_of_independent
    {Ω Ω₁ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₁]
    {P : Measure Ω} {P₁ : Measure Ω₁} [IsProbabilityMeasure P] [IsProbabilityMeasure P₁]
    {hC₁ : Ω₁ → (ℂ → ℝ) → ℝ} {c₁ : Ω₁ → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P₁ hC₁ c₁) (γ : ℝ)
    (hcont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c₁ ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable fun q : (Ioi (0 : ℝ) × ℂ) × Ω₁ => c₁ q.2 q.1.1 q.1.2)
    {U : Ω → Ω₁} {F : Ω → ContinuousPath ℝ}
    (hU : Measurable U) (hF : Measurable F) (hUlaw : P.map U = P₁)
    (hind : IndepFun U F P)
    (hFlaw : IsBMConditionedPositive (lqgQ γ - γ) (P.map F)) :
    IsQuantumCone γ P (fun ω => coneRefPairing γ (hC₁ (U ω)) (c₁ (U ω)) (F ω))
      (fun ω => coneRefCircle γ (c₁ (U ω)) (F ω)) := by
  let ν := P.map F
  let : IsProbabilityMeasure ν := hFlaw.1
  let Q : Ω → Ω₁ × ContinuousPath ℝ := fun ω => (U ω, F ω)
  have hQ : Measurable Q := hU.prodMk hF
  have hQlaw : P.map Q = P₁.prod ν := by
    rw [show P.map Q = (P.map U).prod (P.map F) from
      hind.map_prod_eq_prod_map_map hU.aemeasurable hF.aemeasurable, hUlaw]
  have hcone := isQuantumCone_coneRef hh γ hcont hmeas hFlaw
  have hobs : Measurable (HarmonicBalls.wholePlaneObservableProc
      (fun p : Ω₁ × ContinuousPath ℝ => coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2)
      (fun p : Ω₁ × ContinuousPath ℝ => coneRefCircle γ (c₁ p.1) p.2)) := by
    apply measurable_pi_iff.mpr
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact hcone.measurable_pairing φ ho
    | circle r z => exact hcone.measurable_circle r z ho
  apply MatedCRT.Sec1.IsQuantumCone.of_observable_law_eq hcone
  · intro φ hφ
    exact (measurable_coneRefPairing γ hmeas hh.measurable_pairing hφ).comp hQ
  · intro r z hr
    exact (measurable_coneRefCircle γ hmeas hr z).comp hQ
  · exact Filter.Eventually.of_forall fun ω => continuousOn_coneRefCircle γ (hcont (U ω)) (F ω)
  · rw [← hQlaw, Measure.map_map hobs hQ]
    rfl

end MatedCRT.FirstPass.Derived
