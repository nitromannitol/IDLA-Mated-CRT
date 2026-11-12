import MatedCRT.FirstPass.Derived.ConeReferenceIndep

/-!
# The explicit cone data is a `γ`-quantum cone

Let `(hC₁, c₁)` be the pairings and circle averages of a whole-plane GFF on a probability space `Ω₁`, with
circle averages continuous at every sample and jointly measurable, and let `ν` be the law of the Brownian motion
conditioned to stay positive. On `Ω₁ × C(ℝ≥0, ℝ)` with the product measure `P₁ ⊗ ν`, the cone data
`coneRefPairing`, `coneRefCircle` built from the field and an independent path satisfy all the requirements of
`IsQuantumCone` (the circle averages are measurable and a.s. continuous, the radial process has the law of the
radial process of the cone, the lateral process is independent of it and has the law of the lateral part of a
whole-plane GFF).
-/

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

variable {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} {hC₁ : Ω₁ → (ℂ → ℝ) → ℝ}
  {c₁ : Ω₁ → ℝ → ℂ → ℝ}

/-- **The explicit cone data is a quantum cone.**  For a whole-plane GFF `(hC₁, c₁)` with continuous, jointly
measurable circle averages and a law `ν` of the conditioned Brownian motion with drift `Q - γ`, the pairings and circle averages `coneRefPairing`, `coneRefCircle` on `(Ω₁ × C(ℝ≥0, ℝ), P₁ ⊗ ν)`
form a `γ`-quantum cone (`IsQuantumCone`). -/
theorem isQuantumCone_coneRef [IsProbabilityMeasure P₁] (hh : IsWholePlaneGFF P₁ hC₁ c₁) (γ : ℝ)
    (hcont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c₁ ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable fun q : (Ioi (0 : ℝ) × ℂ) × Ω₁ => c₁ q.2 q.1.1 q.1.2)
    {ν : Measure (ContinuousPath ℝ)} (hν : IsBMConditionedPositive (lqgQ γ - γ) ν) :
    IsQuantumCone γ (P₁.prod ν) (fun p : Ω₁ × ContinuousPath ℝ => coneRefPairing γ (hC₁ p.1) (c₁ p.1) p.2)
      (fun p : Ω₁ × ContinuousPath ℝ => coneRefCircle γ (c₁ p.1) p.2) := by
  have := hν.1
  refine ⟨?_, ?_, ?_, ⟨ν, hν, map_radialProcess_coneRefCircle hh γ hν⟩,
    indepFun_coneRef hh γ hcont hmeas hν, ?_⟩
  · intro φ hφ
    exact measurable_coneRefPairing γ hmeas hh.measurable_pairing hφ
  · intro r z hr
    exact measurable_coneRefCircle γ hmeas hr z
  · exact Filter.Eventually.of_forall fun p => continuousOn_coneRefCircle γ (hcont p.1) p.2
  · exact ⟨Ω₁, inferInstance, P₁, hC₁, c₁, inferInstance, hh, lateralProcess_coneRef_law hh γ hcont hmeas⟩

end MatedCRT.FirstPass.Derived
