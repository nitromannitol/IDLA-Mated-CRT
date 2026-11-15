import MatedCRT.FirstPass.Derived.DMSPostLastConditionedLaw
import MatedCRT.Proofs.Sec1.EnvironmentScaling.IntegrableReferenceObservables

/-! # Brownian reference path and observable laws -/

open MeasureTheory ProbabilityTheory
open HarmonicBalls
open scoped NNReal

noncomputable section

namespace MatedCRT.Sec1

variable {Ω : Type} [MeasurableSpace Ω]

/-- The Brownian reference law with the post-last-zero law supplied. -/
theorem exists_referenceConeConditionedPath_law_of_isBrownianReal_derived
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    ∃ F : Ω → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F) :=
  exists_referenceConeConditionedPath_law_of_isBrownianReal MatedCRT.Proposed.dms14Remark44PostLastZeroLaw hγ0 hγ2 B hB hBm

/-- The Brownian reference law with the post-last-zero law supplied. -/
theorem exists_referenceConeConditionedPath_map_eq_of_isBrownianReal_derived
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {ν : Measure (MarkovProcess.ContinuousPath ℝ)}
    (hν : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) ν) :
    ∃ F : Ω → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      P.map F = ν :=
  exists_referenceConeConditionedPath_map_eq_of_isBrownianReal MatedCRT.Proposed.dms14Remark44PostLastZeroLaw hγ0 hγ2 B hB hBm hν

/-- The Brownian reference law with the post-last-zero law supplied. -/
theorem map_finite_coneObservables_eq_brownian_reference_derived
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    (B : ℝ≥0 → Ω0 → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P0) (hBm : ∀ t, Measurable (B t))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P' hC' hcirc')
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))
    {n : ℕ} (c : Fin n → GFFObservable.Admissible) :
    ∃ F : Ω0 → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P0, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F) ∧
      P.map (fun ω i => (c i).1.eval (hC ω) (hcirc ω)) =
        ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
          (fun p i => coneTransport p (c i)) :=
  map_finite_coneObservables_eq_brownian_reference MatedCRT.Proposed.dms14Remark44PostLastZeroLaw hγ0 hγ2 h B hB hBm hW hlat c

/-- The Brownian reference law with the post-last-zero law supplied. -/
theorem map_coneObservables_eq_brownian_reference_derived
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    (B : ℝ≥0 → Ω0 → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P0) (hBm : ∀ t, Measurable (B t))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P' hC' hcirc')
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω))) :
    ∃ F : Ω0 → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P0, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F) ∧
      P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) =
        ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
          coneTransport :=
  map_coneObservables_eq_brownian_reference MatedCRT.Proposed.dms14Remark44PostLastZeroLaw hγ0 hγ2 h B hB hBm hW hlat

/-- The Brownian reference law with the post-last-zero law supplied. -/
theorem map_coneObservables_index_eq_brownian_assembly_derived
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    (B : ℝ≥0 → Ω0 → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P0) (hBm : ∀ t, Measurable (B t))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P' hC' hcirc')
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))
    {ι : Type} (o : ι → GFFObservable.Admissible) :
    (∀ᵐ ω ∂P, ∀ i, ObservableRadialIntegrable (hcirc ω) (o i).1) ∧
    AEMeasurable (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) P ∧
    (∀ᵐ ω ∂P, ∀ i, (o i).1.eval (hC ω) (hcirc ω) =
      coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (o i)) ∧
    ∃ F : Ω0 → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P0, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F) ∧
      P.map (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) =
        ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
          (fun p i => coneTransport p (o i)) :=
  map_coneObservables_index_eq_brownian_assembly MatedCRT.Proposed.dms14Remark44PostLastZeroLaw hγ0 hγ2 h B hB hBm hW hlat o

end MatedCRT.Sec1
