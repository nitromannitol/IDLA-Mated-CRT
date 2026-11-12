import MatedCRT.FirstPass.Frozen.S2i
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field

/-!
# Uniqueness in law of the circle average process of the quantum cone

Discharges the first-pass frozen input `ConeCircleLawUniqueStep` (`FirstPass/Frozen/S2i.lean:16`).

Two cone fields (`IsConeField`, which contains `IsQuantumCone`) with the same parameter `γ` have the same
joint law of all admissible observables (pairings with test functions and circle averages of positive radius):
`MatedCRT.Sec1.IsQuantumCone.observable_law_eq` (`Proofs/Sec1/EnvironmentScaling/Field.lean:277`), which rests on
the uniqueness of the conditioned Brownian motion law `ν` (`isBMConditionedPositive_unique`), the independence of
the radial and the lateral part, and the uniqueness in law of the lateral part of the whole-plane GFF.
The circle average process `circleProcess` is a coordinate projection of the observable process, hence its law
is the image of the observable law under a measurable map.
-/

namespace MatedCRT

open MeasureTheory HarmonicBalls

/-- The projection from the observable process to the circle average process `(r, z) ↦ h_r(z)`, `r > 0`. -/
noncomputable def observableToCircleProcess :
    (GFFObservable.Admissible → ℝ) → (Set.Ioi (0 : ℝ) × ℂ → ℝ) :=
  fun x p => x ⟨GFFObservable.circle p.1.1 p.2, p.1.2⟩

theorem measurable_observableToCircleProcess : Measurable observableToCircleProcess :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- **`ConeCircleLawUniqueStep`, proved.** Any two `γ`-quantum cone fields have the same law of the circle
average process. -/
theorem coneCircleLawUniqueStep_holds : ConeCircleLawUniqueStep := by
  intro γ _ _ Ω _ P hC hcirc μ hcone Ω' _ P' hC' hcirc' μ' hcone'
  obtain ⟨hP, hq, -⟩ := hcone
  obtain ⟨hP', hq', -⟩ := hcone'
  have hlaw := Sec1.IsQuantumCone.observable_law_eq hq hq'
  have e1 : (fun ω => circleProcess (hcirc ω)) =
      observableToCircleProcess ∘ wholePlaneObservableProc hC hcirc := rfl
  have e2 : (fun ω => circleProcess (hcirc' ω)) =
      observableToCircleProcess ∘ wholePlaneObservableProc hC' hcirc' := rfl
  rw [e1, e2, ← Measure.map_map measurable_observableToCircleProcess (Sec1.IsQuantumCone.measurable_observables hq),
    ← Measure.map_map measurable_observableToCircleProcess (Sec1.IsQuantumCone.measurable_observables hq'), hlaw]

end MatedCRT
