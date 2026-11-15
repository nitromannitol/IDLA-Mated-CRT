import MatedCRT.FirstPass.Derived.AnisotropicTargetBallClock
import LatticeProb.Prob.WeakPathExitOscillationProbability
import LatticeProb.Prob.ConvergesWeaklyInCMapping

/-! # Neighboring ball exits for anisotropic Brownian limits -/

set_option autoImplicit false

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal
open ReflectedGMS.StatementIngredients
open LatticeProb.UnboundedRayIntervalIntegrand

namespace MatedCRT

/-- Weak path convergence to the target controls neighboring ball-exit oscillations. -/
theorem tendsto_measure_ballExitOscillationGood_compl_anisotropic
    (target : AnisotropicBrownianTarget)
    {μs : ℕ → ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)}
    (hweak : Tendsto μs atTop (𝓝 target.pathLaw))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    {r η : ℝ} (hr : 0 < r) (hη : 0 < η) :
    Tendsto (fun n => (μs n : Measure (BouRabeeGwynne.BrownianPath 2))
      (ballExitOscillationGood (d := 2) (r - δ n) (r + δ n) η)ᶜ) atTop (𝓝 0) :=
  tendsto_measure_ballExitOscillationGood_compl hweak hδ hη
    (ae_ballClock_regular_anisotropicBrownianTarget target hr)

/-- Along positive scales, the GMS convergence statement controls neighboring exits. -/
theorem tendsto_measure_ballExitOscillationGood_compl_of_convergesWeaklyInC
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2)
    (target : AnisotropicBrownianTarget)
    (hY : ∀ ε, AEMeasurable (Y ε) Q)
    (hconv : ReflectedGMS.GMS.ConvergesWeaklyInC Q Y target)
    {ε : ℕ → ℝ≥0} (hε : Tendsto ε atTop (𝓝[>] 0))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    {r η : ℝ} (hr : 0 < r) (hη : 0 < η) :
    Tendsto (fun n => Q ((Y (ε n)) ⁻¹'
      (ballExitOscillationGood (d := 2) (r - δ n) (r + δ n) η)ᶜ)) atTop (𝓝 0) := by
  apply tendsto_measure_ballExitOscillationGood_compl_of_map_eq Q (fun n => hY (ε n))
    (fun n => ?_) ((LatticeProb.Portmanteau.tendsto_imageLaw_of_convergesWeaklyInC hY hconv).comp hε)
    hδ hη (ae_ballClock_regular_anisotropicBrownianTarget target hr)
  rfl

end MatedCRT
