import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ClockMeasurable

/-!
# Lemma 3.4 (item 4): a jointly measurable version of the approximate clock in `(ω, b, t)`

For a quantum cone field, each dyadic approximate Liouville clock `t ↦ lqgClockApprox γ (hcirc ω) (dyadicScale k) b t`
has a version that is jointly measurable in the environment `ω`, the Brownian path `b` and the time `t`, which agrees with
the clock for every path and every time outside one null set of environments. The field is replaced by the jointly
measurable circle-average version `IsQuantumCone.exists_measurable_circle_version`, and the time-joint integral is
`measurable_clockIntegral`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal

/-- **Time-joint measurable version of the dyadic approximate clock.** For a quantum cone, the approximate clocks at
dyadic scales have a version measurable in `((ω, b), t)` that agrees with them a.s., simultaneously for all paths and
times. -/
theorem IsQuantumCone.exists_measurable_clockApprox_time_version
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcone : IsQuantumCone γ P hC hcirc) (k : ℕ) :
    ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
        G ((ω, b), t) = lqgClockApprox γ (hcirc ω) (dyadicScale k) b t := by
  obtain ⟨H, hH, hsame⟩ := IsQuantumCone.exists_measurable_circle_version hcone (dyadicScale_pos k)
  refine ⟨fun q => ∫ s in (0 : ℝ)..(q.2 : ℝ),
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H q.1.1 (q.1.2 s.toNNReal)),
    measurable_clockIntegral γ (dyadicScale k) H hH, ?_⟩
  filter_upwards [hsame] with ω hω
  intro b t
  simp only [lqgClockApprox, hω]

end MatedCRT
