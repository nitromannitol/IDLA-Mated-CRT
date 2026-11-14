import LatticeProb.Analysis.MeasureExtOfSmoothTests
import MatedCRT.FirstPass.Derived.PlanarBrownianOccupationMeasure
import MatedCRT.FirstPass.Derived.LimClockOccupationReduction

/-!
# The occupation identity of planar Brownian motion killed on exiting a disc

For `y ∈ B_r(z)` and bounded measurable `f`,

  `E_y ∫_{(0, τ]} f(𝓑_t) dt = 2 ∫_{B_r(z)} G(y, x) f(x) dx`

(`killedBrownianOccupationOnBall`, the Prop `KilledBrownianOccupationOnBall z r`).

Proof. The killed occupation measure and the Green occupation measure `2 G(y, ·) dx` are finite and
integrate every smooth compactly supported test to the same value
(`integral_killedOccupationMeasure_eq_greenOccupationMeasure`), so they are equal
(`LatticeProb.measure_eq_of_forall_integral_contDiff_hasCompactSupport_eq`); integrate `f` against
both (`integral_killedOccupationMeasure`, `integral_greenOccupationMeasure`).

The derived form `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation_derived` supplies
this identity to `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation`, removing its
binder `hK`.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The killed occupation measure of a disc equals its Green occupation measure. -/
theorem killedOccupationMeasure_ball_eq_greenOccupationMeasure {z y : ℂ} {r : ℝ}
    (hy : y ∈ ball z r) :
    killedOccupationMeasure (ball z r) y = greenOccupationMeasure (ball z r) y := by
  have h1 := isFiniteMeasure_killedOccupationMeasure isOpen_ball isBounded_ball (y := y)
    (D := ball z r)
  have h2 := isFiniteMeasure_greenOccupationMeasure hy
  exact LatticeProb.measure_eq_of_forall_integral_contDiff_hasCompactSupport_eq
    fun g hg hgc => integral_killedOccupationMeasure_eq_greenOccupationMeasure hy hg hgc

/-- **The occupation identity of planar Brownian motion killed on exiting a disc**, for bounded
measurable integrands. -/
theorem killedBrownianOccupationOnBall (z : ℂ) (r : ℝ) : KilledBrownianOccupationOnBall z r := by
  rintro y hy f hf ⟨M, hM⟩
  rw [← integral_greenOccupationMeasure, ← killedOccupationMeasure_ball_eq_greenOccupationMeasure hy,
    integral_killedOccupationMeasure isOpen_ball isBounded_ball y hf hM]
  rfl

/-- `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation` with its binder `hK` discharged
by `killedBrownianOccupationOnBall`. -/
theorem frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation_derived
    (𝒮 : SpaceFillingSLEModel) (hlaw : ConeUnitDiskGFFLaw)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) → HasCompactSupport g →
      tsupport g ⊆ ball z r \ ({0, y} : Set ℂ) →
      UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y)))
    (hF0 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → (0 : ℂ) ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ᵐ ω' ∂P', gmcGreenMeasure γ ρ ((1 + ρ) / 2) z 0 r
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (ball z r) < ∞) :
    FrozenLBMGreenOccupationRescaled 𝒮 :=
  frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation 𝒮 hlaw
    (fun z r _ => killedBrownianOccupationOnBall z r) hU hF0

end MatedCRT.KilledOccupation
