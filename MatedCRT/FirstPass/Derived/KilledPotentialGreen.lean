import MatedCRT.FirstPass.Derived.KilledOccupationEnergy
import HarmonicBalls.Proofs.Potential.GreenOccupationBoundary
import HarmonicBalls.Proofs.Potential.LQGClockNearStart
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-!
# The potential of an occupation functional of killed Brownian motion is a Green potential

For an open set `D` and a Borel rate `f ≥ 0`, the potential `u_f(x) = E_x[∫_0^{τ_D} f(B_s) ds]` of the occupation
functional of planar Brownian motion killed on exiting `D` (`killedPotential`) is the integral of `f` against the
occupation measure of the killed motion (`killedPotential_eq_lintegral_occupationMeasure`). On a smooth bounded open
set the occupation measure is the Green measure `2 G_D(x, y) dy` (the factor `2` is the one of the generator `Δ/2`;
`HarmonicBalls.GreenOccupation.occupationMeasure_eq_greenMeasure_all`), so

  `u_f(x) = ∫ 2 G_D(x, y) f(y) dy`

(`killedPotential_eq_lintegral_greenFunction`), in particular on every disc `B(0, R)`
(`killedPotential_ball_eq_lintegral_greenFunction`). This identifies the potentials entering the maximal inequality
for occupation functionals with Green potentials (Armitage–Gardiner, §4.3; Fukushima–Oshima–Takeda (2011), §5.1).
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess HarmonicBalls

variable {D : Set ℂ}

/-- The potential of the occupation functional is the integral of the rate against the occupation measure of
Brownian motion killed on exiting `D`. -/
theorem killedPotential_eq_lintegral_occupationMeasure (hD : IsOpen D) {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    (x : ℂ) : killedPotential D f x = ∫⁻ y, f y ∂GreenOccupation.occupationMeasure D hD x := by
  rw [GreenOccupation.lintegral_occupationMeasure hD x hf]
  refine lintegral_congr fun b => ?_
  rw [← lintegral_indicator measurableSet_Ioi, indicator_indicator]
  rfl

/-- **The potential of the occupation functional is a Green potential.** On a smooth bounded open set `D`,
`u_f(x) = ∫ 2 G_D(x, y) f(y) dy`. -/
theorem killedPotential_eq_lintegral_greenFunction (hD : IsSmoothBoundedOpen D) {f : ℂ → ℝ≥0∞}
    (hf : Measurable f) (x : ℂ) :
    killedPotential D f x = ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y := by
  have hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  rw [killedPotential_eq_lintegral_occupationMeasure hDo hf,
    GreenOccupation.occupationMeasure_eq_greenMeasure_all hD x, GreenOccupation.greenMeasure,
    lintegral_withDensity_eq_lintegral_mul _
      ((measurable_greenFunction hDo x).const_mul 2).ennreal_ofReal hf]
  rfl

/-- The potential of the occupation functional of Brownian motion killed on exiting the disc `B(0, R)` is the
Green potential `∫ 2 G_{B(0,R)}(x, y) f(y) dy`. -/
theorem killedPotential_ball_eq_lintegral_greenFunction {R : ℝ} (hR : 0 < R) {f : ℂ → ℝ≥0∞}
    (hf : Measurable f) (x : ℂ) :
    killedPotential (Metric.ball 0 R) f x =
      ∫⁻ y, ENNReal.ofReal (2 * greenFunction (Metric.ball 0 R) x y) * f y :=
  killedPotential_eq_lintegral_greenFunction (isSmoothBoundedOpen_ball_of_pos 0 hR) hf x

end MatedCRT
