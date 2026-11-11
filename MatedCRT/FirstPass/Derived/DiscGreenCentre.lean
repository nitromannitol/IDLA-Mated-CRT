import MatedCRT.FirstPass.Frozen.S1c
import MatedCRT.FirstPass.Frozen.S2g
import HarmonicBalls.Proofs.Potential.GreenBall

/-!
# The Green function of a disc with pole at the centre

Discharges two first-pass frozen inputs of classical potential theory:

* `FrozenGreenBallCentre` (FirstPass/Frozen/S2g.lean): for `R > 0` and `0 < ‖x‖ < R`,
  `G_{B_R}(0, x) = (2π)⁻¹ log (R / ‖x‖)`;
* `FrozenDiskGreenNonnegCont` (FirstPass/Frozen/S1c.lean): `G_{B_R}(0, ·)` is nonnegative and continuous on
  `B_R ∖ {0}`.

Both follow from the explicit formula for the Green function of a disc,
`HarmonicBalls.greenFunction_ball` (Harmonic-Balls arXiv:2208.11795, Proposition 2.3; Armitage and Gardiner,
*Classical Potential Theory*, §4.1; Doob (1984), Ch. II §1, equation (1.1), divided by `2π`), evaluated at the
centre, and from `HarmonicBalls.continuousOn_greenFunction_ball`.
-/

namespace MatedCRT

open Metric

/-- The explicit disc kernel `HarmonicBalls.greenBall` with pole at the centre:
`greenBall R 0 x = (2π)⁻¹ log (R / ‖x‖)` for `R > 0`. -/
theorem greenBall_zero_left {R : ℝ} (hR : 0 < R) (x : ℂ) :
    HarmonicBalls.greenBall R 0 x = (2 * Real.pi)⁻¹ * Real.log (R / ‖x‖) := by
  unfold HarmonicBalls.greenBall
  have h1 : ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) 0 * x‖ = R ^ 2 := by
    rw [map_zero, zero_mul, sub_zero, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have h2 : ‖(0 : ℂ) - x‖ = ‖x‖ := by rw [zero_sub, norm_neg]
  have h3 : R ^ 2 / (R * ‖x‖) = R / ‖x‖ := by rw [pow_two, mul_div_mul_left _ _ hR.ne']
  rw [h1, h2, h3]

/-- The frozen input `FrozenGreenBallCentre` holds: the Green function of the disc `B_R(0)` with pole at the centre
is `G_{B_R}(0, x) = (2π)⁻¹ log (R / ‖x‖)` for `0 < ‖x‖ < R` (normalization `ΔG = -δ`). -/
theorem frozenGreenBallCentre_holds : FrozenGreenBallCentre := by
  intro R hR x hx0 hxR
  have hx : x ∈ ball (0 : ℂ) R := mem_ball_zero_iff.2 hxR
  have hne : (0 : ℂ) ≠ x := fun h => (norm_pos_iff.1 hx0) h.symm
  rw [HarmonicBalls.greenFunction_ball (mem_ball_self hR) hx hne, greenBall_zero_left hR]

/-- The frozen input `FrozenDiskGreenNonnegCont` holds: for `R > 0`, the Green function `G_{B_R}(0, ·)` of the disc
with pole at the centre is nonnegative and continuous on `B_R ∖ {0}`. -/
theorem frozenDiskGreenNonnegCont_holds : FrozenDiskGreenNonnegCont := by
  intro R hR
  refine ⟨fun x hx hx0 => ?_, ?_⟩
  · have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hxR : ‖x‖ < R := mem_ball_zero_iff.1 hx
    rw [frozenGreenBallCentre_holds R hR x hpos hxR]
    have h1 : 1 ≤ R / ‖x‖ := by
      rw [le_div_iff₀ hpos]
      linarith
    exact mul_nonneg (inv_nonneg.2 (by positivity)) (Real.log_nonneg h1)
  · exact (HarmonicBalls.continuousOn_greenFunction_ball (mem_ball_self hR)).mono fun x hx => hx.2

end MatedCRT
