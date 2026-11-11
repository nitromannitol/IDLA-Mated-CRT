import HarmonicBalls.Proofs.Potential.GreenPositivity

/-!
# FIRST PASS, Lemma 5.3: logarithmic lower bound of the disk Green function near the pole

`G_{B_ρ}(0, x) ≥ (2π)⁻¹ log((ρ/2)/|x|)` for `0 < |x| < ρ/2`. This is `log_div_le_greenFunction` (Harmonic-Balls
Green positivity, normalization `Δ G = -δ`) applied with the pole `0` as the first argument and the point `x` as the
centre of the comparison disk `closedBall x (ρ/2) ⊆ B_ρ`. No symmetry of the Green function is needed.
-/

namespace MatedCRT.S5c

open Metric Set
open scoped Real
open _root_.HarmonicBalls

/-- **Logarithmic lower bound** (G-5-3 Section 1, the blow-up `R_n(0) → ∞` through the circle averages). -/
lemma greenFunction_ball_zero_ge_log {ρ r : ℝ} (hr : 0 < r) (hrρ : r < ρ / 2)
    {x : ℂ} (hx : x ∈ sphere (0 : ℂ) r) :
    (2 * π)⁻¹ * Real.log (ρ / 2 / r) ≤ greenFunction (ball 0 ρ) 0 x := by
  have hxn : ‖x‖ = r := by simpa using hx
  have hsub : closedBall x (ρ / 2) ⊆ ball (0 : ℂ) ρ := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball_zero_iff]
    have h2 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      have := norm_add_le (y - x) x
      simpa using this
    linarith
  have hd : ‖(0 : ℂ) - x‖ = r := by simpa using hxn
  have hlog := log_div_le_greenFunction (O := ball 0 ρ) isBounded_ball (x := (0 : ℂ)) (y := x)
    (r := ρ / 2) (by linarith) hsub (by rw [hd]; exact hr) (by rw [hd]; exact hrρ)
  rw [hd] at hlog
  exact hlog

end MatedCRT.S5c
