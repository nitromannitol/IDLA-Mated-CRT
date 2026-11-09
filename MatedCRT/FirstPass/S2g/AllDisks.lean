import MatedCRT.FirstPass.S2g.GoodSet
import MatedCRT.FirstPass.Frozen.S2g

/-! # All-disks obstacle clause from the radius-3/4 clause (fp-S2g, q1; CHATGPT-q1-open-steps.md H7)

Deterministic part of `ConeCanonicalHalfBallStep`. For a measure `μ`, a time `t > 0` and `A = Λ_t` (open, containing the
pole `0`, contained in `B_{1/2}`), the least supersolution `W = leastSupersolution μ (3/4) 0 t` at radius `3/4` determines
the least supersolutions at every radius `ρ > r` with `A ⊆ B_r`: the candidate `allDisksCandidate W t ρ` is `W + c` on
`B_{3/4}` (with `c` the constant `t G_{B_{3/4}}(0,·) - t G_{B_ρ}(0,·)`, which is constant by the centre formula
`FrozenGreenBallCentre`) and `-t G_{B_ρ}(0,·)` off `B_{3/4}`. The pole cancels in the centre formula. Written argument:
`notes/fp-gaps/CHATGPT-q1-open-steps.md` Section 3 H7; least-ness is `certificate_le_supersolution` (GoodSet.lean). -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

open Classical in
/-- The H7 candidate at radius `ρ` built from `W`: `W + t (2π)⁻¹ log (3/(4ρ))` on `B_{3/4}` and `-t G_{B_ρ}(0,·)` off
`B_{3/4}`. -/
noncomputable def allDisksCandidate (W : ℂ → ℝ) (t ρ : ℝ) : ℂ → ℝ :=
  fun x => if x ∈ ball (0 : ℂ) (3 / 4) then W x + t * ((2 * Real.pi)⁻¹ * Real.log (3 / (4 * ρ)))
    else -t * greenFunction (ball (0 : ℂ) ρ) 0 x

/-- On `B_{3/4} ∩ B_ρ` minus the pole, the candidate is `W + t G_{B_{3/4}}(0,·) - t G_{B_ρ}(0,·)` (pole-free form). -/
theorem allDisksCandidate_eq_of_centre (hC : FrozenGreenBallCentre) {W : ℂ → ℝ} {t ρ : ℝ} (hρ : 0 < ρ)
    {x : ℂ} (hx3 : x ∈ ball (0 : ℂ) (3 / 4)) (hxρ : x ∈ ball (0 : ℂ) ρ) (hx0 : x ≠ 0) :
    allDisksCandidate W t ρ x =
      W x + t * greenFunction (ball (0 : ℂ) (3 / 4)) 0 x - t * greenFunction (ball (0 : ℂ) ρ) 0 x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h3 : ‖x‖ < 3 / 4 := mem_ball_zero_iff.mp hx3
  have hr : ‖x‖ < ρ := mem_ball_zero_iff.mp hxρ
  have h1 : (3 / 4 : ℝ) / ‖x‖ ≠ 0 := (div_pos (by norm_num) hn).ne'
  have h2 : ρ / ‖x‖ ≠ 0 := (div_pos hρ hn).ne'
  have hlog : Real.log (3 / (4 * ρ)) = Real.log ((3 / 4 : ℝ) / ‖x‖) - Real.log (ρ / ‖x‖) := by
    rw [← Real.log_div h1 h2]
    congr 1
    field_simp
  unfold allDisksCandidate
  simp only [hx3, ↓reduceIte]
  rw [hC (3 / 4) (by norm_num) x hn h3, hC ρ hρ x hn hr, hlog]
  ring

end MatedCRT
