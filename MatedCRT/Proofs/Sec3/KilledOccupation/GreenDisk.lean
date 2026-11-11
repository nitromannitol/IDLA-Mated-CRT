import Mathlib
import HarmonicBalls.Proofs.Potential.GreenBall
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable
import MatedCRT.Proofs.Sec3.KilledOccupation.Potential

/-!
# The Green function of a disc in the explicit form (GreenDisk)

Discharges the hypothesis `GreenDiskFormula z r` (paper eq:occ-green, tex:44-47; the Green function of the disc
`B_r(z)` of Armitage-Gardiner, Section 4.1, in the normalization `ΔG(·,x) = -δ_x`). The centred case
`G_{B_r(0)}(x,y) = (2π)⁻¹ log(|r² - x̄ y| / (r |x - y|))` is `HarmonicBalls.greenFunction_ball`; translation invariance
`G_{B_r(z)}(x,y) = G_{B_r(0)}(x - z, y - z)` is `HarmonicBalls.greenFunction_ball_translate`; the remaining step is the
rescaling identity `|1 - ā b| / |a - b| = |r² - conj(v - z) (x - z)| / (r |(v - z) - (x - z)|)` for
`a = (v - z)/r`, `b = (x - z)/r`.
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Metric Set Topology ComplexConjugate
open scoped ENNReal

/-- **The Green function of a disc** (paper eq:occ-green, tex:44-47): `GreenDiskFormula z r` holds for every centre
`z` and radius `r`. For `r ≤ 0` the ball is empty and the formula is vacuous. -/
theorem greenDiskFormula (z : ℂ) (r : ℝ) : GreenDiskFormula z r := by
  intro v hv x hx hvx
  rcases le_or_gt r 0 with hr | hr
  · exact absurd (dist_nonneg.trans_lt hv) (not_lt.2 hr)
  have hv0 : v - z ∈ ball (0 : ℂ) r := by simpa [mem_ball, dist_eq_norm] using hv
  have hx0 : x - z ∈ ball (0 : ℂ) r := by simpa [mem_ball, dist_eq_norm] using hx
  have hne : v - z ≠ x - z := fun h => hvx (sub_left_inj.1 h)
  rw [HarmonicBalls.greenFunction_ball_translate z v x r,
    HarmonicBalls.greenFunction_ball hv0 hx0 hne]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have key1 : (1 : ℂ) - conj ((v - z) / (r : ℂ)) * ((x - z) / (r : ℂ)) =
      ((r : ℂ) ^ 2 - conj (v - z) * (x - z)) / (r : ℂ) ^ 2 := by
    rw [map_div₀, Complex.conj_ofReal]
    field_simp
  have key2 : (v - z) / (r : ℂ) - (x - z) / (r : ℂ) = ((v - z) - (x - z)) / (r : ℂ) := by
    ring
  have hn1 : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hn2 : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  simp only [HarmonicBalls.greenBall, key1, key2, norm_div, hn1, hn2]
  congr 2
  field_simp

end MatedCRT.KilledOccupation
