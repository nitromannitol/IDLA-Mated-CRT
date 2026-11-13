import HarmonicBalls.Proofs.Sec11.FixedSquareFrontierNull
import LatticeProb.Analysis.CircleLogIntegrals

/-!
# First moment of the dyadic density of `h^ℂ - γ log |·|` away from the origin

For a whole-plane GFF `h^ℂ` normalized by `h^ℂ_1(0) = 0` and the field `h = h^ℂ - γ log |·|`, the circle average is
`h_ε(x) = h^ℂ_ε(x) - γ log max(ε, |x|)` (mean value property of `log |·|`), so `h_ε(x) ≤ h^ℂ_ε(x) - γ log |x|` for
`γ ≥ 0`. Together with the Gaussian first-moment bound `E[ε^{γ²/2} e^{γ h^ℂ_ε(x)}] ≤ (R + 1)^{γ²}` for `|x| ≤ R`,
`ε ≤ 1` (`HarmonicBalls.IsWholePlaneGFF.lintegral_density_le`) this gives
`E[ε^{γ²/2} e^{γ h_ε(x)}] ≤ (R + 1)^{γ²} |x|^{-γ²}`, uniformly in `ε ∈ (0, 1]`.

This is the first-moment input for the finiteness of the Green-weighted chaos measure near a pole `y ≠ 0`
(Berestycki 2017, the expected mass of the circle-average approximations).
-/

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The circle average of `log |·|` over `∂B_ε(x)` is at least `log |x|`, for `ε > 0` and `x ≠ 0`
(it equals `log max(ε, |x|)`). -/
lemma log_norm_le_circleAverage_log_norm {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx0 : x ≠ 0) :
    Real.log ‖x‖ ≤ Real.circleAverage (fun w => Real.log ‖w‖) x ε := by
  have h := LatticeProb.CircleLogIntegrals.circleAverage_log_norm_eq x 0 hε
  simp only [sub_zero] at h
  rw [h]
  have hpos : Real.log (ε⁻¹ * ‖x‖) ≤ Real.posLog (ε⁻¹ * ‖x‖) := le_max_right _ _
  rw [Real.log_mul (inv_ne_zero hε.ne') (norm_ne_zero_iff.2 hx0), Real.log_inv] at hpos
  linarith

/-- The circle average of the field `h = h^ℂ - γ log |·|` is at most `h^ℂ_ε(x) - γ log |x|`, for `γ ≥ 0`. -/
lemma fieldCircleAverage_le {γ : ℝ} (hγ : 0 ≤ γ) (hc : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) {x : ℂ}
    (hx0 : x ≠ 0) :
    fieldCircleAverage γ hc ε x ≤ hc ε x - γ * Real.log ‖x‖ := by
  have hA := log_norm_le_circleAverage_log_norm hε hx0
  have h := mul_le_mul_of_nonneg_left hA hγ
  unfold fieldCircleAverage
  linarith

/-- Pointwise comparison of the dyadic densities: `ε^{γ²/2} e^{γ h_ε(x)} ≤ ε^{γ²/2} e^{γ h^ℂ_ε(x)} · |x|^{-γ²}` for the
field `h = h^ℂ - γ log |·|`, `γ ≥ 0`, `x ≠ 0`. -/
lemma density_fieldCircleAverage_le {γ : ℝ} (hγ : 0 ≤ γ) (hc : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) {x : ℂ}
    (hx0 : x ≠ 0) :
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage γ hc ε x) ≤
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * hc ε x) * ‖x‖ ^ (-γ ^ 2) := by
  have hle := mul_le_mul_of_nonneg_left (fieldCircleAverage_le hγ hc hε hx0) hγ
  have hexp : Real.exp (γ * fieldCircleAverage γ hc ε x) ≤
      Real.exp (γ * hc ε x) * ‖x‖ ^ (-γ ^ 2) := by
    rw [Real.rpow_def_of_pos (norm_pos_iff.2 hx0), ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [hle])
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hε.le _)

/-- **First moment of the dyadic density of `h^ℂ - γ log |·|`.** For a whole-plane GFF `h^ℂ`, `γ ≥ 0`,
`0 < ε ≤ 1` and `0 < |x| ≤ R`: `E[ε^{γ²/2} e^{γ h_ε(x)}] ≤ (R + 1)^{γ²} |x|^{-γ²}`, where `h_ε(x)` is the circle
average of `h = h^ℂ - γ log |·|`. -/
theorem lintegral_density_fieldCircleAverage_le {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    {γ : ℝ} (hγ : 0 ≤ γ) {R : ℝ} (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x : ℂ} (hx0 : x ≠ 0)
    (hxR : ‖x‖ ≤ R) :
    ∫⁻ ω', ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage γ (hc ω') ε x)) ∂P' ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1)) * ‖x‖ ^ (-γ ^ 2)) := by
  have hc0 : 0 ≤ ‖x‖ ^ (-γ ^ 2) := Real.rpow_nonneg (norm_nonneg _) _
  have hpt : ∀ ω', ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage γ (hc ω') ε x)) ≤
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hc ω' ε x)) * ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) := by
    intro ω'
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (density_fieldCircleAverage_le hγ (hc ω') hε hx0)
  calc ∫⁻ ω', ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage γ (hc ω') ε x)) ∂P'
      ≤ ∫⁻ ω', ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hc ω' ε x)) *
          ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂P' := lintegral_mono hpt
    _ = (∫⁻ ω', ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hc ω' ε x)) ∂P') *
          ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) := by
          gcongr
          exact hG.lintegral_density_le γ hR hε hε1 hxR
    _ = ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1)) * ‖x‖ ^ (-γ ^ 2)) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

end MatedCRT.KilledOccupation
