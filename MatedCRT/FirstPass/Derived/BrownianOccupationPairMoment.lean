import MatedCRT.FirstPass.Derived.BrownianOccupationPairExpBound
import LatticeProb.Analysis.ExpDampedRieszKernelQuadrant

/-!
# The two-point small-ball moment of the killed Brownian occupation measure

For planar Brownian motion started at `y` and killed on exiting `B_r(z)`, and `0 < θ ≤ 1`, there is a constant
`C` (depending on `r` and `θ` only) such that for every `a ≥ 0`
`E_y[(du|_{[0,τ]} ⊗ du|_{[0,τ]}) {(u, v) : |b_u - b_v| < a}] ≤ C a^{2(1-θ)}`.
This completes the exponential form `lintegral_occupation_prod_norm_sub_lt_le_exp`: the remaining time integral
`∫∫_{u,v ≥ 0} e^{-c max(u, v)} |u - v|^{θ - 1} du dv` is finite (the exponentially damped Riesz kernel on the
quadrant, `LatticeProb.Analysis.lintegral_exp_neg_max_mul_abs_sub_rpow_lt_top`), transported from
`volume|_{[0,∞)}` to Lebesgue measure `lebNN` on `ℝ≥0`.

## Main results

* `lintegral_lebNN_prod_exp_neg_max_mul_abs_sub_rpow_lt_top`: the damped Riesz kernel integral over
  `lebNN ⊗ lebNN` is finite.
* `exists_lintegral_occupation_prod_norm_sub_lt_le`: the moment bound `≤ C a^{2(1-θ)}` with `C ≥ 0`.
-/

open MeasureTheory Set Metric MarkovProcess ProbabilityTheory HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The exponentially damped Riesz kernel `e^{-c max(u, v)} |u - v|^{θ - 1}` has finite integral for
`lebNN ⊗ lebNN`, for `c > 0` and `0 < θ ≤ 1`. -/
theorem lintegral_lebNN_prod_exp_neg_max_mul_abs_sub_rpow_lt_top {c θ : ℝ} (hc : 0 < c) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) :
    ∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal (Real.exp (-c * max (p.1 : ℝ) p.2) * |(p.1 : ℝ) - p.2| ^ (θ - 1))
      ∂(lebNN.prod lebNN) < ∞ := by
  set μ : Measure ℝ := volume.restrict (Ici (0 : ℝ)) with hμ
  have hprod : lebNN.prod lebNN = (μ.prod μ).map (Prod.map Real.toNNReal Real.toNNReal) := by
    rw [lebNN, Measure.map_prod_map μ μ measurable_real_toNNReal measurable_real_toNNReal]
  have hmapm : Measurable (Prod.map Real.toNNReal Real.toNNReal) :=
    measurable_real_toNNReal.prodMap measurable_real_toNNReal
  rw [hprod]
  refine (lintegral_map_le _ hmapm.aemeasurable).trans_lt ?_
  refine lt_of_le_of_lt (le_of_eq ?_) (LatticeProb.Analysis.lintegral_exp_neg_max_mul_abs_sub_rpow_lt_top hc hθ0 hθ1)
  refine lintegral_congr_ae ?_
  have hres : μ.prod μ = (volume.prod volume).restrict (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)) := by
    rw [hμ, Measure.prod_restrict]
  rw [hres]
  filter_upwards [ae_restrict_mem (measurableSet_Ici.prod measurableSet_Ici)] with x hx
  simp only [Prod.map, Real.coe_toNNReal _ hx.1, Real.coe_toNNReal _ hx.2]

/-- **Two-point small-ball moment of the killed occupation measure.** For `0 < θ ≤ 1` there is `C ≥ 0`
(depending on `r` and `θ`) with
`E_y[(du|_{[0,τ]} ⊗ du|_{[0,τ]}) {(u, v) : |b_u - b_v| < a}] ≤ C a^{2(1-θ)}` for every `a ≥ 0`, where `τ` is the
exit time of `B_r(z)`. -/
theorem exists_lintegral_occupation_prod_norm_sub_lt_le (z y : ℂ) (r : ℝ) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      ∫⁻ b, ((lebNN.restrict (Icc 0 (exitNN z r b))).prod (lebNN.restrict (Icc 0 (exitNN z r b))))
          {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < a} ∂planarBrownianMotion y ≤
        ENNReal.ofReal (C * a ^ (2 * (1 - θ))) := by
  set L : ℝ≥0∞ := ∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal (Real.exp (-stayDecay r θ * max (p.1 : ℝ) p.2) *
    |(p.1 : ℝ) - p.2| ^ (θ - 1)) ∂(lebNN.prod lebNN)
  have hLt : L ≠ ∞ :=
    (lintegral_lebNN_prod_exp_neg_max_mul_abs_sub_rpow_lt_top (stayDecay_pos r hθ0) hθ0 hθ1).ne
  refine ⟨stayConst r θ * L.toReal, mul_nonneg (stayConst_pos r θ).le ENNReal.toReal_nonneg, fun a ha => ?_⟩
  refine (lintegral_occupation_prod_norm_sub_lt_le_exp z y r hθ0 hθ1 ha).trans (le_of_eq ?_)
  show ENNReal.ofReal (stayConst r θ * a ^ (2 * (1 - θ))) * L =
    ENNReal.ofReal (stayConst r θ * L.toReal * a ^ (2 * (1 - θ)))
  conv_lhs => rw [← ENNReal.ofReal_toReal hLt]
  rw [← ENNReal.ofReal_mul (mul_nonneg (stayConst_pos r θ).le (Real.rpow_nonneg ha _))]
  congr 1
  ring

end MatedCRT.KilledOccupation
