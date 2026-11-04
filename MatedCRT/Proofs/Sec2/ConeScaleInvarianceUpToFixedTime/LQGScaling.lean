import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime

/-!
# The LQG measure of the rescaled cone field (Fact 2.2 III, IV)

`ConeLQGScalingStep` from Fact 2.2 (`LQGMeasurePropertiesStmt`, IV at `a = R_b`, `w = 0`) and the positivity of `R_b`
(`ConeScaleRadiusPosStep`): the Weyl scaling by the constant `-γ⁻¹ log b` is deterministic (`isLQGLimit_add_const`:
adding a constant `κ` to the circle averages multiplies the approximations `lqgApprox` by `e^{γκ}`).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- **Weyl scaling by a constant** (deterministic): if `ν` is the LQG measure (circle average limit) of `c`, then
`e^{γκ} ν` is that of `c + κ`. -/
theorem isLQGLimit_add_const {γ : ℝ} {c : ℝ → ℂ → ℝ} {ν : Measure ℂ} (h : IsLQGLimit γ c ν) (κ : ℝ) :
    IsLQGLimit γ (fun r z => c r z + κ) (ENNReal.ofReal (Real.exp (γ * κ)) • ν) := by
  have happrox : ∀ ε, lqgApprox γ (fun r z => c r z + κ) ε =
      ENNReal.ofReal (Real.exp (γ * κ)) • lqgApprox γ c ε := by
    intro ε
    unfold lqgApprox
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [mul_add, Real.exp_add]
    ring
  obtain ⟨hlf, htend⟩ := h
  refine ⟨⟨fun x => ?_⟩, fun f hf hfc => ?_⟩
  · obtain ⟨s, hs, hfin⟩ := hlf.finiteAtNhds x
    refine ⟨s, hs, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  · simp_rw [happrox, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    exact (htend f hf hfc).const_mul _

/-- **`ConeLQGScalingStep` from Fact 2.2 and `R_b > 0`.** -/
theorem coneLQGScalingStep_of_steps (h22 : LQGMeasurePropertiesStmt) (hpos : ConeScaleRadiusPosStep) :
    ConeLQGScalingStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone b hb
  obtain ⟨-, -, -, hIV⟩ := h22 γ hγ0 hγ2 Ω P hC hcirc μ hcone
  filter_upwards [hIV, hpos γ hγ0 hγ2 Ω P hC hcirc hcone.1 hcone.2.1 b hb] with ω hω hR
  refine ⟨hR, ?_⟩
  set R := coneScaleRadius γ (hcirc ω) b with hRdef
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have h1 := isLQGLimit_add_const (hω (R : ℂ) 0 hRc) (-(γ⁻¹ * Real.log b))
  have hc : (fun r z => hcirc ω (‖(R : ℂ)‖ * r) ((R : ℂ) * z + 0) + lqgQ γ * Real.log ‖(R : ℂ)‖ +
      -(γ⁻¹ * Real.log b)) = rescaledCircle γ (hcirc ω) R b := by
    funext r z
    show _ = hcirc ω (R * r) ((R : ℂ) * z) + lqgQ γ * Real.log R - γ⁻¹ * Real.log b
    rw [Complex.norm_real, Real.norm_of_nonneg hR.le, add_zero]
    ring
  have hm : ENNReal.ofReal (Real.exp (γ * -(γ⁻¹ * Real.log b))) •
      (μ ω).map (fun x => (R : ℂ)⁻¹ * (x - 0)) = rescaledMeasure (μ ω) R b := by
    rw [mul_neg, mul_inv_cancel_left₀ hγ0.ne', Real.exp_neg, Real.exp_log hb, rescaledMeasure]
    simp only [sub_zero]
  exact (congrArg₂ (IsLQGLimit γ) hc hm).mp h1

end MatedCRT
