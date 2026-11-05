import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ContinuumOccupation
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit
import MatedCRT.Proofs.LBM.ExitTimeChange

/-!
# Lemma 3.4: identification of the continuum occupation integral

The rescaled LBM is `X_t = LBM_{m₀ t}`; its exit time is `τ/m₀` and its occupation integral
is `m₀⁻¹` times that of LBM. By the Revuz identity (`LBMGreenOccupationStep`, IR-m2-1) the
latter is `2 ∫ G f dμ_h`, so the occupation integral of `X` is `c₀ ∫ G f dμ_h`, `c₀ = 2/m₀`
(CORRECTION [C1], line 1172).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- A linear time change `t ↦ c t` divides the occupation integral up to the exit time by `c`. -/
theorem occupation_linear_time_change {U : Set ℂ} (hU : IsOpen U) (p : ContinuousPath ℂ)
    (h0 : p 0 ∈ U) (hfin : ContinuousPath.exitTime U p < ⊤) {c : ℝ} (hc : 0 < c)
    (g : ℂ → ℝ) :
    ∫ t in Ioc (0 : ℝ) (pathExitTime U (fun t => p (c.toNNReal * t))).toReal,
        g (p (c.toNNReal * t.toNNReal)) =
      c⁻¹ * ∫ s in Ioo (0 : ℝ) (ContinuousPath.exitTime U p).toReal, g (p s.toNNReal) := by
  rw [pathExitTime_mul_eq hU p h0 hfin (Real.toNNReal_pos.2 hc), ENNReal.coe_toReal,
    NNReal.coe_div, Real.coe_toNNReal _ hc.le]
  set τ : ℝ := ((ContinuousPath.exitTime U p).toNNReal : ℝ) with hτ
  have hτ' : (ContinuousPath.exitTime U p).toReal = τ := rfl
  rw [hτ']
  have hτ0 : 0 ≤ τ := NNReal.coe_nonneg _
  set h : ℝ → ℝ := fun s => g (p s.toNNReal) with hh
  have hcongr : ∫ t in Ioc (0 : ℝ) (τ / c), g (p (c.toNNReal * t.toNNReal)) =
      ∫ t in Ioc (0 : ℝ) (τ / c), h (c * t) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    change g (p (c.toNNReal * t.toNNReal)) = g (p (c * t).toNNReal)
    rw [Real.toNNReal_mul hc.le]
  rw [hcongr, ← intervalIntegral.integral_of_le (div_nonneg hτ0 hc.le),
    intervalIntegral.integral_comp_mul_left h hc.ne', mul_zero, mul_div_cancel₀ _ hc.ne',
    intervalIntegral.integral_of_le hτ0, integral_Ioc_eq_integral_Ioo, smul_eq_mul]

/-- **Identification of the continuum limit** via the Revuz identity. -/
theorem MatedCRTEnv.IsValid.ae_integral_rescaled_occupation_eq {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hS : S.IsValid 𝒮 γ) (hrevuz : LBMGreenOccupationStep 𝒮) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) (f : Ω → ℂ → ℝ) (hfbound : ∀ ω, ∃ M : ℝ, ∀ x ∈ ball z r, |f ω x| ≤ M)
    (hfcont : ∀ ω, IsHolderContinuousOn (f ω) (ball z r)) :
    ∀ᵐ ω ∂S.P, ∫ b, (∫ t in Ioc (0 : ℝ)
        (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal,
          f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) ∂planarBrownianMotion y =
      S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂S.μ ω := by
  have hm := hS.m₀_pos hγ hγ2
  filter_upwards [hrevuz γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy, hS.isLQGClock]
    with ω hω hcω
  obtain ⟨hfin, hid⟩ := hω
  have key : ∀ᵐ b ∂planarBrownianMotion y,
      (∫ t in Ioc (0 : ℝ) (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal,
        f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) =
      S.m₀⁻¹ * ∫ s in Ioo (0 : ℝ) (lbmExitTime (S.clock ω) (ball z r) b).toReal,
        f ω (liouvilleBrownianPath (S.clock ω) b s.toNNReal) := by
    filter_upwards [(hcω y).2, hfin, ae_planarBrownianMotion_eval_zero y]
      with b hclock hfinb hstart
    have hI : clockInverse (S.clock ω b) 0 = 0 := by
      have h := clockInverse_clockValue hclock.map_zero hclock.strictMono 0
      simpa only [hclock.map_zero, Real.toNNReal_zero] using h
    have h0 : liouvilleBrownianPath (S.clock ω) b 0 ∈ ball z r := by
      simpa only [liouvilleBrownianPath, hI, hstart] using hy
    exact occupation_linear_time_change isOpen_ball
      ⟨liouvilleBrownianPath (S.clock ω) b, continuous_liouvilleBrownianPath hclock⟩ h0 hfinb
      hm (f ω)
  rw [integral_congr_ae key, integral_const_mul]
  change S.m₀⁻¹ * lbmOccupationIntegral (S.clock ω) (ball z r) y (f ω) = _
  rw [hid (f ω) (hfbound ω) (hfcont ω), MatedCRTEnv.c₀]
  field_simp

end MatedCRT
