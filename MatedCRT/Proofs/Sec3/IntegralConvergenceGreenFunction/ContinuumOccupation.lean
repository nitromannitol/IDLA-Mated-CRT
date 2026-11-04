import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.Truncation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Convergence of the continuum occupation integrals under domination. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology MarkovProcess _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Along each path, truncating after increasing integer times eventually
leaves the integral unchanged. -/
theorem lbm_path_occupation_eventually_eq
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (D : Set ℂ) (f : Ω → ℂ → ℝ) (ω : Ω) (b : ContinuousPath ℂ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ t in Ioc (0 : ℝ)
        (min (n : ℝ) (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
          f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) =
      (∫ t in Ioc (0 : ℝ)
        (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal,
          f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [min_eq_right (hN.le.trans hn')]

/-- Dominated convergence passes the pathwise stabilization through the
Brownian expectation. -/
theorem truncatedLBMOccupation_tendsto_of_dominated
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (D : Set ℂ) (y : ℂ) (f : Ω → ℂ → ℝ) (ω : Ω)
    (bound : ContinuousPath ℂ → ℝ)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun b =>
      ∫ t in Ioc (0 : ℝ)
        (min (n : ℝ) (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
          f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) (planarBrownianMotion y))
    (hint : Integrable bound (planarBrownianMotion y))
    (hbound : ∀ n : ℕ, ∀ᵐ b ∂planarBrownianMotion y,
      ‖∫ t in Ioc (0 : ℝ)
        (min (n : ℝ) (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
          f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)‖ ≤ bound b) :
    Tendsto (fun n : ℕ => truncatedLBMOccupation S D y f n ω) atTop
      (𝓝 (∫ b, (∫ t in Ioc (0 : ℝ)
        (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal,
          f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal) )
        ∂planarBrownianMotion y)) := by
  apply tendsto_integral_of_dominated_convergence bound hmeas hint hbound
  filter_upwards [] with b
  exact tendsto_const_nhds.congr' ((lbm_path_occupation_eventually_eq S D f ω b).mono fun _ h => h.symm)

/-- A bounded function integrated up to a truncated nonnegative exit time is
bounded by the exit time times its uniform bound. -/
theorem norm_truncated_time_integral_le (g : ℝ → ℝ) (τ M T : ℝ)
    (hτ : 0 ≤ τ) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hg : ∀ t ∈ Ioo (0 : ℝ) τ, ‖g t‖ ≤ M) :
    ‖∫ t in Ioc (0 : ℝ) (min T τ), g t‖ ≤ M * τ := by
  rw [integral_Ioc_eq_integral_Ioo]
  have hmin : 0 ≤ min T τ := le_min hT hτ
  have h := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Ioo (0 : ℝ) (min T τ))
    (f := g) (C := M) (by simp [Real.volume_Ioo])
    (fun t ht => hg t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩)
  have hvol : volume.real (Ioo (0 : ℝ) (min T τ)) = min T τ := by
    simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_min, hT, hτ]
  rw [hvol] at h
  exact h.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hM)

/-- At every strictly positive time below the real-valued exit time, a path
is inside its domain. -/
theorem path_mem_before_exit_toReal {α : Type} (D : Set α) (p : ℝ≥0 → α)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (pathExitTime D p).toReal) :
    p t.toNNReal ∈ D := by
  by_contra hout
  have hle : pathExitTime D p ≤ (t.toNNReal : ℝ≥0∞) := by
    apply sInf_le
    exact ⟨t.toNNReal, rfl, hout⟩
  have hreal := ENNReal.toReal_mono (by simp : (t.toNNReal : ℝ≥0∞) ≠ ⊤) hle
  simp only [ENNReal.coe_toReal, Real.coe_toNNReal' , max_eq_left ht.1.le] at hreal
  linarith [ht.2]

/-- Boundedness on the domain gives an exit-time envelope for every
truncated continuum occupation integral. -/
theorem norm_truncated_lbm_path_occupation_le
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (D : Set ℂ) (f : Ω → ℂ → ℝ) (ω : Ω) (b : ContinuousPath ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ x ∈ D, |f ω x| ≤ M) (n : ℕ) :
    ‖∫ t in Ioc (0 : ℝ)
        (min (n : ℝ) (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
          f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)‖ ≤
      M * (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal := by
  apply norm_truncated_time_integral_le _ _ _ _ ENNReal.toReal_nonneg hM (Nat.cast_nonneg n)
  intro t ht
  simpa only [Real.norm_eq_abs] using hf _
    (path_mem_before_exit_toReal D (rescaledLBMPath (S.clock ω) S.m₀ b) ht)

/-- Finite mean exit time and boundedness of the test function supply the
integrable envelope for the continuum occupation limit. -/
theorem truncatedLBMOccupation_tendsto_of_integrable_exit
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (D : Set ℂ) (y : ℂ) (f : Ω → ℂ → ℝ) (ω : Ω)
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ x ∈ D, |f ω x| ≤ M)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun b =>
      ∫ t in Ioc (0 : ℝ)
        (min (n : ℝ) (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
          f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) (planarBrownianMotion y))
    (hexit : Integrable (fun b =>
      (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal)
        (planarBrownianMotion y)) :
    Tendsto (fun n : ℕ => truncatedLBMOccupation S D y f n ω) atTop
      (𝓝 (∫ b, (∫ t in Ioc (0 : ℝ)
        (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal,
          f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal))
        ∂planarBrownianMotion y)) := by
  apply truncatedLBMOccupation_tendsto_of_dominated S D y f ω
    (fun b => M * (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal)
    hmeas (hexit.const_mul M)
  intro n
  exact Filter.Eventually.of_forall fun b =>
    norm_truncated_lbm_path_occupation_le S D f ω b M hM hf n

end MatedCRT
