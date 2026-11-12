import MatedCRT.FirstPass.Derived.ExitTimeIntegralBound

/-!
# From the truncated kernel to the logarithmic integral (BG20 (5.1), final comparison)

Berestycki-Gwynne (arXiv:2003.10320), proof of Proposition 5.1: the bound (5.45) on the expected exit
time, `K M + 6 ε⁻¹ ∫_{B_{ε^α₁}(D)} truncLogKernel dμ_h + ε^{-1+α₁}`, is at most a constant times
`ε⁻¹ ∫_{B_{ε^α}(D)} (log(1/|z-w|) + 1) dμ_h(w)` once `α ≤ α₁`, `K M ≤ ε^{-1+α}` and `μ_h(D) ≥ ε^α`.

* `measure_singleton_eq_zero_of_isAreaParametrized`: a measure for which some space-filling curve is
  an area parametrization has no atoms.
* `ofReal_integral_truncLogKernel_le`: the integral of the truncated kernel is at most `C` times the
  logarithmic integral (the pole carries no mass).
* `ofReal_exitBound_le_logIntegral`: the absorption of `K M + ε^{-1+α₁}` into the logarithmic
  integral, using that the integrand is at least `1 - log 2` on `D ⊆ B_1`.
-/

open HarmonicBalls

namespace MatedCRT

open Set Metric MeasureTheory Filter LatticeProb.TruncatedLog
open scoped ENNReal

namespace ExitTimeLogIntegral

/-- An area-parametrized space-filling curve leaves no atom: `μ {z} = 0` for every `z`. -/
theorem measure_singleton_eq_zero_of_isAreaParametrized {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) (z : ℂ) : μ {z} = 0 := by
  obtain ⟨t, rfl⟩ := h.2.2.1 z
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_) bot_le
  have hsub : ({η t} : Set ℂ) ⊆ η '' Icc t (t + δ) :=
    singleton_subset_iff.2 ⟨t, ⟨le_rfl, by simp⟩, rfl⟩
  calc μ {η t} ≤ μ (η '' Icc t (t + δ)) := measure_mono hsub
    _ = ENNReal.ofReal (t + δ - t) := h.2.2.2 t (t + δ) (by simpa using hδ)
    _ = 0 + δ := by simp

/-- Pointwise comparison off the pole: the truncated kernel is at most `C (log (1/|z-w|) + 1)`. -/
theorem ofReal_truncLogKernel_le {C L : ℝ} (hC : 0 ≤ C) {z w : ℂ} (hzw : w ≠ z) :
    ENNReal.ofReal (truncLogKernel C L z w) ≤
      ENNReal.ofReal C * ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) := by
  have hpos : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hzw))
  have h := truncLogKernel_le_of_pos (M := L) hC hpos
  rw [← ENNReal.ofReal_mul hC, ENNReal.ofReal_le_ofReal_iff', one_div]
  rcases le_total 0 (C * Real.log ‖z - w‖⁻¹ + C) with h0 | h0
  · left
    rw [max_eq_right h0] at h
    linarith
  · right
    rw [max_eq_left h0] at h
    exact h

/-- The integral of the truncated kernel over a set `s` is at most `C` times the logarithmic integral,
provided the pole carries no mass. -/
theorem ofReal_integral_truncLogKernel_le {μ : Measure ℂ} {C L : ℝ} (hC : 0 ≤ C) {z : ℂ}
    (hz : μ {z} = 0) (s : Set ℂ) :
    ENNReal.ofReal (∫ w in s, truncLogKernel C L z w ∂μ) ≤
      ENNReal.ofReal C * ∫⁻ w in s, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ := by
  have h1 : ENNReal.ofReal (∫ w in s, truncLogKernel C L z w ∂μ) ≤
      ∫⁻ w in s, ENNReal.ofReal (truncLogKernel C L z w) ∂μ := by
    refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun w => ?_
    rw [Real.enorm_eq_ofReal (truncLogKernel_nonneg C L z w)]
  refine h1.trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  have hae : ∀ᵐ w ∂μ, w ≠ z := compl_mem_ae_iff.2 hz
  filter_upwards [ae_restrict_of_ae hae] with w hw
  exact ofReal_truncLogKernel_le hC hw

/-- On `D ⊆ B_1`, the logarithmic integral over any superset of `D` is at least `(1 - log 2) μ(D)`
from any pole `z ∈ D`. -/
theorem ofReal_mul_measure_le_logIntegral {μ : Measure ℂ} {D s : Set ℂ} (hDs : D ⊆ s)
    (hD1 : D ⊆ ball 0 1) {z : ℂ} (hz : z ∈ D) :
    ENNReal.ofReal (1 - Real.log 2) * μ D ≤
      ∫⁻ w in s, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ := by
  rw [← setLIntegral_const]
  have hmeas : Measurable fun w : ℂ => ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) := by
    fun_prop
  refine (setLIntegral_mono hmeas fun w hw => ?_).trans (lintegral_mono_set hDs)
  refine ENNReal.ofReal_le_ofReal ?_
  have hz1 := mem_ball_zero_iff.1 (hD1 hz)
  have hw1 := mem_ball_zero_iff.1 (hD1 hw)
  have h2 : ‖z - w‖ ≤ 2 := by linarith [norm_sub_le z w]
  have hlog : Real.log ‖z - w‖ ≤ Real.log 2 := by
    rcases (norm_nonneg (z - w)).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg one_le_two
    · exact Real.log_le_log h0 h2
  rw [one_div, Real.log_inv]
  linarith

/-- BG20 (5.45) implies (5.1) for one starting point: if `α ≤ α₁`, `K M ≤ ε^{-1+α}` and
`μ(D) ≥ ε^α` for `D ⊆ B_1` with a pole `z ∈ D` of zero mass, then
`K M + 6 ε⁻¹ ∫_{B_{ε^α₁}(D)} truncLogKernel C L z dμ + ε^{-1+α₁}` is at most
`(2 (1 - log 2)⁻¹ + 6 C) ε⁻¹ ∫_{B_{ε^α}(D)} (log (1/|z-w|) + 1) dμ(w)`. -/
theorem ofReal_exitBound_le_logIntegral {μ : Measure ℂ} {C L K M ε α α₁ : ℝ} {D : Set ℂ} {z : ℂ}
    (hC : 0 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1) (hαα₁ : α ≤ α₁) (hKM : K * M ≤ ε ^ (-1 + α))
    (hD1 : D ⊆ ball 0 1) (hz : z ∈ D) (hz0 : μ {z} = 0) (hμD : ENNReal.ofReal (ε ^ α) ≤ μ D) :
    ENNReal.ofReal (K * M + (6 * ε⁻¹ * ∫ x in thickening (ε ^ α₁) D, truncLogKernel C L z x ∂μ +
        ε ^ (-1 + α₁))) ≤
      ENNReal.ofReal ((2 * (1 - Real.log 2)⁻¹ + 6 * C) * ε⁻¹) *
        ∫⁻ w in thickening (ε ^ α) D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ := by
  set I := ∫⁻ w in thickening (ε ^ α) D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ
  set X := ∫ x in thickening (ε ^ α₁) D, truncLogKernel C L z x ∂μ
  have hX0 : 0 ≤ X := integral_nonneg fun x => truncLogKernel_nonneg C L z x
  have hpow : ε ^ (-1 + α₁) ≤ ε ^ (-1 + α) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hpowα : ε ^ α₁ ≤ ε ^ α := Real.rpow_le_rpow_of_exponent_ge hε hε1 hαα₁
  have hsplit : ε ^ (-1 + α) = ε⁻¹ * ε ^ α := by rw [Real.rpow_add hε, Real.rpow_neg_one]
  have hlog2 : 0 < 1 - Real.log 2 := by have := Real.log_two_lt_d9; linarith
  have hεi : 0 ≤ ε⁻¹ := inv_nonneg.2 hε.le
  have hεα : 0 ≤ ε ^ α := Real.rpow_nonneg hε.le α
  have ha : 0 ≤ 2 * (1 - Real.log 2)⁻¹ * ε⁻¹ := by positivity
  -- the logarithmic integral dominates `(1 - log 2) ε^α`
  have hlow : ENNReal.ofReal (1 - Real.log 2) * ENNReal.ofReal (ε ^ α) ≤ I :=
    (mul_le_mul' le_rfl hμD).trans
      (ofReal_mul_measure_le_logIntegral (self_subset_thickening (by positivity) D) hD1 hz)
  -- the truncated-kernel integral is dominated by `C I`
  have hX : ENNReal.ofReal X ≤ ENNReal.ofReal C * I :=
    (ofReal_integral_truncLogKernel_le hC hz0 _).trans
      (mul_le_mul' le_rfl (lintegral_mono_set (thickening_mono hpowα D)))
  have hfirst : ENNReal.ofReal (2 * ε ^ (-1 + α)) =
      ENNReal.ofReal (2 * (1 - Real.log 2)⁻¹ * ε⁻¹) *
        (ENNReal.ofReal (1 - Real.log 2) * ENNReal.ofReal (ε ^ α)) := by
    rw [← ENNReal.ofReal_mul hlog2.le, ← ENNReal.ofReal_mul ha, hsplit]
    congr 1
    field_simp
  calc ENNReal.ofReal (K * M + (6 * ε⁻¹ * X + ε ^ (-1 + α₁)))
      ≤ ENNReal.ofReal (2 * ε ^ (-1 + α) + 6 * ε⁻¹ * X) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (2 * ε ^ (-1 + α)) + ENNReal.ofReal (6 * ε⁻¹) * ENNReal.ofReal X := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (2 * (1 - Real.log 2)⁻¹ * ε⁻¹) * I +
          ENNReal.ofReal (6 * ε⁻¹) * (ENNReal.ofReal C * I) := by
        rw [hfirst]
        gcongr
    _ = ENNReal.ofReal ((2 * (1 - Real.log 2)⁻¹ + 6 * C) * ε⁻¹) * I := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← add_mul,
          ← ENNReal.ofReal_add ha (by positivity)]
        congr 2
        ring

end ExitTimeLogIntegral

end MatedCRT
