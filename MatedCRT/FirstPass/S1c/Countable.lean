import MatedCRT.FirstPass.S1c.Moments

/-!
# The supersolution inequality from a countable family (Lemma 1 analytic layer)

If the pairings of a continuous extension `extendCM g` of `g ∈ C(B̄_R)` with the countable family `φs k` satisfy
`∫ w Δφs k ≤ ∫ φs k dν` for every `k`, then `extendCM g` satisfies `LaplacianLE` on `B_R` against `ν`: an arbitrary
nonnegative test function is approximated within `δ` on `B̄_R` by a member of the family, and both pairings change
by at most `δ` times a constant (the volume of `B̄_R` times `‖g‖`, resp. the mass `ν(B̄_R)`). Classical; no paper input.
-/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory HarmonicBalls

variable {R : ℝ}

theorem laplacianLE_extend_of_countable (hR : 0 ≤ R) (ν : Measure ℂ) (hν : ν (closedBall (0 : ℂ) R) < ⊤)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (g : C(closedBall (0 : ℂ) R, ℝ))
    (hk : ∀ k, ∫ x, extendCM R hR g x * Laplacian.laplacian (φs k) x ≤ ∫ x, φs k x ∂ν) :
    LaplacianLE (extendCM R hR g) ν (ball (0 : ℂ) R) := by
  refine ⟨((continuous_extendCM hR g).locallyIntegrable).locallyIntegrableOn _, ?_⟩
  intro φ hφ hφ0 hφint
  have hM0 : 0 ≤ ‖g‖ := norm_nonneg g
  have hV0 : 0 ≤ (volume (closedBall (0 : ℂ) R)).toReal := ENNReal.toReal_nonneg
  have hC20 : 0 ≤ (ν (closedBall (0 : ℂ) R)).toReal := ENNReal.toReal_nonneg
  set C1 : ℝ := ‖g‖ * (volume (closedBall (0 : ℂ) R)).toReal with hC1
  set C2 : ℝ := (ν (closedBall (0 : ℂ) R)).toReal with hC2
  have hC10 : 0 ≤ C1 := mul_nonneg hM0 hV0
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := ε / (C1 + C2 + 1) with hδdef
  have hpos : 0 < C1 + C2 + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hpos
  have hδsum : δ * C1 + δ * C2 ≤ ε := by
    have h1 : δ * (C1 + C2) ≤ ε := by
      rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith
    calc δ * C1 + δ * C2 = δ * (C1 + C2) := by ring
      _ ≤ ε := h1
  obtain ⟨k, hk'⟩ := hdense φ ⟨hφ, hφ0⟩ δ hδ
  have hφk : IsTestFunction (ball (0 : ℂ) R) (φs k) := (hφs k).1
  have hφ_out : ∀ x, x ∉ closedBall (0 : ℂ) R → φ x = 0 := fun x hx =>
    eq_zero_of_not_mem_tsupport_fn hφ.2.2 (fun h => hx (ball_subset_closedBall h))
  have hφk_out : ∀ x, x ∉ closedBall (0 : ℂ) R → φs k x = 0 := fun x hx =>
    eq_zero_of_not_mem_tsupport_fn hφk.2.2 (fun h => hx (ball_subset_closedBall h))
  -- integrability
  have hI1 := integrable_mul_laplacian (w := extendCM R hR g) (continuous_extendCM hR g) hφ
  have hI2 := integrable_mul_laplacian (w := extendCM R hR g) (continuous_extendCM hR g) hφk
  have hνk : Integrable (φs k) ν :=
    integrable_of_continuous_of_support hν (contDiff_two_of_isTestFunction hφk).continuous hφk_out
  -- the Lebesgue pairing changes by at most `δ C1`
  have hE1 : (∫ x, extendCM R hR g x * Laplacian.laplacian φ x) -
      (∫ x, extendCM R hR g x * Laplacian.laplacian (φs k) x) ≤ δ * C1 := by
    have hsub1 : ∫ x, (extendCM R hR g x * Laplacian.laplacian φ x -
        extendCM R hR g x * Laplacian.laplacian (φs k) x) =
        (∫ x, extendCM R hR g x * Laplacian.laplacian φ x) -
          (∫ x, extendCM R hR g x * Laplacian.laplacian (φs k) x) :=
      integral_sub hI1 hI2
    have hbd : ∀ x, ‖extendCM R hR g x * Laplacian.laplacian φ x -
        extendCM R hR g x * Laplacian.laplacian (φs k) x‖ ≤
          indicator (closedBall (0 : ℂ) R) (fun _ => ‖g‖ * δ) x := by
      intro x
      by_cases hx : x ∈ closedBall (0 : ℂ) R
      · rw [indicator_of_mem hx, ← mul_sub, Real.norm_eq_abs, abs_mul]
        have h1 : |extendCM R hR g x| ≤ ‖g‖ := abs_extendCM_le hR g x
        have h2 : |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < δ := (hk' x hx).2
        exact mul_le_mul h1 h2.le (abs_nonneg _) hM0
      · have hxU : x ∉ ball (0 : ℂ) R := fun h => hx (ball_subset_closedBall h)
        rw [indicator_of_notMem hx, laplacian_eq_zero_of_not_mem_tsupport hφ.2.2 hxU,
          laplacian_eq_zero_of_not_mem_tsupport hφk.2.2 hxU]
        simp
    have hint : Integrable (indicator (closedBall (0 : ℂ) R) (fun _ => ‖g‖ * δ)) volume :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    have hA := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbd)
    rw [Real.norm_eq_abs] at hA
    have hB : ∫ x, indicator (closedBall (0 : ℂ) R) (fun _ => ‖g‖ * δ) x =
        C1 * δ := by
      rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, measureReal_def, hC1]; ring
    linarith [le_abs_self (∫ x, (extendCM R hR g x * Laplacian.laplacian φ x -
        extendCM R hR g x * Laplacian.laplacian (φs k) x))]
  -- the mass pairing changes by at most `δ C2`
  have hE2 : (∫ x, φs k x ∂ν) - (∫ x, φ x ∂ν) ≤ δ * C2 := by
    have hsub2 : ∫ x, (φs k x - φ x) ∂ν = (∫ x, φs k x ∂ν) - (∫ x, φ x ∂ν) :=
      integral_sub hνk hφint
    have hbd : ∀ x, ‖φs k x - φ x‖ ≤ indicator (closedBall (0 : ℂ) R) (fun _ => δ) x := by
      intro x
      by_cases hx : x ∈ closedBall (0 : ℂ) R
      · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_sub_comm]
        exact (hk' x hx).1.le
      · rw [indicator_of_notMem hx, hφk_out x hx, hφ_out x hx, sub_self, norm_zero]
    have hint : Integrable (indicator (closedBall (0 : ℂ) R) (fun _ => δ)) ν :=
      (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hν.ne)
    have hA := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbd)
    rw [Real.norm_eq_abs] at hA
    have hB : ∫ x, indicator (closedBall (0 : ℂ) R) (fun _ => δ) x ∂ν = C2 * δ := by
      rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, measureReal_def, hC2]
    linarith [le_abs_self (∫ x, (φs k x - φ x) ∂ν)]
  linarith [hE1, hE2, hk k, hδsum]

end MatedCRT
