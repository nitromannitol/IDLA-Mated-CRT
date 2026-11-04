import MatedCRT.Draft.Section4

/-!
# The admissible-supersolution comparison in Theorem 4.1

The distributional inequality from Lemma 4.8 can be normalized by its positive constant;
the definition of the least supersolution then gives one side of the comparison.
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls Laplacian
open scoped ENNReal

/-- Normalize a distributional Laplacian upper bound by a positive constant. -/
theorem laplacianLE_inv_scale {w : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ} {c : ℝ}
    (hc : 0 < c) (h : LaplacianLE w (ENNReal.ofReal c • μ) U) :
    LaplacianLE (fun x => c⁻¹ * w x) μ U := by
  refine ⟨h.1.smul c⁻¹, fun φ hφ hφ0 hφμ => ?_⟩
  have hφscaled : Integrable φ (ENNReal.ofReal c • μ) := hφμ.smul_measure ENNReal.ofReal_ne_top
  have hh := h.2 φ hφ hφ0 hφscaled
  rw [integral_smul_measure] at hh
  simp only [ENNReal.toReal_ofReal hc.le, smul_eq_mul] at hh
  have hi : (fun x => (c⁻¹ * w x) * Δ φ x) =
      fun x => c⁻¹ * (w x * Δ φ x) := by
    funext x
    ring
  rw [hi, integral_const_mul]
  calc
    c⁻¹ * ∫ x, w x * Δ φ x ≤ c⁻¹ * (c * ∫ x, φ x ∂μ) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hc.le)
    _ = ∫ x, φ x ∂μ := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- A continuous candidate satisfying the scaled upper Laplacian and obstacle bounds is above
the scaled least supersolution at every point of the closed ball away from the pole. -/
theorem scaled_leastSupersolution_le {μ : Measure ℂ} {ρ t c : ℝ} {w : ℂ → ℝ}
    (hc : 0 < c) (hw : ContinuousOn w (closedBall 0 ρ))
    (hlap : LaplacianLE w (ENNReal.ofReal c • μ) (ball 0 ρ))
    (hobs : ∀ x ∈ closedBall (0 : ℂ) ρ, x ≠ 0 →
      -t * c * greenFunction (ball 0 ρ) 0 x ≤ w x)
    {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) ρ) (hx0 : x ≠ 0) :
    c * leastSupersolution μ ρ 0 t x ≤ w x := by
  have hsup : (fun x => c⁻¹ * w x) ∈ supersolutions μ ρ 0 t := by
    refine ⟨continuousOn_const.mul hw, laplacianLE_inv_scale hc hlap, ?_⟩
    intro y hy hy0
    have hy' := mul_le_mul_of_nonneg_left (hobs y hy hy0) (inv_nonneg.mpr hc.le)
    have hid : c⁻¹ * (-t * c * greenFunction (ball 0 ρ) 0 y) =
        -t * greenFunction (ball 0 ρ) 0 y := by
      field_simp
    simpa only [hid] using hy'
  have hle := leastSupersolution_le hsup hx hx0
  have := mul_le_mul_of_nonneg_left hle hc.le
  simpa [← mul_assoc, mul_inv_cancel₀ hc.ne'] using this

/-- The same comparison holds at the pole when the least supersolution is continuous. -/
theorem scaled_leastSupersolution_le_on_closedBall {μ : Measure ℂ} {ρ t c : ℝ} {w : ℂ → ℝ}
    (hρ : 0 < ρ) (hc : 0 < c) (hw : ContinuousOn w (closedBall 0 ρ))
    (hcont : ContinuousOn (leastSupersolution μ ρ 0 t) (closedBall 0 ρ))
    (hlap : LaplacianLE w (ENNReal.ofReal c • μ) (ball 0 ρ))
    (hobs : ∀ x ∈ closedBall (0 : ℂ) ρ, x ≠ 0 →
      -t * c * greenFunction (ball 0 ρ) 0 x ≤ w x) :
    ∀ x ∈ closedBall (0 : ℂ) ρ, c * leastSupersolution μ ρ 0 t x ≤ w x := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    let A : Set ℂ := {0}ᶜ ∩ ball 0 ρ
    have hA : closure A ⊆ closedBall (0 : ℂ) ρ :=
      (closure_mono inter_subset_right).trans closure_ball_subset_closedBall
    have h0 : (0 : ℂ) ∈ closure A := by
      simpa [A, inter_comm] using
        (dense_compl_singleton (0 : ℂ)).open_subset_closure_inter isOpen_ball
          (mem_ball_self hρ : (0 : ℂ) ∈ ball 0 ρ)
    apply le_on_closure (s := A) ?_ ((continuousOn_const.mul hcont).mono hA) (hw.mono hA) h0
    intro y hy
    exact scaled_leastSupersolution_le hc hw hlap hobs (ball_subset_closedBall hy.2) (by simpa using hy.1)
  · exact scaled_leastSupersolution_le hc hw hlap hobs hx hx0

end MatedCRT
