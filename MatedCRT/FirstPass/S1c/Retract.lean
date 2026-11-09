import MatedCRT.FirstPass.S1c.TestDense

/-!
# Radial retraction and continuous extension from the closed disc (Lemma 1 analytic layer, fleet note G-hT)

A supersolution is only required to be continuous on the closed disc `B̄_R`, while the Laplacian pairing is
integrated over `ℂ`. To work with globally continuous functions we extend `g ∈ C(B̄_R)` by composition with the
radial retraction `x ↦ min(R, |x|) x / |x|` of `ℂ` onto `B̄_R` (identity on `B̄_R`). Classical; no paper input.
-/

namespace MatedCRT

open Set Metric Filter Topology

variable {R : ℝ}

/-- Radial retraction of `ℂ` onto the closed disc of radius `R`: the identity on `B̄_R`, the radial projection outside. -/
noncomputable def radialRetract (R : ℝ) (x : ℂ) : ℂ :=
  (min R ‖x‖ / ‖x‖ : ℝ) • x

theorem norm_radialRetract (hR : 0 ≤ R) (x : ℂ) : ‖radialRetract R x‖ = min R ‖x‖ := by
  by_cases hx : x = 0
  · subst hx
    simp [radialRetract, min_eq_right hR]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hmin : 0 ≤ min R ‖x‖ := le_min hR (norm_nonneg x)
    unfold radialRetract
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hmin hn.le), div_mul_cancel₀ _ hn.ne']

theorem radialRetract_of_mem {R : ℝ} {x : ℂ} (hx : ‖x‖ ≤ R) : radialRetract R x = x := by
  by_cases h0 : x = 0
  · subst h0
    simp [radialRetract]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 h0
    unfold radialRetract
    rw [min_eq_right hx, div_self hn, one_smul]

theorem norm_radialRetract_le (hR : 0 ≤ R) (x : ℂ) : ‖radialRetract R x‖ ≤ R := by
  rw [norm_radialRetract hR]
  exact min_le_left _ _

/-- The radial retraction is continuous on `ℂ`. -/
theorem continuous_radialRetract (hR : 0 ≤ R) : Continuous (radialRetract R) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : radialRetract R 0 = 0 := by simp [radialRetract]
    have hnorm : Tendsto (fun y : ℂ => ‖y‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_norm (E := ℂ)).tendsto (0 : ℂ)
    unfold ContinuousAt
    rw [h0]
    refine squeeze_zero_norm (fun y => ?_) hnorm
    rw [norm_radialRetract hR]
    exact min_le_right _ _
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hcont : ContinuousAt (fun y : ℂ => (min R ‖y‖ / ‖y‖ : ℝ)) x :=
      ((continuous_const.min continuous_norm).continuousAt).div continuous_norm.continuousAt hn
    exact (hcont.smul continuousAt_id)

/-- The continuous extension of `g ∈ C(B̄_R)` to `ℂ`, by composition with the radial retraction. -/
noncomputable def extendCM (R : ℝ) (hR : 0 ≤ R) (g : C(closedBall (0 : ℂ) R, ℝ)) : ℂ → ℝ :=
  fun x => g ⟨radialRetract R x, mem_closedBall_zero_iff.2 (norm_radialRetract_le hR x)⟩

theorem continuous_extendCM (hR : 0 ≤ R) (g : C(closedBall (0 : ℂ) R, ℝ)) :
    Continuous (extendCM R hR g) :=
  g.continuous.comp ((continuous_radialRetract hR).subtype_mk _)

theorem extendCM_apply {x : ℂ} (hR : 0 ≤ R) (g : C(closedBall (0 : ℂ) R, ℝ)) (hx : x ∈ closedBall (0 : ℂ) R) :
    extendCM R hR g x = g ⟨x, hx⟩ := by
  unfold extendCM
  congr 1
  exact Subtype.ext (radialRetract_of_mem (mem_closedBall_zero_iff.1 hx))

/-- The extension is bounded by the sup norm of `g`. -/
theorem abs_extendCM_le (hR : 0 ≤ R) (g : C(closedBall (0 : ℂ) R, ℝ)) (x : ℂ) :
    |extendCM R hR g x| ≤ ‖g‖ := by
  unfold extendCM
  rw [← Real.norm_eq_abs]
  exact g.norm_coe_le_norm _

end MatedCRT
