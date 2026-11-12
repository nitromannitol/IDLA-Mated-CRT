import MatedCRT.Defs.QuantumCone

/-!
# Circle smears of the rescaled field

For a sample `(hC, hcirc)` and a scale `R > 0`, the field `h(R ·) + Q log R - γ⁻¹ log b` has circle averages
`rescaledCircle γ hcirc R b` and pairings `rescaledPairing γ hC R b` (eq:quantum-cone-scaling). If the pairing of `h` with
the dilated test function `φ(R⁻¹ ·)` is the limit as `ε → 0⁺` of the circle smears `∫ φ(R⁻¹ z) h_ε(z) dz`, then the pairing
of the rescaled field with `φ` is the limit of the circle smears `∫ φ(z) h^b_ε(z) dz` of the rescaled field. This is the
change of variables `w = R z`, which turns the circle average `h_{Rε}(R z)` at radius `Rε` into the smear at radius `ε`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace MatedCRT.FirstPass.Derived

/-- Change of variables `w = R z` in the circle smear: `∫ φ(z) h_{Rε}(R z) dz = R⁻² ∫ φ(R⁻¹ w) h_{Rε}(w) dw`. -/
theorem integral_mul_circle_comp_mul {R : ℝ} (hR : 0 < R) (φ g : ℂ → ℝ) :
    ∫ z, φ z * g ((R : ℂ) * z) = (R⁻¹) ^ 2 * ∫ w, φ ((R⁻¹ : ℂ) * w) * g w := by
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have h := Measure.integral_comp_smul (μ := (volume : Measure ℂ))
    (fun w => φ ((R⁻¹ : ℂ) * w) * g w) R
  simp only [Complex.real_smul, Complex.finrank_real_complex, smul_eq_mul] at h
  have hcancel : ∀ z : ℂ, (R⁻¹ : ℂ) * ((R : ℂ) * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hR0, one_mul]
  simp only [hcancel] at h
  rw [h, abs_of_pos (inv_pos.mpr (pow_pos hR 2)), inv_pow]

/-- **Circle smears of the rescaled field.** If `∫ φ(R⁻¹ z) h_ε(z) dz → (h, φ(R⁻¹ ·))` as `ε → 0⁺`, then
`∫ φ(z) h^b_ε(z) dz → (h^b, φ)` as `ε → 0⁺`, where `h^b = h(R ·) + Q log R - γ⁻¹ log b` (`R > 0`, `φ` continuous with
compact support, the circle average process continuous on `(0, ∞) × ℂ`). -/
theorem tendsto_integral_mul_rescaledCircle {γ b R : ℝ} (hR : 0 < R) {hC : (ℂ → ℝ) → ℝ} {hcirc : ℝ → ℂ → ℝ}
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ))
    (h : Tendsto (fun ε => ∫ z, φ ((R⁻¹ : ℂ) * z) * hcirc ε z) (𝓝[>] 0)
      (𝓝 (hC fun x => φ ((R⁻¹ : ℂ) * x)))) :
    Tendsto (fun ε => ∫ z, φ z * rescaledCircle γ hcirc R b ε z) (𝓝[>] 0)
      (𝓝 (rescaledPairing γ hC R b φ)) := by
  set K : ℝ := rescaledCircle γ hcirc R b 1 0 - hcirc (R * 1) ((R : ℂ) * 0) with hK
  have hKc : ∀ r z, rescaledCircle γ hcirc R b r z = hcirc (R * r) ((R : ℂ) * z) + K := by
    intro r z
    simp only [hK, rescaledCircle]
    ring
  have hKp : rescaledPairing γ hC R b φ =
      (R⁻¹) ^ 2 * hC (fun x => φ ((R⁻¹ : ℂ) * x)) + K * ∫ x, φ x := by
    simp only [hK, rescaledPairing, rescaledCircle]
    ring
  have hRε : Tendsto (fun ε : ℝ => R * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => R * ε) (𝓝 0) (𝓝 (R * 0)) := (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun ε hε => mul_pos hR hε
  have hlim : Tendsto (fun ε => (R⁻¹) ^ 2 * (∫ z, φ ((R⁻¹ : ℂ) * z) * hcirc (R * ε) z) + K * ∫ x, φ x)
      (𝓝[>] 0) (𝓝 (rescaledPairing γ hC R b φ)) := by
    rw [hKp]
    exact ((h.comp hRε).const_mul ((R⁻¹) ^ 2)).add_const (K * ∫ x, φ x)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hRε0 : 0 < R * ε := mul_pos hR hε
  have hgc : Continuous fun z : ℂ => hcirc (R * ε) ((R : ℂ) * z) := by
    have hmap : Continuous fun z : ℂ => ((R * ε : ℝ), (R : ℂ) * z) :=
      continuous_const.prodMk (continuous_const.mul continuous_id)
    refine hcont.comp_continuous hmap fun z => ?_
    exact ⟨hRε0, mem_univ _⟩
  have hi1 : Integrable fun z : ℂ => φ z * hcirc (R * ε) ((R : ℂ) * z) :=
    (hφ.mul hgc).integrable_of_hasCompactSupport (hφc.mul_right)
  have hi2 : Integrable fun z : ℂ => K * φ z :=
    (hφ.integrable_of_hasCompactSupport hφc).const_mul K
  have hfun : (fun z => φ z * rescaledCircle γ hcirc R b ε z) =
      fun z => φ z * hcirc (R * ε) ((R : ℂ) * z) + K * φ z := by
    funext z
    rw [hKc]
    ring
  rw [hfun, integral_add hi1 hi2, integral_const_mul,
    integral_mul_circle_comp_mul hR φ (hcirc (R * ε))]

end MatedCRT.FirstPass.Derived

end
