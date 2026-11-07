import MatedCRT.Proofs.Sec4.SubsequentialConvergence.OdometerPreparedModuli

/-! Geometric estimates for boundary decay in a Euclidean ball. -/

namespace MatedCRT

open Metric Set

/-- A point in a complex ball has a radial boundary point at distance equal
to its distance from the boundary of the ball. -/
theorem exists_sphere_radial_distance {ρ : ℝ} (hρ : 0 < ρ) (x : ℂ)
    (hx : x ∈ ball 0 ρ) : ∃ z ∈ sphere (0 : ℂ) ρ, dist x z = ρ - ‖x‖ := by
  have hxρ : ‖x‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hx
  by_cases hx0 : x = 0
  · subst x
    refine ⟨(ρ : ℂ), ?_, ?_⟩
    · simp [abs_of_pos hρ]
    · simp [dist_eq_norm, abs_of_pos hρ]
  · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let a : ℝ := ρ / ‖x‖
    have ha : 0 ≤ a := div_nonneg hρ.le hnx.le
    have ha1 : 1 ≤ a := (le_div_iff₀ hnx).2 (by linarith)
    have han : a * ‖x‖ = ρ := div_mul_cancel₀ _ (ne_of_gt hnx)
    refine ⟨a • x, ?_, ?_⟩
    · rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, han]
    · have hs : x - a • x = (1 - a) • x := by simp [sub_smul]
      rw [dist_eq_norm, hs, norm_smul, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr ha1)]
      rw [neg_sub]
      nlinarith

/-- Boundary power decay controls a pair when its first point is within
`2R` of the boundary and the pair is at distance at most `R`. -/
theorem abs_sub_le_of_near_boundary {ρ R B χ : ℝ} {w : ℂ → ℝ}
    (hρ : 0 < ρ) (hR : 0 ≤ R) (hB : 0 ≤ B) (hχ : 0 ≤ χ)
    (hdecay : ∀ x ∈ ball (0 : ℂ) ρ, ∀ z ∈ sphere (0 : ℂ) ρ,
      |w x| ≤ B * dist x z ^ χ)
    {x y : ℂ} (hx : x ∈ ball 0 ρ) (hy : y ∈ ball 0 ρ)
    (hnear : ρ - ‖x‖ ≤ 2 * R) (hxy : dist x y ≤ R) :
    |w x - w y| ≤ 2 * B * (3 * R) ^ χ := by
  obtain ⟨z, hz, hzx⟩ := exists_sphere_radial_distance hρ x hx
  have hxz : dist x z ≤ 3 * R := by rw [hzx]; linarith
  have hyz : dist y z ≤ 3 * R := by
    have h := dist_triangle y x z
    rw [dist_comm y x] at h
    rw [hzx] at h
    linarith
  have hxpow := Real.rpow_le_rpow dist_nonneg hxz hχ
  have hypow := Real.rpow_le_rpow dist_nonneg hyz hχ
  have hxw := hdecay x hx z hz
  have hyw := hdecay y hy z hz
  have hw := abs_sub (w x) (w y)
  nlinarith [mul_nonneg hB (sub_nonneg.mpr hxpow), mul_nonneg hB (sub_nonneg.mpr hypow)]

/-- The interior and boundary estimates combine into a uniform radius
modulus on the open ball, including pairs near its boundary. -/
theorem abs_sub_le_of_interior_and_boundary_moduli
    {ρ R₁ ξ A C₁ q Cm C B χ : ℝ} {w : ℂ → ℝ}
    (hρ : 0 < ρ) (_hξ : 0 ≤ ξ) (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁)
    (_hq : 0 ≤ q) (hCm : 0 ≤ Cm) (hC : 0 ≤ C) (hB : 0 ≤ B) (hχ : 0 ≤ χ)
    (hint : ∀ (x y : ℂ) (r0 : ℝ), 0 ≤ r0 → dist x 0 + r0 < ρ → dist y 0 + r0 < ρ →
      ∀ R : ℝ, 0 < R → R < min R₁ (min r0 1) →
      ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2 →
      |w x - w y| ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q))
    (hdecay : ∀ x ∈ ball (0 : ℂ) ρ, ∀ z ∈ sphere (0 : ℂ) ρ,
      |w x| ≤ B * dist x z ^ χ)
    {R : ℝ} (hR : 0 < R) (hR₁ : R < R₁) (hRsmall : R < 1)
    {x y : ℂ} (hx : x ∈ ball 0 ρ) (hy : y ∈ ball 0 ρ)
    (hxy : ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2) :
    |w x - w y| ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) +
      2 * B * (3 * R) ^ χ := by
  have hxyR : dist x y ≤ R := by
    rw [dist_eq_norm]
    nlinarith [sq_nonneg (R - 1)]
  have hI : 0 ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) := by positivity
  have hBterm : 0 ≤ 2 * B * (3 * R) ^ χ := by positivity
  by_cases hxnear : ρ - ‖x‖ ≤ 2 * R
  · have h := abs_sub_le_of_near_boundary hρ hR.le hB hχ hdecay hx hy hxnear hxyR
    linarith
  · by_cases hynear : ρ - ‖y‖ ≤ 2 * R
    · have h := abs_sub_le_of_near_boundary hρ hR.le hB hχ hdecay hy hx hynear (by simpa [dist_comm] using hxyR)
      rw [abs_sub_comm] at h
      linarith
    · have hxsep : dist x 0 + 2 * R < ρ := by simpa using (show ‖x‖ + 2 * R < ρ by linarith)
      have hysep : dist y 0 + 2 * R < ρ := by simpa using (show ‖y‖ + 2 * R < ρ by linarith)
      have hRlt : R < min R₁ (min (2 * R) 1) := lt_min hR₁ (lt_min (by linarith) hRsmall)
      have h := hint x y (2 * R) (by positivity) hxsep hysep R hR hRlt hxy
      linarith

end MatedCRT
