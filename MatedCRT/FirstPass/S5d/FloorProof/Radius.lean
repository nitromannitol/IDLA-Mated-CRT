import MatedCRT.FirstPass.S5c.GreenLog

/-!
# Deterministic annuli and tolerances of the floor

For the localized index `n` (with real parameter `N ≥ 0`), the radius `r_N` of floor note equation (18) is chosen so that the
continuum pole bound `N + 4 ≤ α t G_{B_ρ}(0,x)` holds for `0 < |x| ≤ 3 r_N`. This uses the logarithmic lower bound of the disk
Green function on circles, `MatedCRT.S5c.greenFunction_ball_zero_ge_log` (FirstPass/S5c/GreenLog.lean:18, reused by import only).
-/

open Set Metric HarmonicBalls

namespace MatedCRT

namespace FloorProof

/-- The radius `r_N = (ρ/8) exp(-2π(N+4)/(α t))` of floor note (18). -/
noncomputable def floorRadius (ρ α t N : ℝ) : ℝ :=
  ρ / 8 * Real.exp (-(2 * Real.pi * (N + 4) / (α * t)))

theorem floorRadius_eq {ρ α t N : ℝ} :
    floorRadius ρ α t N = ρ / 8 * (Real.exp (2 * Real.pi * (N + 4) / (α * t)))⁻¹ := by
  unfold floorRadius
  rw [Real.exp_neg]

theorem floorRadius_pos {ρ α t N : ℝ} (hρ : 0 < ρ) : 0 < floorRadius ρ α t N := by
  unfold floorRadius
  positivity

/-- `r_N ≤ ρ/8` for `N ≥ 0` (so that `3 r_N < ρ/2`). -/
theorem floorRadius_le {ρ α t N : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (ht : 0 < t) (hN : 0 ≤ N) :
    floorRadius ρ α t N ≤ ρ / 8 := by
  rw [floorRadius_eq]
  have hK : 0 ≤ 2 * Real.pi * (N + 4) / (α * t) := by positivity
  have h1 : (Real.exp (2 * Real.pi * (N + 4) / (α * t)))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (Real.exp_pos _)]
    exact Real.one_le_exp hK
  have h2 : ρ / 8 * (Real.exp (2 * Real.pi * (N + 4) / (α * t)))⁻¹ ≤ ρ / 8 * 1 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

/-- Floor note (18): on `0 < |x| ≤ 3 r_N` the continuum surplus `α t G_{B_ρ}(0,x)` is at least `N + 4`. -/
theorem pole_of_floorRadius {ρ α t N : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (ht : 0 < t) (hN : 0 ≤ N)
    {x : ℂ} (hx0 : 0 < ‖x‖) (hxr : ‖x‖ ≤ 3 * floorRadius ρ α t N) :
    N + 4 ≤ α * t * greenFunction (ball (0 : ℂ) ρ) 0 x := by
  have hK : 0 ≤ 2 * Real.pi * (N + 4) / (α * t) := by positivity
  have hEpos : 0 < Real.exp (2 * Real.pi * (N + 4) / (α * t)) := Real.exp_pos _
  have hEinv : Real.exp (2 * Real.pi * (N + 4) / (α * t)) *
      (Real.exp (2 * Real.pi * (N + 4) / (α * t)))⁻¹ = 1 := mul_inv_cancel₀ hEpos.ne'
  have hr := floorRadius_eq (ρ := ρ) (α := α) (t := t) (N := N)
  have hxr' : ‖x‖ ≤ 3 * (ρ / 8 * (Real.exp (2 * Real.pi * (N + 4) / (α * t)))⁻¹) := by
    rw [← hr]
    exact hxr
  have hinv1 : (Real.exp (2 * Real.pi * (N + 4) / (α * t)))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hEpos]
    exact Real.one_le_exp hK
  have hRlt : ‖x‖ < ρ / 2 := by
    have h2 : ρ / 8 * (Real.exp (2 * Real.pi * (N + 4) / (α * t)))⁻¹ ≤ ρ / 8 * 1 :=
      mul_le_mul_of_nonneg_left hinv1 (by positivity)
    linarith
  have hsph : x ∈ sphere (0 : ℂ) ‖x‖ := mem_sphere_zero_iff_norm.2 rfl
  have hG := MatedCRT.S5c.greenFunction_ball_zero_ge_log hx0 hRlt hsph
  -- `ρ/(2‖x‖) ≥ (4/3) exp K`, so `log(ρ/(2‖x‖)) ≥ K`
  have hE1 : Real.exp (2 * Real.pi * (N + 4) / (α * t)) * ‖x‖ ≤ 3 * (ρ / 8) := by
    have := mul_le_mul_of_nonneg_left hxr' hEpos.le
    nlinarith [hEinv]
  have hle : (4 / 3 : ℝ) * Real.exp (2 * Real.pi * (N + 4) / (α * t)) ≤ ρ / 2 / ‖x‖ := by
    rw [le_div_iff₀ hx0]
    linarith
  have hlog1 : Real.log ((4 / 3 : ℝ) * Real.exp (2 * Real.pi * (N + 4) / (α * t))) ≤
      Real.log (ρ / 2 / ‖x‖) :=
    Real.log_le_log (mul_pos (by norm_num) hEpos) hle
  rw [Real.log_mul (by norm_num) hEpos.ne', Real.log_exp] at hlog1
  have hlog43 : 0 ≤ Real.log (4 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have hGlow : (N + 4) / (α * t) ≤ greenFunction (ball (0 : ℂ) ρ) 0 x := by
    have hpi : 0 < 2 * Real.pi := by positivity
    have h3 : (2 * Real.pi)⁻¹ * (2 * Real.pi * (N + 4) / (α * t)) = (N + 4) / (α * t) := by
      field_simp
    calc (N + 4) / (α * t) = (2 * Real.pi)⁻¹ * (2 * Real.pi * (N + 4) / (α * t)) := h3.symm
      _ ≤ (2 * Real.pi)⁻¹ * Real.log (ρ / 2 / ‖x‖) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ greenFunction (ball (0 : ℂ) ρ) 0 x := hG
  calc N + 4 = α * t * ((N + 4) / (α * t)) := by field_simp
    _ ≤ α * t * greenFunction (ball (0 : ℂ) ρ) 0 x := mul_le_mul_of_nonneg_left hGlow (by positivity)

end FloorProof

end MatedCRT
