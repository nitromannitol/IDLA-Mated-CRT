import MatedCRT.Proofs.Sec4.SubsequentialConvergence.OdometerPreparedModuli
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.RadiusHolder

/-! Geometric estimates for boundary decay in a Euclidean ball. -/

namespace MatedCRT

open Metric Set Filter Topology
open scoped NNReal

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

/-- The three powers in the combined radius estimate can be bounded by
one positive power on scales below one. -/
theorem radius_modulus_single_power
    {R ξ A C₁ q Cm C B χ : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hξ : 0 ≤ ξ) (hA : 0 ≤ A)
    (hC₁ : 0 ≤ C₁) (hq : 0 ≤ q) (hCm : 0 ≤ Cm) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hχ : 0 ≤ χ) :
    Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q) + 2 * B * (3 * R) ^ χ ≤
      (Cm * (A * C + 2 * C * C₁) + 2 * B * 3 ^ χ) *
        R ^ (min 1 (min ξ (min q χ))) := by
  let p := min 1 (min ξ (min q χ))
  have hpξ : p ≤ ξ := (min_le_right _ _).trans (min_le_left _ _)
  have hpq : p ≤ q := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hpχ : p ≤ χ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp : 0 ≤ p := le_min zero_le_one (le_min hξ (le_min hq hχ))
  have hξp : R ^ ξ ≤ R ^ p := Real.rpow_le_rpow_of_exponent_ge hR hR1 hpξ
  have hqp : R ^ q ≤ R ^ p := Real.rpow_le_rpow_of_exponent_ge hR hR1 hpq
  have hχp : R ^ χ ≤ R ^ p := Real.rpow_le_rpow_of_exponent_ge hR hR1 hpχ
  have hhalf : (R / 2) ^ ξ ≤ R ^ ξ := Real.rpow_le_rpow (by positivity) (by linarith) hξ
  have h3 : (3 * R) ^ χ = 3 ^ χ * R ^ χ := Real.mul_rpow (by positivity) hR.le
  rw [h3]
  have hRp : 0 ≤ R ^ p := Real.rpow_nonneg hR.le p
  have h3p : 0 ≤ (3 : ℝ) ^ χ := Real.rpow_nonneg (by positivity) χ
  have hAC : 0 ≤ A * C := mul_nonneg hA hC
  have hCC : 0 ≤ 2 * C * C₁ := by positivity
  have hBB : 0 ≤ 2 * B * 3 ^ χ := by positivity
  have hleft : A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q ≤
      (A * C + 2 * C * C₁) * R ^ p := by
    nlinarith [mul_nonneg hAC (sub_nonneg.mpr (hhalf.trans hξp)),
      mul_nonneg hCC (sub_nonneg.mpr hqp)]
  have hright : 2 * B * (3 ^ χ * R ^ χ) ≤ (2 * B * 3 ^ χ) * R ^ p := by
    nlinarith [mul_nonneg hBB (sub_nonneg.mpr hχp)]
  have := mul_le_mul_of_nonneg_left hleft hCm
  nlinarith

/-- A single-power radius modulus and bounded oscillation imply Hölder
continuity, with half the radius exponent. -/
theorem holderOn_of_single_power_radius_modulus
    {f : ℂ → ℝ} {K : Set ℂ} {L M p R₀ : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hp : 0 < p) (hp2 : p ≤ 2) (hR₀ : 0 < R₀)
    (hmod : ∀ R : ℝ, 0 < R → R < R₀ → ∀ x ∈ K, ∀ y ∈ K,
      dist x y ≤ ((R / 2) * (R / 2)) / 2 → dist (f x) (f y) ≤ L * R ^ p)
    (hbound : ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) ≤ M) :
    IsHolderContinuousOn f K := by
  let a : ℝ≥0 := ⟨p / 2, by positivity⟩
  have ha : 0 < a := by exact_mod_cast (show 0 < p / 2 by positivity)
  have ha1 : a ≤ 1 := by exact_mod_cast (show p / 2 ≤ 1 by linarith)
  apply holderOn_of_eventual_radius_modulus (F := fun _ => f)
    (C₁ := 0) (C₂ := ⟨L, hL⟩) (M := ⟨M, hM⟩) (a := a) (b := a)
    ha ha ha1 hR₀
  · intro x hx
    exact tendsto_const_nhds
  · intro R hR hRlt
    filter_upwards [] with n x hx y hy hxy
    have h := hmod R hR hRlt x hx y hy hxy
    change dist (f x) (f y) ≤ (0 : ℝ) * _ + L * R ^ (2 * (a : ℝ))
    have haeq : 2 * (a : ℝ) = p := by change 2 * (p / 2) = p; ring
    simpa [haeq] using h
  · intro x hx y hy
    filter_upwards [] with n
    exact hbound x hx y hy

/-- A boundary-decaying function has bounded oscillation on the ball. -/
theorem oscillation_le_of_boundary_decay {ρ B χ : ℝ} {w : ℂ → ℝ}
    (hρ : 0 < ρ) (hB : 0 ≤ B) (hχ : 0 ≤ χ)
    (hdecay : ∀ x ∈ ball (0 : ℂ) ρ, ∀ z ∈ sphere (0 : ℂ) ρ,
      |w x| ≤ B * dist x z ^ χ) :
    ∀ x ∈ ball (0 : ℂ) ρ, ∀ y ∈ ball (0 : ℂ) ρ,
      dist (w x) (w y) ≤ 2 * B * ρ ^ χ := by
  have hb : ∀ x ∈ ball (0 : ℂ) ρ, |w x| ≤ B * ρ ^ χ := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := exists_sphere_radial_distance hρ x hx
    have hd : dist x z ≤ ρ := by rw [hzx]; exact sub_le_self _ (norm_nonneg _)
    exact (hdecay x hx z hz).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg hd hχ) hB)
  intro x hx y hy
  rw [Real.dist_eq]
  have h := abs_sub (w x) (w y)
  linarith [hb x hx, hb y hy]

/-- Interior two-point estimates and boundary power decay imply Hölder
continuity on the whole open ball. -/
theorem holderOn_ball_of_interior_and_boundary_moduli
    {ρ R₁ ξ A C₁ q Cm C B χ : ℝ} {w : ℂ → ℝ}
    (hρ : 0 < ρ) (hR₁ : 0 < R₁) (hξ : 0 < ξ) (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁)
    (hq : 0 < q) (hCm : 0 ≤ Cm) (hC : 0 ≤ C) (hB : 0 ≤ B) (hχ : 0 < χ)
    (hint : ∀ (x y : ℂ) (r0 : ℝ), 0 ≤ r0 → dist x 0 + r0 < ρ → dist y 0 + r0 < ρ →
      ∀ R : ℝ, 0 < R → R < min R₁ (min r0 1) →
      ‖x - y‖ ≤ ((R / 2) * (R / 2)) / 2 →
      |w x - w y| ≤ Cm * (A * C * (R / 2) ^ ξ + 2 * C * C₁ * R ^ q))
    (hdecay : ∀ x ∈ ball (0 : ℂ) ρ, ∀ z ∈ sphere (0 : ℂ) ρ,
      |w x| ≤ B * dist x z ^ χ) : IsHolderContinuousOn w (ball 0 ρ) := by
  let p := min 1 (min ξ (min q χ))
  let L := Cm * (A * C + 2 * C * C₁) + 2 * B * 3 ^ χ
  have hp : 0 < p := lt_min zero_lt_one (lt_min hξ (lt_min hq hχ))
  have hp2 : p ≤ 2 := (min_le_left _ _).trans (by norm_num)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hM : 0 ≤ 2 * B * ρ ^ χ := by positivity
  apply holderOn_of_single_power_radius_modulus (L := L) (M := 2 * B * ρ ^ χ)
    (p := p) (R₀ := min R₁ 1) hL hM hp hp2 (lt_min hR₁ zero_lt_one)
  · intro R hR hRlt x hx y hy hxy
    have hRi : R < R₁ := hRlt.trans_le (min_le_left _ _)
    have hRsmall : R < 1 := hRlt.trans_le (min_le_right _ _)
    rw [Real.dist_eq]
    exact (abs_sub_le_of_interior_and_boundary_moduli hρ hξ.le hA hC₁ hq.le hCm hC hB hχ.le
      hint hdecay hR hRi hRsmall hx hy (by simpa [dist_eq_norm] using hxy)).trans
      (radius_modulus_single_power hR hRsmall.le hξ.le hA hC₁ hq.le hCm hC hB hχ.le)
  · exact oscillation_le_of_boundary_decay hρ hB hχ.le hdecay

end MatedCRT
