import MatedCRT.Proofs.Sec4.SubsequentialConvergence.InteriorHolder
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.QuantitativeRescale

/-! Hölder limits from the radius-parametrized two-power modulus. -/

namespace MatedCRT

open Filter Topology Set Metric
open scoped NNReal

/-- A modulus at radius `R` controlling pairs at distance at most `R² / 8`
gives Hölder continuity of every pointwise limit. -/
theorem holderOn_of_eventual_radius_modulus
    {F : ℕ → ℂ → ℝ} {f : ℂ → ℝ} {K : Set ℂ}
    {C₁ C₂ M a b : ℝ≥0} {R₀ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1) (hR₀ : 0 < R₀)
    (hconv : ∀ x ∈ K, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hmod : ∀ R : ℝ, 0 < R → R < R₀ → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ ((R / 2) * (R / 2)) / 2 →
      dist (F n x) (F n y) ≤
        C₁ * (R / 2) ^ (2 * (a : ℝ)) + C₂ * R ^ (2 * (b : ℝ)))
    (hbound : ∀ x ∈ K, ∀ y ∈ K, ∀ᶠ n in atTop,
      dist (F n x) (F n y) ≤ M) : IsHolderContinuousOn f K := by
  let δ₀ : ℝ≥0 := Real.toNNReal (min 1 (R₀ ^ 2 / 16))
  let L : ℝ := (C₁ : ℝ) * 2 ^ (2 * (a : ℝ)) + (C₂ : ℝ) * 4 ^ (2 * (b : ℝ))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hδ₀ : 0 < (δ₀ : ℝ) := by dsimp [δ₀]; simp; positivity
  have hδ₀' : 0 < δ₀ := by exact_mod_cast hδ₀
  have hδ₀1 : δ₀ ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    dsimp [δ₀]
    exact max_le (min_le_left _ _) (by norm_num)
  apply holderOn_of_eventual_two_power_modulus ha hb ha1 hδ₀' hδ₀1 hconv
    (C := Real.toNNReal L) (M := M)
  · intro δ hδ hδlt x hx y hy hxy
    have hδR : δ < R₀ ^ 2 / 16 := by
      apply lt_of_lt_of_le hδlt
      dsimp [δ₀]
      exact max_le (min_le_right _ _) (by positivity)
    have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hsq : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ.le
    have hR : 4 * Real.sqrt δ < R₀ := by nlinarith
    filter_upwards [hmod (4 * Real.sqrt δ) (by positivity) hR] with n hn
    have hd : dist x y ≤ ((4 * Real.sqrt δ / 2) * (4 * Real.sqrt δ / 2)) / 2 := by
      nlinarith
    have h₁ : (4 * Real.sqrt δ / 2) ^ (2 * (a : ℝ)) =
        2 ^ (2 * (a : ℝ)) * δ ^ (a : ℝ) := by
      have heq : 4 * Real.sqrt δ / 2 = 2 * Real.sqrt δ := by ring
      rw [heq, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _), ← Real.rpow_div_two_eq_sqrt _ hδ.le]
      congr 1
      ring
    have h₂ : (4 * Real.sqrt δ) ^ (2 * (b : ℝ)) =
        4 ^ (2 * (b : ℝ)) * δ ^ (b : ℝ) := by
      rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _), ← Real.rpow_div_two_eq_sqrt _ hδ.le]
      congr 1
      ring
    have hv := hn x hx y hy hd
    rw [h₁, h₂] at hv
    rw [Real.coe_toNNReal _ hL]
    dsimp [L]
    have hda : 0 ≤ δ ^ (a : ℝ) := Real.rpow_nonneg hδ.le _
    have hdb : 0 ≤ δ ^ (b : ℝ) := Real.rpow_nonneg hδ.le _
    have hc₁ : 0 ≤ (C₁ : ℝ) * 2 ^ (2 * (a : ℝ)) := by positivity
    have hc₂ : 0 ≤ (C₂ : ℝ) * 4 ^ (2 * (b : ℝ)) := by positivity
    nlinarith [mul_nonneg hc₁ hdb, mul_nonneg hc₂ hda]
  · exact hbound

end MatedCRT
