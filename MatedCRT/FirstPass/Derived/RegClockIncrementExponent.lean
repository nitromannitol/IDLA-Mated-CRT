import MatedCRT.FirstPass.Derived.RegClockIncrementPath

/-!
# Choice of exponents in the dyadic increment rate of the regularized clock

For `0 < γ < 2` the dyadic increment rate `dyadicIncrementRate γ α ε t I A` of the chaos over the Brownian
occupation measure decays polynomially in `ε` once the near-diagonal mass is `I = K₁ (2ε)^{2(1-θ)}`: take
`α = γ + δ`, `t = ε^c` and `θ` small. With `η = 2 - γ²/2 > 0`, `θ = η/8` and `γδ ≤ η/4`, the two terms balanced
by `t` both carry the power `ε^{(2 - 2θ - γ²/2 - γδ + δ²/2)/2} ≤ ε^{η/4}`, and the total-mass term carries
`ε^{δ²/2}`.
-/

open Real

namespace MatedCRT.KilledOccupation

/-- **Exponents for the dyadic increment rate.** For `0 < γ < 2` there are `δ ∈ (0, γ]`, `θ ∈ (0, 1]`, `c` and
`κ > 0` such that for all `K₁, K₃ ≥ 0` and `ε ∈ (0, 1]`,
`dyadicIncrementRate γ (γ + δ) ε (ε^c) (K₁ (2ε)^{2(1-θ)}) K₃ ≤ ((2^{γ²} - 1) 2^{2(1-θ)} K₁/2 + 1/2 + 2K₃) ε^κ`. -/
theorem exists_dyadicIncrementRate_le_rpow {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ δ θ c κ : ℝ, 0 < δ ∧ δ ≤ γ ∧ 0 < θ ∧ θ ≤ 1 ∧ 0 < κ ∧
      ∀ K₁ K₃ : ℝ, 0 ≤ K₁ → 0 ≤ K₃ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        dyadicIncrementRate γ (γ + δ) ε (ε ^ c) (K₁ * (2 * ε) ^ (2 * (1 - θ))) K₃ ≤
          ((Real.exp (γ ^ 2 * Real.log 2) - 1) * 2 ^ (2 * (1 - θ)) * K₁ / 2 + 1 / 2 + 2 * K₃) * ε ^ κ := by
  set η := 2 - γ ^ 2 / 2 with hη
  have hη0 : 0 < η := by nlinarith
  have hη2 : η ≤ 2 := by nlinarith [sq_nonneg γ]
  set δ := min γ (η / (4 * γ)) with hδ
  have hδ0 : 0 < δ := lt_min hγ0 (by positivity)
  have hδγ : δ ≤ γ := min_le_left _ _
  have hγδ : γ * δ ≤ η / 4 := by
    calc γ * δ ≤ γ * (η / (4 * γ)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hγ0.le
      _ = η / 4 := by field_simp
  set θ := η / 8 with hθ
  set c := (2 * (1 - θ) - (2 * γ ^ 2 - (2 * γ - (γ + δ)) ^ 2 / 2)) / 2 with hc
  set κ := min (η / 4) (δ ^ 2 / 2) with hκ
  refine ⟨δ, θ, c, κ, hδ0, hδγ, by positivity, by linarith, lt_min (by positivity) (by positivity), ?_⟩
  intro K₁ K₃ hK₁ hK₃ ε hε hε1
  have hu : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  set u := Real.log ε with hudef
  have hX : 0 ≤ Real.exp (γ ^ 2 * Real.log 2) - 1 := by
    have : 0 ≤ γ ^ 2 * Real.log 2 := mul_nonneg (sq_nonneg γ) (Real.log_nonneg one_le_two)
    linarith [Real.add_one_le_exp (γ ^ 2 * Real.log 2)]
  have hpow : ∀ y : ℝ, ε ^ y = Real.exp (u * y) := fun y => Real.rpow_def_of_pos hε y
  have hlog : ∀ x : ℝ, Real.exp (Real.log (1 / ε) * x) = Real.exp (u * (-x)) := fun x => by
    rw [one_div, Real.log_inv]
    congr 1
    ring
  have h2ε : (2 * ε) ^ (2 * (1 - θ)) = 2 ^ (2 * (1 - θ)) * Real.exp (u * (2 * (1 - θ))) := by
    rw [Real.mul_rpow zero_le_two hε.le, hpow]
  have e1 : Real.exp (u * (γ ^ 2 / 2)) * Real.exp (u * -(2 * γ ^ 2 - (2 * γ - (γ + δ)) ^ 2 / 2)) *
      Real.exp (u * (2 * (1 - θ))) / Real.exp (u * c) = Real.exp (u * (γ ^ 2 / 2 + c)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
    congr 1
    rw [hc]
    ring
  have e2 : Real.exp (u * (γ ^ 2 / 2)) * Real.exp (u * c) = Real.exp (u * (γ ^ 2 / 2 + c)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e3 : Real.exp (u * (γ ^ 2 / 2)) * Real.exp (u * -(γ ^ 2 / 2 - (γ + δ - γ) ^ 2 / 2)) =
      Real.exp (u * (δ ^ 2 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hκ1 : κ ≤ γ ^ 2 / 2 + c := by
    have hS : γ ^ 2 / 2 + c = (2 - 2 * θ - γ ^ 2 / 2 - γ * δ + δ ^ 2 / 2) / 2 := by
      rw [hc]
      ring
    rw [hS]
    have := min_le_left (η / 4) (δ ^ 2 / 2)
    nlinarith [sq_nonneg δ]
  have hb1 : Real.exp (u * (γ ^ 2 / 2 + c)) ≤ Real.exp (u * κ) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hκ1 hu)
  have hb3 : Real.exp (u * (δ ^ 2 / 2)) ≤ Real.exp (u * κ) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (min_le_right _ _) hu)
  have hA : 0 ≤ (Real.exp (γ ^ 2 * Real.log 2) - 1) * 2 ^ (2 * (1 - θ)) * K₁ / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hX (Real.rpow_nonneg zero_le_two _)) hK₁) zero_le_two
  unfold dyadicIncrementRate
  rw [hlog, hlog, h2ε, hpow, hpow, hpow]
  calc _ = (Real.exp (γ ^ 2 * Real.log 2) - 1) * 2 ^ (2 * (1 - θ)) * K₁ / 2 *
          (Real.exp (u * (γ ^ 2 / 2)) * Real.exp (u * -(2 * γ ^ 2 - (2 * γ - (γ + δ)) ^ 2 / 2)) *
            Real.exp (u * (2 * (1 - θ))) / Real.exp (u * c)) +
        1 / 2 * (Real.exp (u * (γ ^ 2 / 2)) * Real.exp (u * c)) +
        2 * K₃ * (Real.exp (u * (γ ^ 2 / 2)) * Real.exp (u * -(γ ^ 2 / 2 - (γ + δ - γ) ^ 2 / 2))) := by
        ring
    _ = (Real.exp (γ ^ 2 * Real.log 2) - 1) * 2 ^ (2 * (1 - θ)) * K₁ / 2 * Real.exp (u * (γ ^ 2 / 2 + c)) +
        1 / 2 * Real.exp (u * (γ ^ 2 / 2 + c)) + 2 * K₃ * Real.exp (u * (δ ^ 2 / 2)) := by
        rw [e1, e2, e3]
    _ ≤ (Real.exp (γ ^ 2 * Real.log 2) - 1) * 2 ^ (2 * (1 - θ)) * K₁ / 2 * Real.exp (u * κ) +
        1 / 2 * Real.exp (u * κ) + 2 * K₃ * Real.exp (u * κ) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb1 hA) (mul_le_mul_of_nonneg_left hb1 (by norm_num)))
          (mul_le_mul_of_nonneg_left hb3 (by positivity))
    _ = _ := by ring

end MatedCRT.KilledOccupation
