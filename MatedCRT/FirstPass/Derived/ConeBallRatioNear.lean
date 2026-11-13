import Mathlib

/-!
# The ball-mass ratio of the γ-quantum cone near the marked point: deterministic step

Near the origin, the LQG measure `μ` of the `γ`-quantum cone is `|x|^{-γ²}` times a whole-plane LQG
measure `μ₀` (`exists_coneGFF_singularWeight`). For a centre `z` with `|z| < 3δ` the singular
weight cannot be compared to a constant on `B_δ(z)`, so the proof of Berestycki and Gwynne
(arXiv:2003.10320, Lemma A.2) compares both balls with one centred ball at a dyadic radius
`r ∈ [4δ, 8δ]`:

* `μ(B_δ(z)) ≤ μ(B_r(0)) = ∫_{B_r(0)} |x|^{-γ²} dμ₀` (numerator);
* `μ(B_{cδ}(z)) ≥ r^{-γ²} μ₀(B_{cδ}(z))`, since `B_{cδ}(z) ⊆ B_r(0)` and `μ₀` has no atom at `0`;
* `μ₀(B_{cδ}(z)) ≥ A μ₀(B_{8δ}(z)) ≥ A μ₀(B_{r/2}(0))` on the whole-plane ratio event at scale `8δ`;
* the centred variable `r^{γ²} ∫_{B_r(0)} |x|^{-γ²} dμ₀ / μ₀(B_{r/2}(0))` is at most `t`.

Together, `A μ(B_δ(z)) ≤ t μ(B_{cδ}(z))`. The second lemma chooses `A = (8δ)^{γ²/2+ζ/2}` and
`t = δ^{-ζ/4}`, which gives `δ^{γ²/2+ζ} μ(B_δ(z)) ≤ μ(B_{cδ}(z))` for `δ ≤ 1`.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **Near case, deterministic step.** Let `μ = |x|^{-γ²} μ₀` on the closed unit disk, with
`μ₀{0} = 0`. If `|z| < 3δ`, `4δ ≤ r ≤ min(8δ, 1)`, the whole-plane ratio bound
`A μ₀(B_{8δ}(z)) ≤ μ₀(B_{cδ}(z))` holds and the centred weighted mass satisfies
`r^{γ²} ∫_{B_r(0)} |x|^{-γ²} dμ₀ ≤ t μ₀(B_{r/2}(0))`, then `A μ(B_δ(z)) ≤ t μ(B_{cδ}(z))`. -/
lemma coneBallRatio_near_le {γ A t δ c r : ℝ} {μ μ₀ : Measure ℂ} {z : ℂ}
    (hrep : ∀ s : Set ℂ, MeasurableSet s → s ⊆ closedBall 0 1 →
      μ s = ∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂μ₀)
    (h0 : μ₀ {0} = 0) (hδ : 0 < δ) (hc1 : c ≤ 1)
    (hz : ‖z‖ < 3 * δ) (hr4 : 4 * δ ≤ r) (hr8 : r ≤ 8 * δ) (hr1 : r ≤ 1)
    (hW3 : ENNReal.ofReal A * μ₀ (ball z (8 * δ)) ≤ μ₀ (ball z (c * δ)))
    (hG : ENNReal.ofReal (r ^ (γ ^ 2)) *
        ∫⁻ x in ball 0 r, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂μ₀ ≤
      ENNReal.ofReal t * μ₀ (ball 0 (r / 2))) :
    ENNReal.ofReal A * μ (ball z δ) ≤ ENNReal.ofReal t * μ (ball z (c * δ)) := by
  have hr0 : 0 < r := by linarith
  have hcδ : c * δ ≤ δ := mul_le_of_le_one_left hδ.le hc1
  have hdz : dist z 0 = ‖z‖ := by rw [dist_zero_right]
  have hsubR : ball (0 : ℂ) r ⊆ closedBall 0 1 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hr1)
  have hB1 : ball z δ ⊆ ball 0 r := ball_subset_ball' (by rw [hdz]; linarith)
  have hBc : ball z (c * δ) ⊆ ball 0 r := ball_subset_ball' (by rw [hdz]; linarith)
  have hBh : ball (0 : ℂ) (r / 2) ⊆ ball z (8 * δ) :=
    ball_subset_ball' (by rw [dist_comm, hdz]; linarith)
  set I := ∫⁻ x in ball 0 r, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂μ₀ with hI
  have hnum : μ (ball z δ) ≤ I := by
    rw [hI, ← hrep _ measurableSet_ball hsubR]
    exact measure_mono hB1
  have hden : ENNReal.ofReal (r ^ (-γ ^ 2)) * μ₀ (ball z (c * δ)) ≤ μ (ball z (c * δ)) := by
    rw [hrep _ measurableSet_ball (hBc.trans hsubR), ← measure_sdiff_null (s := ball z (c * δ)) h0,
      ← setLIntegral_const]
    calc ∫⁻ _ in ball z (c * δ) \ {0}, ENNReal.ofReal (r ^ (-γ ^ 2)) ∂μ₀
        ≤ ∫⁻ x in ball z (c * δ) \ {0}, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂μ₀ := by
          refine setLIntegral_mono (by fun_prop) fun x hx => ENNReal.ofReal_le_ofReal ?_
          have hxr : ‖x‖ < r := by simpa using hBc hx.1
          have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx.2
          exact Real.rpow_le_rpow_of_nonpos hx0 hxr.le (by nlinarith)
      _ ≤ _ := lintegral_mono_set Set.sdiff_subset
  have hden2 : μ₀ (ball 0 (r / 2)) ≤ μ₀ (ball z (8 * δ)) := measure_mono hBh
  have hone : ENNReal.ofReal (r ^ (-γ ^ 2)) * ENNReal.ofReal (r ^ (γ ^ 2)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr0.le _), Real.rpow_neg hr0.le,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos hr0 _).ne', ENNReal.ofReal_one]
  calc ENNReal.ofReal A * μ (ball z δ)
      ≤ ENNReal.ofReal A *
          (ENNReal.ofReal (r ^ (-γ ^ 2)) * (ENNReal.ofReal (r ^ (γ ^ 2)) * I)) := by
        rw [← mul_assoc (ENNReal.ofReal (r ^ (-γ ^ 2))), hone, one_mul]
        exact mul_le_mul' le_rfl hnum
    _ ≤ ENNReal.ofReal A *
          (ENNReal.ofReal (r ^ (-γ ^ 2)) * (ENNReal.ofReal t * μ₀ (ball z (8 * δ)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hG.trans (mul_le_mul' le_rfl hden2)))
    _ = ENNReal.ofReal t *
          (ENNReal.ofReal (r ^ (-γ ^ 2)) * (ENNReal.ofReal A * μ₀ (ball z (8 * δ)))) := by
        ring
    _ ≤ ENNReal.ofReal t * (ENNReal.ofReal (r ^ (-γ ^ 2)) * μ₀ (ball z (c * δ))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hW3)
    _ ≤ ENNReal.ofReal t * μ (ball z (c * δ)) := mul_le_mul' le_rfl hden

/-- **Near case with the exponents of Lemma A.2.** With the whole-plane ratio bound at scale `8δ`
and exponent `γ²/2 + ζ/2`, and the centred weighted mass at most `δ^{-ζ/4} μ₀(B_{r/2}(0))`, for
`0 < δ ≤ 1` and `ζ > 0`: `δ^{γ²/2+ζ} μ(B_δ(z)) ≤ μ(B_{cδ}(z))`. -/
lemma coneBallRatio_near_le_rpow {γ ζ δ c r : ℝ} {μ μ₀ : Measure ℂ} {z : ℂ}
    (hrep : ∀ s : Set ℂ, MeasurableSet s → s ⊆ closedBall 0 1 →
      μ s = ∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂μ₀)
    (h0 : μ₀ {0} = 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hζ : 0 < ζ) (hc1 : c ≤ 1)
    (hz : ‖z‖ < 3 * δ) (hr4 : 4 * δ ≤ r) (hr8 : r ≤ 8 * δ) (hr1 : r ≤ 1)
    (hW3 : ENNReal.ofReal ((8 * δ) ^ (γ ^ 2 / 2 + ζ / 2)) * μ₀ (ball z (8 * δ)) ≤
      μ₀ (ball z (c * δ)))
    (hG : ENNReal.ofReal (r ^ (γ ^ 2)) *
        ∫⁻ x in ball 0 r, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂μ₀ ≤
      ENNReal.ofReal (δ ^ (-(ζ / 4))) * μ₀ (ball 0 (r / 2))) :
    ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * μ (ball z δ) ≤ μ (ball z (c * δ)) := by
  have hmain := coneBallRatio_near_le hrep h0 hδ hc1 hz hr4 hr8 hr1 hW3 hG
  set t := δ ^ (-(ζ / 4)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hδ _
  have hkey : t * δ ^ (γ ^ 2 / 2 + ζ) ≤ (8 * δ) ^ (γ ^ 2 / 2 + ζ / 2) := by
    rw [ht, ← Real.rpow_add hδ]
    calc δ ^ (-(ζ / 4) + (γ ^ 2 / 2 + ζ)) ≤ δ ^ (γ ^ 2 / 2 + ζ / 2) :=
          Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ ≤ (8 * δ) ^ (γ ^ 2 / 2 + ζ / 2) :=
          Real.rpow_le_rpow hδ.le (by linarith) (by positivity)
  have h2 : ENNReal.ofReal t * (ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * μ (ball z δ)) ≤
      ENNReal.ofReal t * μ (ball z (c * δ)) := by
    calc ENNReal.ofReal t * (ENNReal.ofReal (δ ^ (γ ^ 2 / 2 + ζ)) * μ (ball z δ))
        = ENNReal.ofReal (t * δ ^ (γ ^ 2 / 2 + ζ)) * μ (ball z δ) := by
          rw [ENNReal.ofReal_mul ht0.le, mul_assoc]
      _ ≤ ENNReal.ofReal ((8 * δ) ^ (γ ^ 2 / 2 + ζ / 2)) * μ (ball z δ) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hkey) le_rfl
      _ ≤ _ := hmain
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 ht0).ne' ENNReal.ofReal_ne_top).1 h2

end MatedCRT.FirstPass.Derived
