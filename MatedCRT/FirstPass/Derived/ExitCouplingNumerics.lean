import Mathlib

/-!
# Choice of the small parameters in the equicontinuity of the laws of the stopped walks

Real analysis behind Berestycki–Gwynne (2020), Proposition 6.12: for every target distance `r > 0` there are
`T₀` and `δ₀ > 0` such that for all `δ ∈ (0, δ₀)`, with the scales `δ' = δ ^ a` (the ball radius of
Lemma 6.11) and the cell diameter `d = √δ / 4`, the constraints of the equicontinuity estimate hold:
`d < δ'`, `2 d + δ < √δ`, `T₀ (2 (3 (2 δ') + 2 d) + (2 δ + 2 d)) + exp (-T₀) < r`, and the error
`A δ ^ ξ + 2 (2 δ ^ e + ψ₀ (2 δ') + ⌊(2 δ') ^ (-3)⌋ ψ δ')` is at most `r`, for superpolynomial `ψ₀, ψ`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingNumerics

open Filter Set
open scoped Topology NNReal

/-- Extract a threshold from an eventual statement as `δ → 0+`. -/
theorem exists_delta0_of_eventually {P : ℝ → Prop} (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), P δ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → P δ := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨δ₀, hδ₀, h'⟩ := h
  exact ⟨δ₀, hδ₀, fun δ hδ hδlt =>
    h' (y := δ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; exact hδlt) hδ⟩

/-- `δ ^ a → 0` as `δ → 0+` for `a > 0`. -/
theorem tendsto_rpow_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ : ℝ => δ ^ a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (Real.continuous_rpow_const ha.le).tendsto (0 : ℝ)
  rw [Real.zero_rpow ha.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- `δ ^ a → 0+` as `δ → 0+` for `a > 0`. -/
theorem tendsto_rpow_zero_pos {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ : ℝ => δ ^ a) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_rpow_zero ha,
    eventually_mem_nhdsWithin.mono fun _ hδ => Real.rpow_pos_of_pos hδ a⟩

/-- A superpolynomial function tends to `0` at `0+`. -/
theorem tendsto_of_superpoly {ψ : ℝ → ℝ}
    (hψ : ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1 := (tendsto_rpow_zero one_pos).mul (hψ 1 one_pos)
  rw [mul_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with δ hδ
  have hδ' : (0 : ℝ) < δ := hδ
  rw [← mul_assoc, ← Real.rpow_add hδ']
  simp

/-- **Choice of the parameters.** -/
theorem exists_small_parameters {a e A ξ : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4) (he : 0 < e)
    (hξ : 0 < ξ) {ψ₀ ψ : ℝ → ℝ}
    (hψ₀ : ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hψ : ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hψnn : ∀ x : ℝ, 0 < x → 0 ≤ ψ x) {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) :
    ∃ T₀ : ℝ≥0, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      δ < 1 / 4 ∧ δ ^ a < κ ∧ Real.sqrt δ / 4 < δ ^ a ∧ 2 * (Real.sqrt δ / 4) + δ < Real.sqrt δ ∧
      (T₀ : ℝ) * (2 * (3 * (2 * δ ^ a) + 2 * (Real.sqrt δ / 4)) + (2 * δ + 2 * (Real.sqrt δ / 4))) +
        Real.exp (-(T₀ : ℝ)) < r ∧
      A * δ ^ ξ + 2 * (2 * δ ^ e + ψ₀ (2 * δ ^ a) +
        (⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℝ) * ψ (δ ^ a)) ≤ r := by
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ≥0, Real.exp (-(T₀ : ℝ)) ≤ r / 4 := by
    refine ⟨(Real.log (4 / r)).toNNReal, ?_⟩
    have h4 : 0 < 4 / r := by positivity
    calc Real.exp (-(((Real.log (4 / r)).toNNReal : ℝ≥0) : ℝ))
        ≤ Real.exp (-Real.log (4 / r)) :=
          Real.exp_le_exp.2 (neg_le_neg (by rw [Real.coe_toNNReal']; exact le_max_left _ _))
      _ = r / 4 := by rw [Real.exp_neg, Real.exp_log h4]; field_simp
  refine ⟨T₀, ?_⟩
  have hpa := tendsto_rpow_zero ha
  have hsq : Tendsto (fun δ : ℝ => Real.sqrt δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := Real.continuous_sqrt.tendsto (0 : ℝ)
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hL : Tendsto (fun δ : ℝ => (T₀ : ℝ) * (2 * (3 * (2 * δ ^ a) + 2 * (Real.sqrt δ / 4)) +
      (2 * δ + 2 * (Real.sqrt δ / 4)))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ((((hpa.const_mul 2).const_mul 3).add ((hsq.div_const 4).const_mul 2)).const_mul 2).add
      ((hid.const_mul 2).add ((hsq.div_const 4).const_mul 2)) |>.const_mul (T₀ : ℝ)
    simpa using this
  have hψ₀t : Tendsto (fun δ : ℝ => ψ₀ (2 * δ ^ a)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine (tendsto_of_superpoly hψ₀).comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · simpa using hpa.const_mul 2
    · exact eventually_mem_nhdsWithin.mono fun δ hδ => by
        have := Real.rpow_pos_of_pos (show (0 : ℝ) < δ from hδ) a
        exact mul_pos two_pos this
  have hKt : Tendsto (fun δ : ℝ => (⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℝ) * ψ (δ ^ a)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hg : Tendsto (fun δ : ℝ => (2 : ℝ) ^ (-3 : ℝ) * ((δ ^ a) ^ (-3 : ℝ) * ψ (δ ^ a)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := ((hψ 3 (by norm_num)).comp (tendsto_rpow_zero_pos ha)).const_mul ((2 : ℝ) ^ (-3 : ℝ))
      simpa using this
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
      have hx : (0 : ℝ) < δ ^ a := Real.rpow_pos_of_pos (show (0 : ℝ) < δ from hδ) a
      exact mul_nonneg (Nat.cast_nonneg _) (hψnn _ hx)
    · filter_upwards [eventually_mem_nhdsWithin] with δ hδ
      have hx : (0 : ℝ) < δ ^ a := Real.rpow_pos_of_pos (show (0 : ℝ) < δ from hδ) a
      have hy : 0 ≤ (2 * δ ^ a) ^ (-3 : ℝ) := Real.rpow_nonneg (by positivity) _
      rw [Real.mul_rpow (by norm_num) hx.le, ← mul_assoc]
      rw [Real.mul_rpow (by norm_num) hx.le] at hy
      exact mul_le_mul_of_nonneg_right (Nat.floor_le hy) (hψnn _ hx)
  have hE : Tendsto (fun δ : ℝ => A * δ ^ ξ + 2 * (2 * δ ^ e + ψ₀ (2 * δ ^ a) +
      (⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℝ) * ψ (δ ^ a))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ((tendsto_rpow_zero hξ).const_mul A).add
      ((((tendsto_rpow_zero he).const_mul 2).add hψ₀t).add hKt |>.const_mul 2)
    simpa using this
  have e1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 / 4 := hid.eventually (gt_mem_nhds (by norm_num))
  have e2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ a < κ := hpa.eventually (gt_mem_nhds hκ)
  have e3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (T₀ : ℝ) * (2 * (3 * (2 * δ ^ a) + 2 * (Real.sqrt δ / 4)) +
      (2 * δ + 2 * (Real.sqrt δ / 4))) < r / 2 := hL.eventually (gt_mem_nhds (half_pos hr))
  have e4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), A * δ ^ ξ + 2 * (2 * δ ^ e + ψ₀ (2 * δ ^ a) +
      (⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℝ) * ψ (δ ^ a)) < r := hE.eventually (gt_mem_nhds hr)
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 / 4 ∧ δ ^ a < κ ∧ Real.sqrt δ / 4 < δ ^ a ∧
      2 * (Real.sqrt δ / 4) + δ < Real.sqrt δ ∧
      (T₀ : ℝ) * (2 * (3 * (2 * δ ^ a) + 2 * (Real.sqrt δ / 4)) + (2 * δ + 2 * (Real.sqrt δ / 4))) +
        Real.exp (-(T₀ : ℝ)) < r ∧
      A * δ ^ ξ + 2 * (2 * δ ^ e + ψ₀ (2 * δ ^ a) +
        (⌊(2 * δ ^ a) ^ (-3 : ℝ)⌋₊ : ℝ) * ψ (δ ^ a)) ≤ r := by
    filter_upwards [e1, e2, e3, e4, eventually_mem_nhdsWithin] with δ h1 h2 h3 h4 hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    have hs0 : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
    have hs : Real.sqrt δ < 1 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      linarith
    have hss := Real.mul_self_sqrt hδ0.le
    refine ⟨h1, h2, ?_, ?_, by linarith, h4.le⟩
    · have hpow : Real.sqrt δ ≤ δ ^ a := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge hδ0 (by linarith) (by linarith)
      linarith
    · nlinarith
  obtain ⟨δ₀, hδ₀, h⟩ := exists_delta0_of_eventually hall
  exact ⟨δ₀, hδ₀, h⟩

end ExitCouplingNumerics
end MatedCRT
