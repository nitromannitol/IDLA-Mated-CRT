import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Superpolynomial envelope of the exit-time lower tail (proof of BG20 Lemma 6.9)

The Brownian estimate (6.29) of BG20 (arXiv:2003.10320, Lemma 6.8) gives, for each `p : ℕ`, a constant
`C_p` with `P[exit before σ_K(r)] ≤ C_p r^p` for `r ∈ (0, 1)`. In the proof of Lemma 6.9 the ratio `r` is at
most `A δ^β` (with `A = 5`, `β = ℓ - 1` in the regime of `MatedCRT.StepScaleRegime`), and the estimate (6.32)
needs a *single* superpolynomial function `ψ₀(δ)` bounding the probability for every `δ`.

This file builds that function as a pure real-analysis construction:

* `envelope C A β δ := ⨅ p, (C_p)₊ (A δ^β)^p`, which dominates every probability bounded by `C_p r^p` for
  `0 ≤ r ≤ A δ^β` (`le_envelope`, `le_ofReal_envelope`) and satisfies `δ^{-p} envelope δ → 0` as `δ ↓ 0`
  for every real `p` (`tendsto_rpow_neg_mul_envelope`);
* `budget δ := exp(-1/δ)` for `δ > 0` (and `0` otherwise), a positive superpolynomial tolerance for the
  comparison of the walk with Brownian motion;
* `cutoff C A β δ₁ δ`, equal to `envelope + budget` for `δ ≤ δ₁` and to `1` beyond, which has exactly the
  properties required of `ψ₀` in (6.32): it is nonnegative on `[0, ∞)`, vanishes at `0`, and
  `δ^{-p} ψ₀(δ) → 0` as `δ ↓ 0` for every `p > 0` (`cutoff_superpoly`).

Since `r ↦ C_p r^p` is monotone, no supremum over `r ≤ A δ^β` is needed.
-/

namespace MatedCRT.SuperpolyEnvelope

open Filter Topology
open scoped ENNReal

/-- The superpolynomial envelope `δ ↦ ⨅ p, (C_p)₊ (A δ^β)^p` of the family of polynomial bounds `C_p r^p`
at the scale `r = A δ^β`. -/
noncomputable def envelope (C : ℕ → ℝ) (A β δ : ℝ) : ℝ :=
  ⨅ p : ℕ, max (C p) 0 * (A * δ ^ β) ^ p

lemma term_nonneg (C : ℕ → ℝ) {A β δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (p : ℕ) :
    0 ≤ max (C p) 0 * (A * δ ^ β) ^ p :=
  mul_nonneg (le_max_right _ _) (pow_nonneg (mul_nonneg hA (Real.rpow_nonneg hδ β)) p)

lemma bddBelow_range_term (C : ℕ → ℝ) {A β δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    BddBelow (Set.range fun p : ℕ => max (C p) 0 * (A * δ ^ β) ^ p) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact term_nonneg C hA hδ p⟩

theorem envelope_nonneg (C : ℕ → ℝ) {A β δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    0 ≤ envelope C A β δ :=
  le_ciInf (term_nonneg C hA hδ)

theorem envelope_le (C : ℕ → ℝ) {A β δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (p : ℕ) :
    envelope C A β δ ≤ max (C p) 0 * (A * δ ^ β) ^ p :=
  ciInf_le (bddBelow_range_term C hA hδ) p

theorem envelope_zero (C : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β) :
    envelope C A β 0 = 0 := by
  refine le_antisymm ?_ (envelope_nonneg C hA le_rfl)
  calc envelope C A β 0 ≤ max (C 1) 0 * (A * (0 : ℝ) ^ β) ^ 1 := envelope_le C hA le_rfl 1
    _ = 0 := by rw [Real.zero_rpow hβ.ne']; ring

/-- A number bounded by `(C_p)₊ r^p` for every `p`, with `0 ≤ r ≤ A δ^β`, is bounded by the envelope. -/
theorem le_envelope_of_max {C : ℕ → ℝ} {A β δ x r : ℝ} (hr : 0 ≤ r) (hrA : r ≤ A * δ ^ β)
    (h : ∀ p : ℕ, x ≤ max (C p) 0 * r ^ p) : x ≤ envelope C A β δ :=
  le_ciInf fun p => (h p).trans <|
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrA p) (le_max_right _ _)

/-- A number bounded by `C_p r^p` for every `p`, with `0 ≤ r ≤ A δ^β`, is bounded by the envelope. -/
theorem le_envelope {C : ℕ → ℝ} {A β δ x r : ℝ} (hr : 0 ≤ r) (hrA : r ≤ A * δ ^ β)
    (h : ∀ p : ℕ, x ≤ C p * r ^ p) : x ≤ envelope C A β δ :=
  le_envelope_of_max hr hrA fun p =>
    (h p).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr p))

/-- The `ℝ≥0∞` form: a measure of an event bounded by `ofReal (C_p r^p)` for every `p`, with
`0 ≤ r ≤ A δ^β`, is bounded by `ofReal` of the envelope. -/
theorem le_ofReal_envelope {C : ℕ → ℝ} {A β δ r : ℝ} {μ : ℝ≥0∞} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hr : 0 ≤ r) (hrA : r ≤ A * δ ^ β) (h : ∀ p : ℕ, μ ≤ ENNReal.ofReal (C p * r ^ p)) :
    μ ≤ ENNReal.ofReal (envelope C A β δ) := by
  have h' : ∀ p : ℕ, μ ≤ ENNReal.ofReal (max (C p) 0 * r ^ p) := fun p =>
    (h p).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr p)))
  have hμ : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h' 0)
  rw [ENNReal.le_ofReal_iff_toReal_le hμ (envelope_nonneg C hA hδ)]
  exact le_envelope_of_max hr hrA fun p =>
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (le_max_right _ _) (pow_nonneg hr p)) (h' p)

/-- **The envelope is superpolynomially small**: `δ^{-p} envelope δ → 0` as `δ ↓ 0`, for every real `p`. -/
theorem tendsto_rpow_neg_mul_envelope (C : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β) (p : ℝ) :
    Tendsto (fun δ => δ ^ (-p) * envelope C A β δ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (p / β)
  have hnβ : p < n * β := by rwa [div_lt_iff₀ hβ] at hn
  have hlim : Tendsto (fun δ : ℝ => max (C n) 0 * A ^ n * δ ^ ((n : ℝ) * β - p)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun δ : ℝ => δ ^ ((n : ℝ) * β - p)) 0 :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
    have h0 : Tendsto (fun δ : ℝ => δ ^ ((n : ℝ) * β - p)) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow (by linarith : (n : ℝ) * β - p ≠ 0)] using hc.tendsto
    simpa using (h0.const_mul (max (C n) 0 * A ^ n)).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact mul_nonneg (Real.rpow_nonneg hδ.le _) (envelope_nonneg C hA hδ.le)
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    have e : δ ^ ((n : ℝ) * β - p) = (δ ^ β) ^ n * δ ^ (-p) := by
      rw [sub_eq_add_neg, Real.rpow_add hδ, mul_comm (n : ℝ) β, Real.rpow_mul hδ.le,
        Real.rpow_natCast]
    calc δ ^ (-p) * envelope C A β δ ≤ δ ^ (-p) * (max (C n) 0 * (A * δ ^ β) ^ n) :=
          mul_le_mul_of_nonneg_left (envelope_le C hA hδ.le n) (Real.rpow_nonneg hδ.le _)
      _ = max (C n) 0 * A ^ n * δ ^ ((n : ℝ) * β - p) := by rw [e, mul_pow]; ring

/-- The comparison tolerance `exp(-1/δ)` for `δ > 0`, and `0` otherwise. -/
noncomputable def budget (δ : ℝ) : ℝ := if 0 < δ then Real.exp (-δ⁻¹) else 0

theorem budget_pos {δ : ℝ} (hδ : 0 < δ) : 0 < budget δ := by
  simp [budget, hδ, Real.exp_pos]

theorem budget_nonneg (δ : ℝ) : 0 ≤ budget δ := by
  unfold budget; split_ifs <;> positivity

theorem budget_zero : budget 0 = 0 := by simp [budget]

/-- **The tolerance is superpolynomially small**: `δ^{-p} exp(-1/δ) → 0` as `δ ↓ 0`, for every real `p`. -/
theorem tendsto_rpow_neg_mul_budget (p : ℝ) :
    Tendsto (fun δ => δ ^ (-p) * budget δ) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p 1 one_pos).comp
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  simp [budget, hδ, Real.inv_rpow hδ.le, Real.rpow_neg hδ.le]

/-- The function `ψ₀` of (6.32): `envelope + budget` up to the threshold `δ₁`, and `1` beyond. -/
noncomputable def cutoff (C : ℕ → ℝ) (A β δ₁ δ : ℝ) : ℝ :=
  if δ ≤ δ₁ then envelope C A β δ + budget δ else 1

theorem cutoff_of_le {C : ℕ → ℝ} {A β δ₁ δ : ℝ} (hδ : δ ≤ δ₁) :
    cutoff C A β δ₁ δ = envelope C A β δ + budget δ := by simp [cutoff, hδ]

theorem cutoff_of_lt {C : ℕ → ℝ} {A β δ₁ δ : ℝ} (hδ : δ₁ < δ) : cutoff C A β δ₁ δ = 1 :=
  by simp [cutoff, not_le.mpr hδ]

/-- **`ψ₀` is a superpolynomial function in the sense of (6.32)**: nonnegative on `[0, ∞)`, zero at `0`, and
`δ^{-p} ψ₀(δ) → 0` as `δ ↓ 0` for every `p > 0`. -/
theorem cutoff_superpoly (C : ℕ → ℝ) {A β δ₁ : ℝ} (hA : 0 ≤ A) (hβ : 0 < β) (hδ₁ : 0 < δ₁) :
    (∀ δ : ℝ, 0 ≤ δ → 0 ≤ cutoff C A β δ₁ δ) ∧ cutoff C A β δ₁ 0 = 0 ∧
      ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * cutoff C A β δ₁ δ) (𝓝[>] 0) (𝓝 0) := by
  refine ⟨fun δ hδ => ?_, ?_, fun p _ => ?_⟩
  · unfold cutoff
    split_ifs
    · exact add_nonneg (envelope_nonneg C hA hδ) (budget_nonneg δ)
    · exact zero_le_one
  · rw [cutoff_of_le hδ₁.le, envelope_zero C hA hβ, budget_zero, add_zero]
  · have hsum := (tendsto_rpow_neg_mul_envelope C hA hβ p).add (tendsto_rpow_neg_mul_budget p)
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ₁] with δ hδ
    rw [cutoff_of_le hδ.2.le, mul_add]

/-- **The bound (6.32) below the threshold**: if `μ ≤ ν + κ` with `κ ≤ budget δ`, and `ν ≤ C_p r^p` for every
`p` with `0 ≤ r ≤ A δ^β`, then `μ ≤ ψ₀(δ)` for `0 ≤ δ ≤ δ₁`. -/
theorem le_ofReal_cutoff {C : ℕ → ℝ} {A β δ₁ δ r κ : ℝ} {μ ν : ℝ≥0∞} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hδ₁ : δ ≤ δ₁) (hr : 0 ≤ r) (hrA : r ≤ A * δ ^ β) (hκ : κ ≤ budget δ)
    (hν : ∀ p : ℕ, ν ≤ ENNReal.ofReal (C p * r ^ p)) (hμ : μ ≤ ν + ENNReal.ofReal κ) :
    μ ≤ ENNReal.ofReal (cutoff C A β δ₁ δ) := by
  rw [cutoff_of_le hδ₁, ENNReal.ofReal_add (envelope_nonneg C hA hδ) (budget_nonneg δ)]
  exact hμ.trans (add_le_add (le_ofReal_envelope hA hδ hr hrA hν) (ENNReal.ofReal_le_ofReal hκ))

end MatedCRT.SuperpolyEnvelope
