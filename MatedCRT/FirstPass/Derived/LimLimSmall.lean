import MatedCRT.FirstPass.S3i.GoodEvent

/-!
# Failure probabilities that vanish as `ε → 0` and then `δ → 0`

Many statements of Berestycki–Gwynne (2020) hold "with probability tending to `1` as `ε → 0` and then
`δ → 0`".  `LimLimSmall P F` says that the failure probability `P[F δ ε]` has this property: for every
`θ > 0` there is `δ₀ > 0` such that for each `δ ∈ (0, δ₀)` there is `ε₀ > 0` with `P[F δ ε] ≤ θ` for all
`ε ∈ (0, ε₀)`.  The notion is monotone, stable under finite unions, holds for the failure of every event
that has polynomially high probability for each fixed `δ`, and follows from the `limsup` form
(`limsup_{ε → 0} P[F δ ε] → 0` as `δ → 0`).
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The failure probability `P[F δ ε]` tends to `0` as `ε → 0` and then `δ → 0`. -/
def LimLimSmall {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ℝ → ℝ → Set Ω) : Prop :=
  ∀ θ : ℝ, 0 < θ → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → P (F δ ε) ≤ ENNReal.ofReal θ

namespace LimLimSmall

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F G : ℝ → ℝ → Set Ω}

/-- Monotonicity: a smaller failure event is also negligible. -/
theorem mono (hFG : ∀ δ ε, F δ ε ⊆ G δ ε) (hG : LimLimSmall P G) : LimLimSmall P F := by
  intro θ hθ
  obtain ⟨δ₀, hδ₀, h⟩ := hG θ hθ
  refine ⟨δ₀, hδ₀, fun δ hδ hδδ₀ => ?_⟩
  obtain ⟨ε₀, hε₀, h'⟩ := h δ hδ hδδ₀
  exact ⟨ε₀, hε₀, fun ε hε hεε₀ => (measure_mono (hFG δ ε)).trans (h' ε hε hεε₀)⟩

/-- Finite unions: the union of two negligible failure events is negligible. -/
theorem union (hF : LimLimSmall P F) (hG : LimLimSmall P G) :
    LimLimSmall P (fun δ ε => F δ ε ∪ G δ ε) := by
  intro θ hθ
  obtain ⟨δ₁, hδ₁, h₁⟩ := hF (θ / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hG (θ / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδlt => ?_⟩
  obtain ⟨ε₁, hε₁, h₁'⟩ := h₁ δ hδ (lt_of_lt_of_le hδlt (min_le_left _ _))
  obtain ⟨ε₂, hε₂, h₂'⟩ := h₂ δ hδ (lt_of_lt_of_le hδlt (min_le_right _ _))
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hεlt => ?_⟩
  calc P (F δ ε ∪ G δ ε) ≤ P (F δ ε) + P (G δ ε) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
        add_le_add (h₁' ε hε (lt_of_lt_of_le hεlt (min_le_left _ _)))
          (h₂' ε hε (lt_of_lt_of_le hεlt (min_le_right _ _)))
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- An event with polynomially high probability for each fixed `δ ∈ (0, 1)` has a negligible failure
event. -/
theorem of_polyHighProb {E : ℝ → ℝ → Set Ω} (hE : ∀ δ : ℝ, 0 < δ → δ < 1 → HarmonicBalls.PolyHighProb P (E δ)) :
    LimLimSmall P (fun δ ε => (E δ ε)ᶜ) := by
  intro θ hθ
  refine ⟨1, one_pos, fun δ hδ hδ1 => ?_⟩
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := hE δ hδ hδ1
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hpos : 0 < θ / (max C 0 + 1) := by positivity
  refine ⟨min r₀ ((θ / (max C 0 + 1)) ^ p⁻¹), lt_min hr₀ (Real.rpow_pos_of_pos hpos _),
    fun ε hε hεlt => ?_⟩
  have hpow : ε ^ p < θ / (max C 0 + 1) :=
    calc ε ^ p < ((θ / (max C 0 + 1)) ^ p⁻¹) ^ p :=
          Real.rpow_lt_rpow hε.le (lt_of_lt_of_le hεlt (min_le_right _ _)) hp
      _ = θ / (max C 0 + 1) := Real.rpow_inv_rpow hpos.le hp.ne'
  have hle : C * ε ^ p ≤ θ :=
    calc C * ε ^ p ≤ max C 0 * ε ^ p :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hε.le p)
      _ ≤ max C 0 * (θ / (max C 0 + 1)) := mul_le_mul_of_nonneg_left hpow.le hC
      _ ≤ θ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [hθ.le]
  exact (hb ε hε (lt_of_lt_of_le hεlt (min_le_left _ _))).trans (ENNReal.ofReal_le_ofReal hle)

/-- The `limsup` form: if `limsup_{ε → 0} P[F δ ε] → 0` as `δ → 0`, then `F` is negligible. -/
theorem of_tendsto_limsup
    (h : Tendsto (fun δ => limsup (fun ε => P (F δ ε)) (𝓝[>] (0 : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    LimLimSmall P F := by
  intro θ hθ
  have hδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), limsup (fun ε => P (F δ ε)) (𝓝[>] (0 : ℝ)) < ENNReal.ofReal θ := by
    have hlt : (0 : ℝ≥0∞) < ENNReal.ofReal θ := ENNReal.ofReal_pos.2 hθ
    exact h.eventually (gt_mem_nhds hlt)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hδ
  obtain ⟨δ₀, hδ₀, hδ'⟩ := hδ
  refine ⟨δ₀, hδ₀, fun δ hδpos hδlt => ?_⟩
  have hlim := hδ' (y := δ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hδpos]; exact hδlt) hδpos
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P (F δ ε) < ENNReal.ofReal θ := eventually_lt_of_limsup_lt hlim
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε₀, hε₀, hε'⟩ := hev
  refine ⟨ε₀, hε₀, fun ε hε hεlt => (hε' (y := ε) ?_ hε).le⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hε]
  exact hεlt

/-- Failure events whose probability tends to `0` as `ε → 0` for every fixed `δ ∈ (0, 1)` are
negligible. -/
theorem of_tendsto_eps
    (h : ∀ δ : ℝ, 0 < δ → δ < 1 → Tendsto (fun ε => P (F δ ε)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    LimLimSmall P F := by
  intro θ hθ
  refine ⟨1, one_pos, fun δ hδ hδ1 => ?_⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P (F δ ε) < ENNReal.ofReal θ :=
    (h δ hδ hδ1).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε₀, hε₀, hε'⟩ := hev
  refine ⟨ε₀, hε₀, fun ε hε hεlt => (hε' (y := ε) ?_ hε).le⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hε]
  exact hεlt

/-- Reparametrisation of the scale: if `φ δ > 0` tends to `0` as `δ → 0`, a negligible failure event
stays negligible when `δ` is replaced by `φ δ`. -/
theorem comp_delta (hF : LimLimSmall P F) {φ : ℝ → ℝ} (hφ0 : ∀ δ : ℝ, 0 < δ → 0 < φ δ)
    (hφ : Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 0)) : LimLimSmall P (fun δ ε => F (φ δ) ε) := by
  intro θ hθ
  obtain ⟨δ₀, hδ₀, h⟩ := hF θ hθ
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), φ δ < δ₀ := hφ.eventually (gt_mem_nhds hδ₀)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hev
  refine ⟨δ₁, hδ₁, fun δ hδ hδlt => h (φ δ) (hφ0 δ hδ) ?_⟩
  exact hδ₁' (y := δ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; exact hδlt) hδ

end LimLimSmall
end MatedCRT
