import MatedCRT.Defs.Setting
import MatedCRT.Defs.Map

/-!
# Elementary facts on the random setting

* a valid environment carries the field of the `γ`-quantum cone and its LQG measure (`IsConeField`);
* the random variable `𝓜(D)` of eq:largest-exit-time-rv is nondecreasing in `D`;
* the interior cell vertices `V^ε(D) ∖ V^ε(∂D)` lie in `V^ε(D)`;
* events with polynomially high probability (`HarmonicBalls.PolyHighProb`): intersection with an almost sure event,
  union bounds, and the elementary limits `K (c r)^p → 0`, `r^α < s` for small `r`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- A valid environment carries the field of the `γ`-quantum cone and its `γ`-LQG measure. -/
theorem MatedCRTEnv.IsValid.isConeField {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) : IsConeField γ S.P S.hC S.hcirc S.μ := by
  unfold IsConeField
  exact ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩

/-- `𝓜(D) = sup_{z ∈ D} ∫_D (log (1/|z - w|) + 1) dμ(w)` is nondecreasing in `D`. -/
theorem largestExitTimeRV_mono (μ : Measure ℂ) {D D' : Set ℂ} (h : D ⊆ D') :
    largestExitTimeRV μ D ≤ largestExitTimeRV μ D' := by
  unfold largestExitTimeRV
  exact iSup₂_le fun z hz => le_iSup₂_of_le z (h hz) (lintegral_mono_set h)

/-- The interior cell vertices `V^ε(D) ∖ V^ε(∂D)` form a subset of `V^ε(D)`. -/
theorem interiorCellVertices_subset (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) :
    interiorCellVertices ε η D ⊆ cellVertices ε η D := by
  unfold interiorCellVertices
  exact Set.sdiff_subset

/-- An event containing, for small `r`, the intersection of an event with polynomially high probability and an almost
sure event has polynomially high probability. -/
theorem polyHighProb_of_inter_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    {G : Set Ω} (hE : PolyHighProb P E) (hG : P Gᶜ = 0) {r₁ : ℝ} (hr₁ : 0 < r₁)
    (hEF : ∀ r, 0 < r → r < r₁ → E r ∩ G ⊆ F r) : PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, h⟩ := hE
  refine ⟨p, hp, C, min r₀ r₁, lt_min hr₀ hr₁, fun r hr hrlt => ?_⟩
  calc P (F r)ᶜ ≤ P ((E r)ᶜ ∪ Gᶜ) := by
        rw [← Set.compl_inter]
        exact measure_mono (Set.compl_subset_compl.mpr (hEF r hr (hrlt.trans_le (min_le_right _ _))))
    _ ≤ P (E r)ᶜ + P Gᶜ := measure_union_le _ _
    _ = P (E r)ᶜ := by rw [hG, add_zero]
    _ ≤ ENNReal.ofReal (C * r ^ p) := h r hr (hrlt.trans_le (min_le_left _ _))

/-- Union bound: if `p` holds on `A ∩ B`, then `P[¬ p] ≤ P[Aᶜ] + P[Bᶜ]`. -/
theorem measure_setOf_not_le_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A B : Set Ω}
    {p : Ω → Prop} {a b : ℝ≥0∞} (hA : P Aᶜ ≤ a) (hB : P Bᶜ ≤ b) (h : ∀ ω ∈ A, ω ∈ B → p ω) :
    P {ω | ¬ p ω} ≤ a + b := by
  calc P {ω | ¬ p ω} ≤ P (Aᶜ ∪ Bᶜ) := by
        refine measure_mono fun ω hω => ?_
        by_cases hωA : ω ∈ A
        · by_cases hωB : ω ∈ B
          · exact absurd (h ω hωA hωB) hω
          · exact Set.mem_union_right _ hωB
        · exact Set.mem_union_left _ hωA
    _ ≤ P Aᶜ + P Bᶜ := measure_union_le _ _
    _ ≤ a + b := add_le_add hA hB

/-- `K (c r)^p → 0` as `r → 0⁺`, for `p > 0`. -/
theorem tendsto_ofReal_mul_rpow (K c p : ℝ) (hp : 0 < p) :
    Tendsto (fun r : ℝ => ENNReal.ofReal (K * (c * r) ^ p)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => c * r) (𝓝 0) (𝓝 (c * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun r : ℝ => K * (c * r) ^ p) (𝓝[>] 0) (𝓝 (K * (0 : ℝ) ^ p)) :=
    tendsto_const_nhds.mul (h1.rpow_const (Or.inr hp.le))
  rw [Real.zero_rpow hp.ne', mul_zero] at h2
  simpa using ENNReal.tendsto_ofReal h2

/-- For `α, s > 0`, `r^α < s` for all small `r > 0`. -/
theorem exists_pos_rpow_lt {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    ∃ r₁ > 0, ∀ ε : ℝ, 0 < ε → ε < r₁ → ε ^ α < s :=
  ⟨s ^ α⁻¹, Real.rpow_pos_of_pos hs _, fun ε hε hεr => by
    calc ε ^ α < (s ^ α⁻¹) ^ α := Real.rpow_lt_rpow hε.le hεr hα
      _ = s := Real.rpow_inv_rpow hs.le hα.ne'⟩

end MatedCRT
