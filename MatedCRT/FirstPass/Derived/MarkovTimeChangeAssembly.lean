import MatedCRT.FirstPass.Derived.PCAFStartUpgrade
import MatedCRT.FirstPass.Derived.RevuzScaling
import MatedCRT.FirstPass.Derived.RevuzKernel

/-!
# Two good clocks with a common invariant measure differ by a constant factor

Abstract assembly of the identification of the time change of planar Brownian motion by a positive continuous
additive functional (Berestycki–Gwynne (2020), Proposition 7.10).  Given two PCAFs `A₁, A₂` of planar Brownian
motion with good clocks and a nonzero locally finite measure `μ` that is invariant for both time changes, the
three Revuz inputs (`RevuzUniquenessInput`, `RevuzInvariantInput`, `TimeChangeInvariantUniqueInput`) show that
`A₁ = c A₂` up to indistinguishability from every starting point, for a deterministic constant `c > 0`
independent of the starting point, and hence `B ∘ τ¹_u = B ∘ τ²_{u / c}`.

* `clockInverse_const_mul`: `τ_u(c A) = τ_{u / c}(A)`;
* `eq_smul_of_smul_eq`: from `a μ = b ν` with `a ≠ 0` one gets `μ = (a⁻¹ b) ν`;
* `exists_const_mul_of_invariant`: the constant `c` with `A₁ = c A₂` from every starting point;
* `ae_eval_clockInverse_eq_of_invariant`: the identification of the time-changed paths.
-/

open MeasureTheory MarkovProcess Filter
open scoped NNReal ENNReal

namespace MatedCRT

/-- The right inverse of the clock `c A` is the right inverse of `A` at the rescaled level `u / c`. -/
theorem clockInverse_const_mul {c : ℝ≥0} (hc : c ≠ 0) (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u : ℝ≥0)
    (ω : ContinuousPath ℂ) :
    clockInverse (fun t ω => c * A t ω) u ω = clockInverse A (u / c) ω := by
  unfold clockInverse
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq]
  rw [div_lt_iff₀ (pos_iff_ne_zero.2 hc), mul_comm]

/-- If `a μ = b ν` with `a ≠ 0` then `μ = (a⁻¹ b) ν` (scalars in `ℝ≥0`, measures over `ℝ≥0∞`). -/
theorem eq_smul_of_smul_eq {μ ν : Measure ℂ} {a b : ℝ≥0} (ha : a ≠ 0)
    (h : (a : ℝ≥0∞) • μ = (b : ℝ≥0∞) • ν) : μ = ((a⁻¹ * b : ℝ≥0) : ℝ≥0∞) • ν := by
  have h1 : μ = ((a⁻¹ : ℝ≥0) : ℝ≥0∞) • ((a : ℝ≥0∞) • μ) := by
    rw [smul_smul, ← ENNReal.coe_mul, inv_mul_cancel₀ ha, ENNReal.coe_one, one_smul]
  rw [h1, h, smul_smul, ← ENNReal.coe_mul]

/-- **Two good clocks with a common invariant measure are proportional.**  Let `A₁, A₂` be PCAFs of planar
Brownian motion with good clocks and `μ` a nonzero locally finite measure invariant for both time changes.  Under
the three Revuz inputs there is a constant `c > 0` such that, for every starting point, almost surely
`A₁ t = c A₂ t` for all `t`. -/
theorem exists_const_mul_of_invariant (hRU : RevuzUniquenessInput) (hRI : RevuzInvariantInput)
    (hTU : TimeChangeInvariantUniqueInput) {A₁ A₂ : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA₁ : IsPCAF planarLaw A₁) (hA₂ : IsPCAF planarLaw A₂) (hG₁ : GoodClock planarLaw A₁)
    (hG₂ : GoodClock planarLaw A₂) {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (h₁ : IsInvTC planarLaw A₁ μ) (h₂ : IsInvTC planarLaw A₂ μ) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, ∀ᵐ ω ∂planarLaw z, ∀ t, A₁ t ω = c * A₂ t ω := by
  have : SigmaFinite μ := inferInstance
  obtain ⟨c₁, hc₁⟩ := hTU A₁ hA₁ hG₁ μ inferInstance h₁
  obtain ⟨c₂, hc₂⟩ := hTU A₂ hA₂ hG₂ μ inferInstance h₂
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    apply hμ
    rw [hc₁]
    simp
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    apply hμ
    rw [hc₂]
    simp
  have hR : revuz planarLaw A₁ = ((c₁⁻¹ * c₂ : ℝ≥0) : ℝ≥0∞) • revuz planarLaw A₂ :=
    eq_smul_of_smul_eq hc₁0 (hc₁.symm.trans hc₂)
  have hc0 : c₁⁻¹ * c₂ ≠ 0 := mul_ne_zero (inv_ne_zero hc₁0) hc₂0
  have hscale := revuz_const_mul hc0 measurable_planarLaw
    (measurable_occupationMeasure_regularize hA₂.meas)
  have hae := hRU A₁ (fun t ω => (c₁⁻¹ * c₂) * A₂ t ω) hA₁ (hA₂.const_mul _)
    (hRI A₁ hA₁ hG₁).1 (hR.trans hscale.symm)
  exact ⟨c₁⁻¹ * c₂, hc0, fun z => ae_start_upgrade hA₁ (hA₂.const_mul _) hae z⟩

/-- **The identification of the time-changed paths** (Berestycki–Gwynne, Proposition 7.10, abstract form): under
the hypotheses of `exists_const_mul_of_invariant` there is a constant `c > 0` such that, from every starting
point, almost surely `B (τ¹_u) = B (τ²_{u / c})` for all `u`. -/
theorem ae_eval_clockInverse_eq_of_invariant (hRU : RevuzUniquenessInput) (hRI : RevuzInvariantInput)
    (hTU : TimeChangeInvariantUniqueInput) {A₁ A₂ : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA₁ : IsPCAF planarLaw A₁) (hA₂ : IsPCAF planarLaw A₂) (hG₁ : GoodClock planarLaw A₁)
    (hG₂ : GoodClock planarLaw A₂) {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (h₁ : IsInvTC planarLaw A₁ μ) (h₂ : IsInvTC planarLaw A₂ μ) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, ∀ᵐ ω ∂planarLaw z, ∀ u,
      ω (clockInverse A₁ u ω) = ω (clockInverse A₂ (u / c) ω) := by
  obtain ⟨c, hc, h⟩ := exists_const_mul_of_invariant hRU hRI hTU hA₁ hA₂ hG₁ hG₂ hμ h₁ h₂
  refine ⟨c, hc, fun z => ?_⟩
  filter_upwards [h z] with ω hω u
  have : clockInverse A₁ u ω = clockInverse (fun t ω => c * A₂ t ω) u ω := by
    simp only [clockInverse, hω]
  rw [this, clockInverse_const_mul hc]

end MatedCRT
