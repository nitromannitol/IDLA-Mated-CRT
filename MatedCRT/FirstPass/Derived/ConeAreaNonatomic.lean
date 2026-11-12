import MatedCRT.Proofs.Infra.Setting

/-!
# The area measure of a valid environment has no atoms

If `η` is a space-filling curve parametrized by `μ`-area (`IsAreaParametrized μ η`), then `μ` has no atoms: every
point is `z = η(t)` for some `t`, and `μ{z} ≤ μ(η([t, t + u])) = u` for every `u > 0`. No estimate on the field near
its singularities is used. In a valid environment the curve `η` is parametrized by the area measure `μ_h` almost
surely, so `μ_h` has no atoms almost surely.

## Main results

* `MatedCRT.IsAreaParametrized.measure_singleton_eq_zero`, `MatedCRT.IsAreaParametrized.nullSingletonClass`.
* `MatedCRT.MatedCRTEnv.IsValid.ae_nullSingletonClass`: almost surely the area measure of a valid environment has no atoms.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

/-- A measure along which a space-filling curve is parametrized by area gives zero mass to every point. -/
theorem IsAreaParametrized.measure_singleton_eq_zero {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    (z : ℂ) : μ {z} = 0 := by
  obtain ⟨t, rfl⟩ := h.2.2.1 z
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  have hsub : {η t} ⊆ η '' Icc t (t + ε) :=
    singleton_subset_iff.2 ⟨t, ⟨le_rfl, le_add_of_nonneg_right ε.2⟩, rfl⟩
  have hm := (measure_mono hsub).trans_eq (h.2.2.2 t (t + ε) (by simpa using hε))
  simpa only [add_sub_cancel_left, ENNReal.ofReal_coe_nnreal, zero_add] using hm

/-- A measure along which a space-filling curve is parametrized by area has no atoms. -/
theorem IsAreaParametrized.nullSingletonClass {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η) : NullSingletonClass μ :=
  ⟨h.measure_singleton_eq_zero⟩

/-- **The area measure of a valid environment has no atoms**, almost surely. -/
theorem MatedCRTEnv.IsValid.ae_nullSingletonClass {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, NullSingletonClass (S.μ ω) :=
  hS.isAreaParametrized.mono fun _ h => h.nullSingletonClass

/-- Almost surely, the area measure of a valid environment gives zero mass to every point. -/
theorem MatedCRTEnv.IsValid.ae_forall_measure_singleton_eq_zero {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ z, S.μ ω {z} = 0 :=
  hS.isAreaParametrized.mono fun _ h => h.measure_singleton_eq_zero

end MatedCRT
