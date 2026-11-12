import MatedCRT.Defs.Setting
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime

/-!
# Area parametrization under the scaling of the environment

The space-filling curve of a mated-CRT environment is parametrized by LQG area: `η(0) = 0` and
`μ_h(η([a, a'])) = a' - a` (`IsAreaParametrized`). Under the scaling of the environment
(eq:scale-invariance-of-field-and-eta of the paper; Duplantier-Miller-Sheffield, *Mating of trees*,
Proposition 4.13(i)) the curve becomes `ηᵇ(s) = R⁻¹ η(b s)` and the measure becomes
`A ↦ b⁻¹ μ(R A)` (`rescaledMeasure μ R b`). This deterministic identity says that `ηᵇ` is again
parametrized by the area of the rescaled measure, for every `R > 0` and `b > 0`.
-/

namespace MatedCRT

open MeasureTheory Set

/-- **The area parametrization is preserved by the scaling of the environment**: if `η` is
parametrized by `μ`-area, then `s ↦ R⁻¹ η(b s)` is parametrized by the area of the rescaled measure
`A ↦ b⁻¹ μ(R A)`, for all `R > 0` and `b > 0`. -/
theorem IsAreaParametrized.rescale {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {R b : ℝ} (hR : 0 < R) (hb : 0 < b) :
    IsAreaParametrized (rescaledMeasure μ R b) (fun s => (R : ℂ)⁻¹ * η (b * s)) := by
  obtain ⟨hc, h0, hs, hm⟩ := h
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hcont : Continuous fun s : ℝ => (R : ℂ)⁻¹ * η (b * s) :=
    continuous_const.mul (hc.comp (continuous_const.mul continuous_id))
  refine ⟨hcont, ?_, ?_, ?_⟩
  · simp [h0]
  · intro w
    obtain ⟨t, ht⟩ := hs ((R : ℂ) * w)
    refine ⟨t / b, ?_⟩
    show (R : ℂ)⁻¹ * η (b * (t / b)) = w
    rw [mul_div_cancel₀ t hb.ne', ht, ← mul_assoc, inv_mul_cancel₀ hR', one_mul]
  · intro a a' haa'
    have hpre : (fun x : ℂ => (R : ℂ)⁻¹ * x) ⁻¹'
        ((fun s : ℝ => (R : ℂ)⁻¹ * η (b * s)) '' Icc a a') = η '' Icc (b * a) (b * a') := by
      ext x
      simp only [mem_preimage, mem_image, mem_Icc]
      constructor
      · rintro ⟨s, ⟨hs1, hs2⟩, hsx⟩
        exact ⟨b * s, ⟨mul_le_mul_of_nonneg_left hs1 hb.le, mul_le_mul_of_nonneg_left hs2 hb.le⟩,
          mul_left_cancel₀ (inv_ne_zero hR') hsx⟩
      · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
        refine ⟨t / b, ⟨?_, ?_⟩, ?_⟩
        · rw [le_div_iff₀ hb, mul_comm]; exact ht1
        · rw [div_le_iff₀ hb, mul_comm]; exact ht2
        · rw [mul_div_cancel₀ t hb.ne']
    have hmeas : MeasurableSet ((fun s : ℝ => (R : ℂ)⁻¹ * η (b * s)) '' Icc a a') :=
      (isCompact_Icc.image hcont).isClosed.measurableSet
    have hab : b * a < b * a' := mul_lt_mul_of_pos_left haa' hb
    unfold rescaledMeasure
    rw [Measure.smul_apply,
      Measure.map_apply (by fun_prop : Measurable fun x : ℂ => (R : ℂ)⁻¹ * x) hmeas, hpre, hm _ _ hab,
      smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hb.le)]
    congr 1
    field_simp

end MatedCRT
