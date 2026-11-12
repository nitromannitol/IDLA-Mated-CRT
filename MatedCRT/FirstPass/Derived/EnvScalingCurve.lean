import MatedCRT.External.SLE

/-!
# The rescaled space-filling SLE curve

Under the scaling of the environment (eq:scale-invariance-of-field-and-eta of the paper, lines
3286-3293) the space-filling curve becomes `ηᵇ(s) = R⁻¹ η(b s)`, with `R > 0` a function of the
field and `b > 0`. This file shows that `ηᵇ` is again a whole-plane space-filling SLE_κ independent
of any smaller σ-algebra `𝓖 ≤ 𝓕`, for every model `𝒮` closed under scaling by a positive
`𝓕`-measurable factor (`SLEScaleInvarianceInput`, eq:eta-scale-invariant), under increasing
reparametrization (`SLEReparametrizationInput`) and under restriction of the independent
σ-algebra (`SLEIndepMonoInput`).
-/

namespace MatedCRT

open MeasureTheory

/-- **The rescaled curve `s ↦ R⁻¹ η(b s)` is a whole-plane space-filling SLE_κ**: for a model closed
under scaling, increasing reparametrization and restriction of the independent σ-algebra, if `η`
is a whole-plane space-filling SLE_κ (`κ > 4`) independent of `𝓕`, `b > 0`, and `R` is a positive
`𝓕`-measurable random factor, then `s ↦ R⁻¹ η(b s)` is a whole-plane space-filling SLE_κ
independent of every `𝓖 ≤ 𝓕`. -/
theorem isSLE_rescale {𝒮 : SpaceFillingSLEModel} (hSc : SLEScaleInvarianceInput 𝒮)
    (hRe : SLEReparametrizationInput 𝒮) (hMo : SLEIndepMonoInput 𝒮)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ} {𝓕 𝓖 : MeasurableSpace Ω} {κ : ℝ}
    {η : Ω → ℝ → ℂ} (hκ : 4 < κ) (hη : @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 κ η)
    {b : ℝ} (hb : 0 < b) {R : Ω → ℝ} (hR : Measurable[𝓕] R) (hRpos : ∀ ω, 0 < R ω)
    (h𝓖 : 𝓖 ≤ 𝓕) :
    @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓖 κ
      (fun ω s => ((R ω : ℝ) : ℂ)⁻¹ * η ω (b * s)) := by
  -- time change `s ↦ b s`
  have h1 : @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 κ (fun ω s => η ω (b * s)) := by
    refine hRe Ω mΩ P 𝓕 κ η _ hκ hη (Filter.Eventually.of_forall fun ω => ?_)
    refine ⟨Homeomorph.mulLeft₀ b hb.ne', fun x y hxy => ?_, ?_⟩
    · simpa using mul_lt_mul_of_pos_left hxy hb
    · funext s
      simp
  -- spatial scaling by the `𝓕`-measurable factor `R⁻¹`
  have h2 := hSc Ω mΩ P 𝓕 κ _ hκ h1 (fun ω => (R ω)⁻¹) hR.inv (fun ω => inv_pos.mpr (hRpos ω))
  have h3 : (fun ω s => (((R ω)⁻¹ : ℝ) : ℂ) * η ω (b * s)) =
      fun ω s => ((R ω : ℝ) : ℂ)⁻¹ * η ω (b * s) := by
    funext ω s
    rw [Complex.ofReal_inv]
  rw [h3] at h2
  -- restriction of the independent σ-algebra
  exact hMo Ω mΩ P 𝓕 𝓖 κ _ hκ h2 h𝓖

end MatedCRT
