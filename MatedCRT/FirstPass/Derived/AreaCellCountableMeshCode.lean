import MatedCRT.FirstPass.Derived.AreaCellCodeRealization

/-! # Measurable area-cell codes at countably many meshes -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- For countably many positive meshes, the area-cell codes admit a jointly
measurable version which is simultaneously good and agrees with the original
codes almost surely. -/
theorem MatedCRTEnv.IsValid.exists_countable_areaCell_goodCode_version
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ Z : Ω → ι → ReflectedGMS.Code.RawCode, Measurable Z ∧
      (∀ᵐ ω ∂S.P, ∀ i, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
        Z ω i = (areaCellConfig h (hε i) (S.mult (ε i) ω)).code ∧
          Z ω i ∈ goodCodes) := by
  classical
  have hex := fun i => hS.exists_areaCell_goodCode_version S (hε i)
  choose Z hZ hgood using hex
  refine ⟨fun ω i => Z i ω, Measurable.of_eval hZ, ?_⟩
  exact ae_all_iff.mpr hgood

end MatedCRT
