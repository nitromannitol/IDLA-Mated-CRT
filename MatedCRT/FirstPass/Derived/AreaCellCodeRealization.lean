import MatedCRT.FirstPass.Derived.AreaCellGoodCode

/-! # Measurable codes for area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- A valid environment has a measurable good-code version for its fixed-mesh
area-cell configuration. -/
theorem MatedCRTEnv.IsValid.exists_areaCell_goodCode_version
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : Ω → ReflectedGMS.Code.RawCode, Measurable Z ∧
      (∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
        Z ω = (areaCellConfig h hε (S.mult ε ω)).code ∧ Z ω ∈ goodCodes) := by
  classical
  let H : Ω → CellConfig := fun ω =>
    if h : IsAreaParametrized (S.μ ω) (S.η ω) then
      areaCellConfig h hε (S.mult ε ω)
    else ⟨∅, fun _ _ => 0⟩
  have hH : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      H ω = areaCellConfig h hε (S.mult ε ω) := by
    filter_upwards [hS.isAreaParametrized] with ω hω
    exact ⟨hω, by simp [H, hω]⟩
  obtain ⟨Z, hZ, hgood⟩ := hS.exists_measurable_areaCell_goodCode S hε H hH
  refine ⟨Z, hZ, ?_⟩
  filter_upwards [hH, hgood] with ω ⟨h, hh⟩ ⟨heq, hg⟩
  exact ⟨h, heq.trans (congrArg CellConfig.code hh), hg⟩

end MatedCRT
