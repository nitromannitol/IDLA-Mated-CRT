import MatedCRT.FirstPass.Derived.AreaCellCodeAEMeasurable
import MatedCRT.FirstPass.Derived.ValidAreaCellConfiguration
import LatticeProb.Bonanno.ReflectedGMS.GMS.ValidCodeSet

/-! # Measurable codes for area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- A fixed-mesh area-cell configuration has a measurable code version which is
almost surely a good code and agrees with the canonical code. -/
theorem MatedCRTEnv.IsValid.exists_measurable_areaCell_goodCode
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (H : Ω → CellConfig)
    (hH : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      H ω = areaCellConfig h hε (S.mult ε ω)) :
    ∃ Z : Ω → ReflectedGMS.Code.RawCode, Measurable Z ∧
      (∀ᵐ ω ∂S.P, Z ω = (H ω).code ∧ Z ω ∈ goodCodes) := by
  let hc := hS.areaCellConfig_code_aemeasurable S hε H hH
  refine ⟨hc.mk _, hc.measurable_mk, ?_⟩
  filter_upwards [hc.ae_eq_mk, hH, hS.ae_areaCellConfig_isCellConfiguration S hε] with ω hz hh hg
  obtain ⟨h, heq⟩ := hh
  obtain ⟨h', hvalid, _, hline⟩ := hg
  have hgood : (H ω).code ∈ goodCodes := by
    rw [heq]
    exact code_mem_goodCodes hvalid hline
  exact ⟨hz.symm, hz.symm ▸ hgood⟩

end MatedCRT
