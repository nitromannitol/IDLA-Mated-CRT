import MatedCRT.FirstPass.Derived.AreaCellEnumerationMeasurable
import LatticeProb.Prob.EnumeratedCellCodeAEModification

/-! # Almost-everywhere measurability of area-cell codes -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- An area-cell realization has an almost-everywhere measurable canonical code. -/
theorem MatedCRTEnv.IsValid.areaCellConfig_code_aemeasurable
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (H : Ω → CellConfig)
    (hH : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      H ω = areaCellConfig h hε (S.mult ε ω)) :
    AEMeasurable (fun ω => (H ω).code) S.P := by
  obtain ⟨C, hC, hgood, hc⟩ :=
    hS.areaCellConfig_measurable_enumeration S hε H hH
  exact LatticeProb.aemeasurable_enumeratedCell_code_of_ae S.P H C hgood
    (fun k => (hC k).aemeasurable) hc

end MatedCRT
