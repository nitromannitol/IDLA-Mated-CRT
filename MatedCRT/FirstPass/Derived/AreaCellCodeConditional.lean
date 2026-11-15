import MatedCRT.FirstPass.Derived.AreaCellEnumerationMeasurable
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingDef

/-! # Conditional measurability of area-cell codes -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- An area-cell realization has an almost-everywhere measurable code, given
    the corresponding theorem for almost-everywhere measurable enumerations. -/
theorem MatedCRTEnv.IsValid.areaCellConfig_code_aemeasurable_of_enumeration
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (H : Ω → CellConfig)
    (hH : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      H ω = areaCellConfig h hε (S.mult ε ω))
    (hcode : ∀ {α ι : Type} [MeasurableSpace α] [Countable ι]
      (μ : Measure α) (G : α → CellConfig) (C : ι → α → Cell),
      (∀ᵐ ω ∂μ, (G ω).IsCellConfiguration ∧
        (G ω).cells = Set.range (fun i => C i ω)) →
      (∀ i, AEMeasurable (C i) μ) →
      (∀ i j, AEMeasurable (fun ω => (G ω).c (C i ω) (C j ω)) μ) →
      AEMeasurable (fun ω => (G ω).code) μ) :
    AEMeasurable (fun ω => (H ω).code) S.P := by
  obtain ⟨C, hC, hgood, hc⟩ :=
    hS.areaCellConfig_measurable_enumeration S hε H hH
  exact hcode S.P H C hgood (fun k => (hC k).aemeasurable) hc

end MatedCRT
