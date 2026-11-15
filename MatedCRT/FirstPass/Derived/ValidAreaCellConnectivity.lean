import MatedCRT.FirstPass.Derived.AreaCellPeanosphereConnectivity
import MatedCRT.FirstPass.Derived.ValidPeanosphere

/-! # Area-cell connectivity in a valid environment -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic

/-- A single almost-sure event gives connectivity for all positive meshes, provided the
area-parametrization, local-finiteness and matching-embedding witnesses are supplied. -/
theorem MatedCRTEnv.IsValid.ae_areaCellConfig_connected
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (ε : ℝ) (hε : 0 < ε)
      (h : IsAreaParametrized (S.μ ω) (S.η ω))
      (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
      (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ)),
      H.cell = cell ε (S.η ω) →
        (∀ U : Set ReflectedGMS.Plane, IsConnected U →
          ((areaCellConfig h hε (S.mult ε ω)).inducedGraph U).Connected) ∧
        (areaCellConfig h hε (S.mult ε ω)).LineConnected := by
  obtain ⟨η', hη', hP, -⟩ := MatedCRTEnv.IsValid.exists_curve_peanosphere S hS
  filter_upwards [hη', hP] with ω hη hP ε hε h hlf H hH
  exact ⟨fun U hU => S.areaCellConfig_inducedGraph_connected_of_peanosphere
    ω hε h hlf H hH (η' ω) hη hP U hU,
    S.areaCellConfig_lineConnected_of_peanosphere ω hε h hlf H hH (η' ω) hη hP⟩

end MatedCRT
