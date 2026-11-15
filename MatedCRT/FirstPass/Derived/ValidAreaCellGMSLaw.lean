import MatedCRT.FirstPass.Derived.ValidAreaCellConfiguration
import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedMeasurable

/-! # Line connectivity of area-cell configuration laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- A measurable realization of the fixed-mesh area-cell configuration has a
law connected along lines. The realization agrees with the constructed cells
almost surely. -/
theorem MatedCRTEnv.IsValid.connectedAlongLines_map_areaCellConfig
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (F : Ω → GMSSpace)
    (hF : AEMeasurable F S.P)
    (hF_eq : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (F ω).1 = areaCellConfig h hε (S.mult ε ω)) :
    ConnectedAlongLines (S.P.map F) := by
  rw [connectedAlongLines_iff]
  apply (ae_map_iff hF measurableSet_lineConnected).2
  filter_upwards [hS.ae_areaCellConfig_isCellConfiguration S hε, hF_eq] with ω hgeom heq
  obtain ⟨h, _, _, hline⟩ := hgeom
  obtain ⟨h', hF'⟩ := heq
  rw [hF']
  exact hline

end MatedCRT
