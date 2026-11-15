import MatedCRT.FirstPass.Derived.ValidAreaCellGMSLaw
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116

/-! # Recurrence of area-cell walks under the GMS hypotheses -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- A fixed-mesh area-cell realization is almost surely recurrent when its law
satisfies the hypotheses of the cell-configuration invariance principle. -/
theorem MatedCRTEnv.IsValid.ae_areaCellConfig_recurrent_of_gmsLaw
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (F : Ω → GMSSpace)
    (hF : AEMeasurable F S.P)
    (hF_eq : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (F ω).1 = areaCellConfig h hε (S.mult ε ω))
    [IsProbabilityMeasure (S.P.map F)]
    (hmt : MassTransport (S.P.map F)) (herg : ErgodicModuloScaling (S.P.map F))
    (hfin : FiniteExpectation (S.P.map F)) :
    ∀ᵐ ω ∂S.P, ∀ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (areaCellConfig h hε (S.mult ε ω)).Recurrent := by
  have hconn := hS.connectedAlongLines_map_areaCellConfig S hε F hF hF_eq
  obtain ⟨_, _, hrec, _⟩ := theorem1_16 (S.P.map F) hmt herg hfin hconn
  filter_upwards [ae_of_ae_map hF hrec, hF_eq] with ω hω ⟨h, heq⟩
  intro h'
  rw [heq] at hω
  exact hω

end MatedCRT
