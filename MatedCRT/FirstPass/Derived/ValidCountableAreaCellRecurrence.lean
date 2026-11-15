import MatedCRT.FirstPass.Derived.ValidAreaCellRecurrence

/-! # Recurrence for countable families of area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- For a countable family of positive meshes, the area-cell configurations
are simultaneously recurrent almost surely when each realization satisfies
the hypotheses of the cell-configuration invariance principle. -/
theorem MatedCRTEnv.IsValid.ae_countable_areaCellConfig_recurrent_of_gmsLaw
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (F : ι → Ω → GMSSpace)
    (hF : ∀ i, AEMeasurable (F i) S.P)
    (hF_eq : ∀ i, ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (F i ω).1 = areaCellConfig h (hε i) (S.mult (ε i) ω))
    (hprob : ∀ i, IsProbabilityMeasure (S.P.map (F i)))
    (hmt : ∀ i, MassTransport (S.P.map (F i)))
    (herg : ∀ i, ErgodicModuloScaling (S.P.map (F i)))
    (hfin : ∀ i, FiniteExpectation (S.P.map (F i))) :
    ∀ᵐ ω ∂S.P, ∀ i, ∀ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (areaCellConfig h (hε i) (S.mult (ε i) ω)).Recurrent := by
  apply ae_all_iff.mpr
  intro i
  let _ : IsProbabilityMeasure (S.P.map (F i)) := hprob i
  exact hS.ae_areaCellConfig_recurrent_of_gmsLaw S (hε i) (F i)
    (hF i) (hF_eq i) (hmt i) (herg i) (hfin i)

end MatedCRT
