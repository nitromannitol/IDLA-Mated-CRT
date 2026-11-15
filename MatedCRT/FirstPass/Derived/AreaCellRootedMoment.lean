import MatedCRT.FirstPass.Derived.AreaCellIntegralConductance
import LatticeProb.Prob.CellConfigRootedMomentMap

/-! # Rooted moments of area-cell configuration laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS LatticeProb.CellConfigCappedSquare
open scoped ENNReal

/-- An integrable rooted conductance sum gives finite expectation for the law
of an almost-everywhere measurable area-cell configuration. -/
theorem areaCellConfig_finiteExpectation_map_of_originRowSum
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε : ℝ} (hε : 0 < ε) (F : Ω → GMSSpace)
    (hF : AEMeasurable F S.P)
    (hF_eq : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (F ω).1 = areaCellConfig h hε (S.mult ε ω))
    (hfin : ∫⁻ ω, originRowSum id (F ω) ∂S.P < ∞) :
    FiniteExpectation (S.P.map F) := by
  apply finiteExpectation_map_of_originRowSum S.P F hF
  · exact ae_areaCellConfig_conductance_eq_zero_or_one_le S hε F hF_eq
  · exact hfin

end MatedCRT
