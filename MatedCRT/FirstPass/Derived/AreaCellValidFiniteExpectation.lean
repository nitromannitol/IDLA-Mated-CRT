import MatedCRT.FirstPass.Derived.AreaCellRootedEnumerationBridge
import MatedCRT.FirstPass.Derived.AreaCellRowMoment
import MatedCRT.FirstPass.Derived.ValidCurveFixedTime

/-! # Finite expectation of valid area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS LatticeProb.CellConfigCappedSquare
open scoped ENNReal

/-- A square-integrable bound on the two root-cell ratios gives finite
expectation for a measurable area-cell configuration of a valid environment. -/
theorem MatedCRTEnv.IsValid.areaCellConfig_finiteExpectation_map_of_root_shape
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε)
    (F : Ω → GMSSpace) (hF : AEMeasurable F S.P)
    (hF_eq : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (F ω).1 = areaCellConfig h hε (S.mult ε ω))
    (A : Ω → ℝ≥0∞) (hA : AEMeasurable A S.P)
    (hA2 : ∫⁻ ω, A ω ^ (2 : ℝ) ∂S.P < ∞)
    (hshape : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      originAreaRatio (euclideanCell ε (S.η ω) h.1 hε 0) ≤ A ω ∧
      originAreaRatio (euclideanCell ε (S.η ω) h.1 hε 1) ≤ A ω) :
    FiniteExpectation (S.P.map F) := by
  obtain ⟨D, hD, hD2, hrow⟩ := hS.exists_twoRoot_row_bound hε
  apply areaCellConfig_finiteExpectation_map_of_root_moments S hε F hF hF_eq
    A D hA hD.aemeasurable hA2 hD2
  filter_upwards [hshape, hrow, hS.ae_fixedTime_singleton_fibre 0] with ω hs hd hf
  obtain ⟨h, h0, h1⟩ := hs
  exact ⟨h, hf, h0, h1, hd⟩

end MatedCRT
