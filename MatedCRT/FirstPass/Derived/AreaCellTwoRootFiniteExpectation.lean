import MatedCRT.FirstPass.Derived.AreaCellRootedMoment
import MatedCRT.FirstPass.Derived.AreaCellTwoRootMoment

/-! # Finite expectation from the two root cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS LatticeProb.CellConfigCappedSquare
open scoped ENNReal

/-- Two square-moment bounds imply finite expectation for an area-cell law,
provided its rooted row sum is bounded by the integer-indexed weighted sum. -/
theorem areaCellConfig_finiteExpectation_map_of_two_root_bounds
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε : ℝ} (hε : 0 < ε) (F : Ω → GMSSpace)
    (hF : AEMeasurable F S.P)
    (hF_eq : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (F ω).1 = areaCellConfig h hε (S.mult ε ω))
    (w : Ω → ℤ → ℝ≥0∞) (A D : Ω → ℝ≥0∞)
    (hA : AEMeasurable A S.P) (hD : AEMeasurable D S.P)
    (hA2 : ∫⁻ ω, A ω ^ (2 : ℝ) ∂S.P < ∞)
    (hD2 : ∫⁻ ω, D ω ^ (2 : ℝ) ∂S.P < ∞)
    (hbound : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (∀ t, S.η ω t = S.η ω 0 → t = 0) ∧
      originRowSum id (F ω) ≤
        ∑' k : ℤ, originAreaRatio (euclideanCell ε (S.η ω) h.1 hε k) * w ω k ∧
      originAreaRatio (euclideanCell ε (S.η ω) h.1 hε 0) ≤ A ω ∧
      originAreaRatio (euclideanCell ε (S.η ω) h.1 hε 1) ≤ A ω ∧
      w ω 0 + w ω 1 ≤ D ω) :
    FiniteExpectation (S.P.map F) := by
  apply areaCellConfig_finiteExpectation_map_of_originRowSum S hε F hF hF_eq
  exact lintegral_lt_top_of_two_root_bounds S.P hε w (fun ω => originRowSum id (F ω))
    A D hA hD hA2 hD2 hbound

end MatedCRT
