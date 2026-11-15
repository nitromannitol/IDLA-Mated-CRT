import MatedCRT.FirstPass.Derived.AreaCellTwoRootFiniteExpectation
import MatedCRT.FirstPass.Derived.AreaCellConductanceRows
import LatticeProb.Prob.CellConfigRootedEnumeration

/-! # Rooted conductance sums of area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS LatticeProb.CellConfigCappedSquare
open scoped ENNReal

/-- The rooted sum of an area-cell configuration includes the full conductance
row of each integer-indexed cell. -/
theorem originRowSum_eq_areaCell_tsum
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (H : GMSSpace)
    (hH : H.1 = areaCellConfig h hε m) :
    originRowSum id H = ∑' k : ℤ,
      originAreaRatio (euclideanCell ε η h.1 hε k) *
        ENNReal.ofReal (∑' b : ℤ, (m k b : ℝ)) := by
  cases H with
  | mk C hC =>
    cases hH
    change originRowSum id ⟨areaCellConfig h hε m, hC⟩ = _
    rw [originRowSum_eq_tsum_cells ⟨areaCellConfig h hε m, hC⟩ (euclideanCellEquiv h hε)]
    apply tsum_congr
    intro k
    change originAreaRatio (euclideanCell ε η h.1 hε k) *
      ENNReal.ofReal ((areaCellConfig h hε m).pi (euclideanCellEquiv h hε k)) = _
    rw [areaCellConfig_pi_eq_tsum]

/-- Square moments of the root-cell ratios and full conductance rows imply
finite expectation of an identified area-cell configuration law. -/
theorem areaCellConfig_finiteExpectation_map_of_root_moments
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε : ℝ} (hε : 0 < ε) (F : Ω → GMSSpace)
    (hF : AEMeasurable F S.P)
    (hF_eq : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (F ω).1 = areaCellConfig h hε (S.mult ε ω))
    (A D : Ω → ℝ≥0∞)
    (hA : AEMeasurable A S.P) (hD : AEMeasurable D S.P)
    (hA2 : ∫⁻ ω, A ω ^ (2 : ℝ) ∂S.P < ∞)
    (hD2 : ∫⁻ ω, D ω ^ (2 : ℝ) ∂S.P < ∞)
    (hbound : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (∀ t, S.η ω t = S.η ω 0 → t = 0) ∧
      originAreaRatio (euclideanCell ε (S.η ω) h.1 hε 0) ≤ A ω ∧
      originAreaRatio (euclideanCell ε (S.η ω) h.1 hε 1) ≤ A ω ∧
      ENNReal.ofReal (∑' b : ℤ, (S.mult ε ω 0 b : ℝ)) +
        ENNReal.ofReal (∑' b : ℤ, (S.mult ε ω 1 b : ℝ)) ≤ D ω) :
    FiniteExpectation (S.P.map F) := by
  apply areaCellConfig_finiteExpectation_map_of_two_root_bounds S hε F hF hF_eq
    (fun ω k => ENNReal.ofReal (∑' b : ℤ, (S.mult ε ω k b : ℝ)))
    A D hA hD hA2 hD2
  filter_upwards [hF_eq, hbound] with ω ⟨h, hFω⟩ ⟨h', hf, h0, h1, hd⟩
  have heq : h' = h := Subsingleton.elim _ _
  subst h'
  exact ⟨h, hf, (originRowSum_eq_areaCell_tsum h hε (S.mult ε ω) (F ω) hFω).le,
    h0, h1, hd⟩

end MatedCRT
