import MatedCRT.FirstPass.Derived.SrwStrictAdjacency
import MatedCRT.FirstPass.Derived.AreaCellGraph

/-! # Adjacent steps of area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov
open scoped ENNReal

/-- Relabelling the vertices by their area cells preserves almost-sure adjacency
of all steps of the walk. -/
theorem ae_areaCell_adjacent_steps
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hlf : IsLocallyFiniteMult m) (hpos : ∀ x, 0 < mdeg m x)
    (hloop : ∀ x, m x x = 0) (hsymm : ∀ x y, m x y = m y x) (x : ℤ) :
    ∀ᵐ ξ ∂(srwLaw m x).map (fun ξ n => euclideanCellEquiv h hε (ξ n)),
      ∀ n, (areaCellConfig h hε m).Adj (ξ n) (ξ (n + 1)) := by
  let C := areaCellConfig h hε m
  let e := euclideanCellEquiv h hε
  let : Countable C.cells := Countable.of_equiv ℤ e
  let e' : ℤ ≃ᵐ C.cells :=
    { toEquiv := e
      measurable_toFun := measurable_of_countable _
      measurable_invFun := measurable_of_countable _ }
  let E : (ℕ → ℤ) ≃ᵐ (ℕ → C.cells) :=
    MeasurableEquiv.piCongrRight (fun _ => e')
  change ∀ᵐ ξ ∂(srwLaw m x).map E, _
  apply E.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [srwLaw_ae_adj m hlf hpos hloop x] with ξ hstep
  intro n
  exact ((areaCellConfig_graph_adj_iff h hε m hsymm _ _).2 (hstep n)).2.1

end MatedCRT
end
