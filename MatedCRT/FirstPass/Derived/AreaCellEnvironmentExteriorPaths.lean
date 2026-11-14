import MatedCRT.FirstPass.Derived.AreaCellAdjacentSteps
import MatedCRT.FirstPass.Derived.AreaCellShiftedExteriorHit
import MatedCRT.FirstPass.Derived.AreaCellTransition

/-! # Adjacency and exterior visits of area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- An environment's relabelled walk has adjacent steps and, simultaneously
for every shift, visits the exterior of each bounded set at every positive
scale and for every choice of cell representatives. -/
theorem MatedCRTEnv.ae_areaCell_adjacent_and_exterior_all_shifts
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε (S.bm ω))
    (hm : IsLocallyFiniteMult (S.mult ε ω))
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf) (0 : ℤ))
    (hH : H.cell = cell ε (S.η ω))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) hlf).adj.Connected)
    (hc : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration) (x : ℤ) :
    ∀ᵐ ξ ∂((srwLaw (S.mult ε ω) x).map (fun ξ n => euclideanCellEquiv h hε (ξ n))),
      (∀ n, (areaCellConfig h hε (S.mult ε ω)).Adj (ξ n) (ξ (n + 1))) ∧
      (∀ K : ℕ, ∀ p : (areaCellConfig h hε (S.mult ε ω)).cells → Plane,
        (∀ C, p C ∈ (C.1 : Set Plane)) → ∀ a : ℝ≥0, 0 < a →
        ∀ U : Set Plane, Bornology.IsBounded U →
        hitTime {C : (areaCellConfig h hε (S.mult ε ω)).cells | (a : ℝ) • p C ∉ U}
          (fun n => ξ (K + n)) ≠ ⊤) := by
  filter_upwards [ae_areaCell_adjacent_steps h hε (S.mult ε ω) hm
    (S.mult_mdeg_pos hε.le ω hm) (S.mult_self ε ω) (S.mult_symm ε ω) x,
    ae_hitTime_exterior_ne_top_all_bounded_all_shifts_areaCell
      h hε (S.mult ε ω) hlf H hH hconn hc x] with ξ hadj hvisit
  exact ⟨hadj, hvisit⟩

end MatedCRT
end
