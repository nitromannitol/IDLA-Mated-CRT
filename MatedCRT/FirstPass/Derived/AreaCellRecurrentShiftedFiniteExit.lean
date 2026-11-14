import MatedCRT.FirstPass.Derived.AreaCellShiftedFiniteExit
import MatedCRT.FirstPass.Derived.AreaCellRecurrentSimultaneousFiniteExit

/-! # Shifted finite exits for recurrent area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- For a recurrent area-cell walk, every shifted interpolation exits every
bounded set in finite time, simultaneously over representatives and scales. -/
theorem ae_continuousExitTime_ne_top_all_bounded_all_shifts_areaCell_of_recurrent
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (hc : (areaCellConfig h hε m).IsCellConfiguration)
    (hadj : ∀ K : (areaCellConfig h hε m).cells,
      ∃ K' : (areaCellConfig h hε m).cells, (areaCellConfig h hε m).Adj K K')
    (hrec : (areaCellConfig h hε m).Recurrent) (x : ℤ)
    (Q : Measure (ℕ → (areaCellConfig h hε m).cells))
    (hQ : Q = (srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
      (fun ξ n => euclideanCellEquiv h hε (ξ n)))
    (hSRW : (areaCellConfig h hε m).IsSRWLaw (euclideanCellEquiv h hε x) Q) :
    ∀ᵐ ξ ∂Q, ∀ K : ℕ, ∀ (p : (areaCellConfig h hε m).cells → Plane),
      (∀ C, p C ∈ (C.1 : Set Plane)) → ∀ (a : ℝ≥0), 0 < a →
      ∀ U : Set Plane, Bornology.IsBounded U →
      BouRabeeGwynne.continuousExitTime U 0
        ((areaCellConfig h hε m).interpolatedWalk p a (fun n => ξ (K + n))) ≠ ∞ := by
  have hpos := LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hc hadj
  have hunb := LatticeProb.CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hSRW
  rw [hQ] at hunb ⊢
  exact ae_continuousExitTime_ne_top_all_bounded_all_shifts_areaCell
    h hε m hlf H hH hconn hc hpos x hunb

end MatedCRT
end
