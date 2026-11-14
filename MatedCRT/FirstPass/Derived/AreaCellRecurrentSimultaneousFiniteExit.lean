import MatedCRT.FirstPass.Derived.AreaCellSimultaneousFiniteExit

/-! # Simultaneous finite exit for recurrent area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- A recurrent area-cell walk exits every bounded set in finite time, on one
full-measure event. -/
theorem ae_continuousExitTime_ne_top_all_bounded_areaCell_of_recurrent
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    {σ : ℝ≥0} (hσ : 0 < σ)
    (hcell : (areaCellConfig h hε m).IsCellConfiguration)
    (hadj : ∀ K : (areaCellConfig h hε m).cells,
      ∃ K' : (areaCellConfig h hε m).cells, (areaCellConfig h hε m).Adj K K')
    (hrec : (areaCellConfig h hε m).Recurrent) (x : ℤ)
    (Q : Measure (ℕ → (areaCellConfig h hε m).cells))
    (hQ : Q = (srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
      (fun ξ n => euclideanCellEquiv h hε (ξ n)))
    (hSRW : (areaCellConfig h hε m).IsSRWLaw (euclideanCellEquiv h hε x) Q) :
    ∀ᵐ ξ ∂Q, ∀ U : Set ReflectedGMS.Plane, Bornology.IsBounded U →
      BouRabeeGwynne.continuousExitTime U 0
        ((areaCellConfig h hε m).interpolatedWalk
          (areaCellRepresentative h hε m) σ ξ) ≠ ∞ := by
  have hpos := LatticeProb.CellConfigWalk.holding_pos_of_forall_exists_adj hcell hadj
  have hunb := LatticeProb.CellConfigWalk.ae_jumpTimesUnbounded_of_recurrent hrec hpos hSRW
  exact ae_continuousExitTime_ne_top_all_bounded_areaCell
    h hε m hlf H hH hconn hσ hpos x Q hQ hunb

end MatedCRT
end
