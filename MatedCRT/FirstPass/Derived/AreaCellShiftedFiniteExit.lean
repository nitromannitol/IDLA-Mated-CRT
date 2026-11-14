import MatedCRT.FirstPass.Derived.AreaCellShiftedExteriorHit
import LatticeProb.Walk.CellConfigFiniteExit

/-! # Shifted finite exits for area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- On one full-measure event, every shifted interpolated walk exits every
bounded set in finite time, simultaneously for all valid representatives and
positive scales. -/
theorem ae_continuousExitTime_ne_top_all_bounded_all_shifts_areaCell
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (hc : (areaCellConfig h hε m).IsCellConfiguration)
    (hpos : ∀ K, 0 < (areaCellConfig h hε m).holding K) (x : ℤ)
    (hunb : ∀ᵐ ξ ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
        (fun ξ n => euclideanCellEquiv h hε (ξ n)),
      (areaCellConfig h hε m).JumpTimesUnbounded ξ) :
    ∀ᵐ ξ ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
        (fun ξ n => euclideanCellEquiv h hε (ξ n)),
      ∀ K : ℕ, ∀ (p : (areaCellConfig h hε m).cells → Plane),
        (∀ C, p C ∈ (C.1 : Set Plane)) → ∀ (a : ℝ≥0), 0 < a →
        ∀ U : Set Plane, Bornology.IsBounded U →
        BouRabeeGwynne.continuousExitTime U 0
          ((areaCellConfig h hε m).interpolatedWalk p a (fun n => ξ (K + n))) ≠ ∞ := by
  filter_upwards [hunb,
    ae_hitTime_exterior_ne_top_all_bounded_all_shifts_areaCell
      h hε m hlf H hH hconn hc x] with ξ hξ hvisit
  intro K p hp a ha U hU
  obtain ⟨n, hn⟩ := hitTime_ne_top_iff.mp (hvisit K p hp a ha U hU)
  exact LatticeProb.CellConfigInterpolation.continuousExitTime_ne_top_of_visit
    (areaCellConfig h hε m) p (fun n => ξ (K + n)) hpos
    (LatticeProb.CellConfigInterpolation.jumpTimesUnbounded_shift
      (areaCellConfig h hε m) ξ hpos hξ K) ha U n hn

end MatedCRT
end
