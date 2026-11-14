import MatedCRT.FirstPass.Derived.AreaCellSimultaneousExteriorVisit
import LatticeProb.Walk.CellConfigFiniteExit

/-! # Simultaneous finite exit for area-parametrized cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal

/-- Almost every interpolated walk exits every bounded set in finite time. -/
theorem ae_continuousExitTime_ne_top_all_bounded_areaCell
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    {σ : ℝ≥0} (hσ : 0 < σ)
    (hpos : ∀ K, 0 < (areaCellConfig h hε m).holding K) (x : ℤ)
    (Q : Measure (ℕ → (areaCellConfig h hε m).cells))
    (hQ : Q = (srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
      (fun ξ n => euclideanCellEquiv h hε (ξ n)))
    (hunb : ∀ᵐ ξ ∂Q, (areaCellConfig h hε m).JumpTimesUnbounded ξ) :
    ∀ᵐ ξ ∂Q, ∀ U : Set ReflectedGMS.Plane, Bornology.IsBounded U →
      BouRabeeGwynne.continuousExitTime U 0
        ((areaCellConfig h hε m).interpolatedWalk
          (areaCellRepresentative h hε m) σ ξ) ≠ ∞ := by
  have hs : (σ : ℝ) ≠ 0 := by exact_mod_cast hσ.ne'
  filter_upwards [hunb,
    ae_visit_all_exteriors_areaCellRepresentative h hε m hlf H hH hconn hs x Q hQ]
    with ξ hξ hvisit U hU
  obtain ⟨k, hk⟩ := hvisit U hU
  exact LatticeProb.CellConfigInterpolation.continuousExitTime_ne_top_of_visit
    (areaCellConfig h hε m) (areaCellRepresentative h hε m) ξ hpos hξ hσ U k hk

end MatedCRT
end
