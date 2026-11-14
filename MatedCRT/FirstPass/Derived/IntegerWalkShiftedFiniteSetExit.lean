import MatedCRT.FirstPass.Derived.IntegerWalkShiftedVertexExit
import MatedCRT.Proofs.IDLA.Measurable
import MatedCRT.Proofs.Sec4.ObstacleSpecialization

/-! # Shifted exit from finite vertex sets -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain

/-- On one almost-sure event, every shift exits every finite set of vertices. -/
theorem ae_vExitTime_ne_top_all_finite_all_shifts
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) :
    ∀ᵐ ξ ∂srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x,
      ∀ A : Set ℤ, A.Finite → ∀ K : ℕ,
        vExitTime A (fun n => ξ (K + n)) ≠ ⊤ := by
  classical
  filter_upwards [ae_embeddedExitTime_ne_top_all_bounded_all_shifts h hε m hlf H hH hconn x]
    with ξ hξ
  intro A hA K htop
  apply hξ (vertexPoint ε η '' A) (hA.image _).isBounded K
  apply vExitTime_eq_top_iff.mpr
  intro n
  exact ⟨ξ (K + n), vExitTime_eq_top_iff.mp htop n, rfl⟩

/-- A continuous proper curve has finite cell sets over bounded sets, so every
shift exits all such cell sets on the same almost-sure event. -/
theorem ae_vExitTime_cellVertices_ne_top_all_bounded_all_shifts
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) :
    ∀ᵐ ξ ∂srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x,
      ∀ U : Set ℂ, Bornology.IsBounded U → ∀ K : ℕ,
        vExitTime (cellVertices ε η U) (fun n => ξ (K + n)) ≠ ⊤ := by
  filter_upwards [ae_vExitTime_ne_top_all_finite_all_shifts h hε m hlf H hH hconn x]
    with ξ hξ
  intro U hU K
  exact hξ _ (cellVertices_finite_of_isBounded hη hp hε hU) K

end MatedCRT
end
