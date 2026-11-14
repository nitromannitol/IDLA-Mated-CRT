import MatedCRT.FirstPass.Derived.SrwMappedBoundaryHit

/-! # Exterior visits from boundary hitting -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain

/-- A relabelled walk visits the exterior of a set when the representatives of
all cells meeting a separating frontier lie outside that set. The path-law
identity and geometric separation are explicit hypotheses. -/
theorem ae_visit_exterior_of_srwLaw_map_frontier
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    {β : Type*} [SMul ℝ β]
    {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω) (hε : 0 ≤ ε)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {x : ℤ} (hx : (H.cell x ∩ D).Nonempty) (e : ℤ → α)
    (p : α → β) (s : ℝ) (U : Set β)
    (hsep : ∀ v ∈ verticesMeeting H.cell (frontier D), s • p (e v) ∉ U)
    (Q : Measure (ℕ → α))
    (hQ : Q = (srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
      (fun ξ n => e (ξ n))) :
    ∀ᵐ ξ ∂Q, ∃ n : ℕ, s • p (ξ n) ∉ U := by
  rw [hQ]
  have hh := ae_hitTime_of_srwLaw_map_frontier hlf hε H hconn hDo hDb hx e
    {a | s • p a ∉ U} hsep
  filter_upwards [hh] with ξ hξ
  exact hitTime_ne_top_iff.mp hξ

end MatedCRT
