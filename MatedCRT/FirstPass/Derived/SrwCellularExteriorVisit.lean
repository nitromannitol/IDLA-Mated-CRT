import MatedCRT.FirstPass.Derived.SrwExteriorVisit
import LatticeProb.Walk.CellularEmbeddingIsometricExterior

/-! # Exterior visits for embedded random walks -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain

/-- A relabelled walk with representatives in their cells almost surely visits
outside every bounded set after nonzero scaling and isometric coordinates. -/
theorem ae_visit_exterior_of_srwLaw_map_cellular
    {α F : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω) (hε : 0 ≤ ε)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (e : ℤ → α) (p : α → ℂ) (hp : ∀ v, p (e v) ∈ H.cell v)
    (f : ℂ ≃ₗᵢ[ℝ] F) {s : ℝ} (hs : s ≠ 0)
    {U : Set F} (hU : Bornology.IsBounded U) (x : ℤ)
    (Q : Measure (ℕ → α))
    (hQ : Q = (srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
      (fun ξ n => e (ξ n))) :
    ∀ᵐ ξ ∂Q, ∃ n : ℕ, s • f (p (ξ n)) ∉ U := by
  obtain ⟨R, _, hx, hsep⟩ :=
    MatedCRTHarmonic.GMS3.exists_ball_frontier_isometric_scaled_representatives_outside
      H e p hp f hs hU (p (e x))
  exact ae_visit_exterior_of_srwLaw_map_frontier hlf hε H hconn
    Metric.isOpen_ball Metric.isBounded_ball ⟨p (e x), hp x, hx⟩ e
    (fun a => f (p a)) s U hsep Q hQ

end MatedCRT
