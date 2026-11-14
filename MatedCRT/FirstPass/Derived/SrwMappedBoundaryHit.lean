import MatedCRT.FirstPass.Derived.SrwBoundaryHit

/-! # Boundary hitting under vertex relabelling -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain

/-- A relabelled walk almost surely hits any set containing the labels of all
vertices whose cells meet the boundary of a bounded open domain. -/
theorem ae_hitTime_of_srwLaw_map_frontier
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω) (hε : 0 ≤ ε)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {x : ℤ} (hx : (H.cell x ∩ D).Nonempty) (e : ℤ → α) (A : Set α)
    (hA : ∀ v ∈ verticesMeeting H.cell (frontier D), e v ∈ A) :
    ∀ᵐ ξ ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
        (fun ξ n => e (ξ n)), hitTime A ξ ≠ ⊤ := by
  have hm : Measurable (fun ξ : ℕ → ℤ => fun n => e (ξ n)) :=
    Measurable.of_eval fun n => (measurable_of_countable e).comp (measurable_pi_apply n)
  have htarget : MeasurableSet {ξ : ℕ → α | hitTime A ξ ≠ ⊤} :=
    (measurableSet_hitTime_eq_top (MeasurableSet.of_discrete : MeasurableSet A)).compl
  apply (ae_map_iff hm.aemeasurable htarget).2
  have hsource : ∀ᵐ ξ ∂srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x,
      hitTime (verticesMeeting H.cell (frontier D)) ξ ≠ ⊤ := by
    apply (mem_ae_iff_prob_eq_one ?_).2
    · exact srwLaw_hitTime_frontier_ne_top hlf hε H hconn hDo hDb hx
    · exact (measurableSet_hitTime_eq_top (MeasurableSet.of_discrete :
        MeasurableSet (verticesMeeting H.cell (frontier D)))).compl
  filter_upwards [hsource] with ξ hξ
  obtain ⟨n, hn⟩ := hitTime_ne_top_iff.mp hξ
  exact hitTime_ne_top_iff.mpr ⟨n, hA _ hn⟩

end MatedCRT
