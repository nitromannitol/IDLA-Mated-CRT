import MatedCRT.FirstPass.Derived.IntegerWalkShiftedFiniteSetExit
import MatedCRT.FirstPass.Derived.SrwGraphAdjBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CHitting

/-! # Frontier hitting after time shifts -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMS3
open MatedCRTHarmonic.GMSMain MatedCRTHarmonic.GoodScales

/-- Every shifted walk starting in a cell meeting a bounded open set hits its
frontier cells, simultaneously for all such sets and shifts. -/
theorem ae_hitTime_frontier_ne_top_all_bounded_open_all_shifts
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) :
    ∀ᵐ ξ ∂srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x,
      ∀ D : Set ℂ, Bornology.IsBounded D → IsOpen D → ∀ K : ℕ,
        (H.cell (ξ K) ∩ D).Nonempty →
        hitTime (verticesMeeting H.cell (frontier D)) (fun n => ξ (K + n)) ≠ ⊤ := by
  let M := bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)
  have hsteps : ∀ᵐ ξ ∂srwLaw M x, ∀ n,
      ξ (n + 1) = ξ n ∨ (srwGraph M).Adj (ξ n) (ξ (n + 1)) := by
    have ht := MatedCRTHarmonic.Harmonic.ae_forall_succ_mem (srwKernel M) x
      (fun a => {b | b = a ∨ (srwGraph M).Adj a b})
      (isNNChain_srwKernel M).step_null
    simpa only [chainLaw_srwKernel, mem_ofPred_eq] using ht
  filter_upwards [ae_vExitTime_ne_top_all_finite_all_shifts h hε m hlf H hH hconn x,
    hsteps] with ξ hexit hstep
  intro D hDb hDo K hstart
  have hX : ∀ n, StepOK (MatedCRTHarmonic.MatedCRT.graph ε ω hlf)
      (ξ (K + n)) (ξ (K + (n + 1))) := by
    intro n
    have hs := hstep (K + n)
    rw [← graph_adj_eq_srwGraph hlf hε.le] at hs
    simpa only [StepOK, Nat.add_assoc] using hs
  have hnexist : ∃ n, ξ (K + n) ∉ verticesMeeting H.cell D := by
    by_contra hn
    apply hexit (verticesMeeting H.cell D) (finite_verticesMeeting H hDb) K
    apply vExitTime_eq_top_iff.mpr
    intro n
    by_contra hnot
    exact hn ⟨n, hnot⟩
  obtain ⟨n, hn⟩ := hnexist
  have hnsub : ¬ H.cell (ξ (K + n)) ⊆ D := by
    intro hsub
    obtain ⟨z, hz⟩ := cell_nonempty H (ξ (K + n))
    exact hn ⟨z, hz, hsub hz⟩
  refine ne_top_of_le_ne_top (ENat.natCast_ne_top n) ?_
  apply t15c_hitTime_frontier_le hDo hX
  · simpa using hstart
  · exact hnsub

end MatedCRT
end
