import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S4S6c.FrontierSeparation

/-!
# Almost sure finite exit from a bounded region (q2, task fp-S4S6c-envscaling-6-7-6-8; LEMMA68 C2, the input `hexit`)

For a configuration `ω` with `η` continuous and proper, a multiplicity `m` that is locally finite with consecutive
edges, and a bounded open-or-not region `U`, the walk from any start leaves the set of vertices `V(U) = meetVerts`
of the cells meeting `U` almost surely in finite time. This is the input `hexit` of `ConfigBound68.trace_half`.
The finiteness of `V(U)` is `TraceInputs68.cellVertices_finite_of_tendsto` (cells are compact, so the closure in
`meetVerts` is the cell itself); the exit null set is `ExitNull68.exit_null_of_finite`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MatedCRT

namespace ExitAe68

/-- Almost surely finite exit from the vertices whose cells meet a bounded set. -/
theorem ae_exit_ne_top_of_bounded {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {U : Set ℂ} (hU : Bornology.IsBounded U) (a : ℤ) :
    ∀ᵐ x ∂srwLaw m a, vExitTime (FrontierSeparation.meetVerts (cell ε η) U) x ≠ ⊤ := by
  have hfin : (FrontierSeparation.meetVerts (cell ε η) U).Finite := by
    refine (TraceInputs68.cellVertices_finite_of_tendsto hε hp hU).subset ?_
    intro v hv
    obtain ⟨x, hx1, hx2⟩ := hv
    have hc : IsCompact (cell ε η v) := isCompact_Icc.image hη
    rw [hc.isClosed.closure_eq] at hx1
    exact ⟨x, hx1, hx2⟩
  have h0 := ExitNull68.exit_null_of_finite hlf hcons hfin a
  exact ae_iff.mpr (by simpa using h0)

end ExitAe68

end MatedCRT

#print axioms MatedCRT.ExitAe68.ae_exit_ne_top_of_bounded
