import MatedCRT.FirstPass.Derived.BoundaryLengthPastEdges
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EnvSigmaEdge

/-!
# Past measurability of mated-CRT edges

Edge multiplicities between vertices before a fixed time are measurable from
boundary-length evaluations up to that time.
-/

set_option autoImplicit false

open MeasureTheory

namespace MatedCRT

/-- Edges with both endpoints before `s` are measurable from the path up to `s`. -/
theorem measurable_bmEdgeCount_of_past {Ω : Type} [MeasurableSpace Ω]
    (B : Ω → C(ℝ, ℝ × ℝ)) (s ε : ℝ)
    (hB : ∀ t ≤ s, Measurable fun ω => B ω t)
    (hε : 0 ≤ ε) (j k : ℤ) (hjk : ε * ((max j k : ℤ) : ℝ) ≤ s) :
    Measurable fun ω =>
      bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k := by
  let Bstop : Ω → C(ℝ, ℝ × ℝ) := fun ω =>
    ⟨fun t => B ω (min t s), (B ω).continuous.comp (continuous_id.min continuous_const)⟩
  have hstop : Measurable Bstop := by
    apply ContinuousMap.measurable_iff_eval.2
    intro t
    exact hB (min t s) (min_le_right t s)
  have hmeas := measurable_bmEdgeCount_comp Bstop hstop ε j k
  convert hmeas using 1
  funext ω
  apply bmEdgeCount_eq_of_eqOn_past hε _ _ hjk
  · intro t ht
    simp [Bstop, min_eq_left ht]
  · intro t ht
    simp [Bstop, min_eq_left ht]

end MatedCRT
