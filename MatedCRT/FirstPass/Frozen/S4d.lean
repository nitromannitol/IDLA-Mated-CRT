import MatedCRT.Defs.Setting

/-!
# First-pass frozen inputs of Proposition 4.2, strict obstacle gap (q4, fp-S4d-4-2-assembly)

EXTERNAL facts of plane topology used by the deterministic comparison `StrictGapDeterministicComparisonStep`
(FirstPass/S4d/DeterministicComparison.lean). They are about open connected planar sets, not about the paper's clusters,
odometers, harmonic balls or IDLA processes. The potential-theoretic inputs (minimum principles, pole divergence of the
disc Green function) are reused from FirstPass/Frozen/S2g.lean and S5c.lean, and the disc Green function identity
`GreenFunctionBallStmt` (Harmonic-Balls-LQG Draft/Section2.lean) enters as an explicit hypothesis.
-/

namespace MatedCRT

open Set

/-- **FIRST-PASS FROZEN.** Removing one point from a connected open planar set leaves it connected: for an open connected
`U ⊆ ℂ` and `z ∈ U`, `U \ {z}` is connected. Source: standard plane topology (the complement of a point in a connected
open subset of the plane is connected, since a path through `z` can be rerouted inside a small disc about `z`);
standard; locator pending (e.g. Newman, Elements of the Topology of Plane Sets of Points; or Armitage-Gardiner,
Classical Potential Theory, §1). Used by: `strictGapDeterministicComparison_of_frozen`
(FirstPass/S4d/DeterministicComparison.lean), to apply the strong minimum principle on `Λ_s \ {0}`. -/
def FrozenPunctureConnected : Prop :=
  ∀ U : Set ℂ, IsOpen U → IsConnected U → ∀ z ∈ U, IsConnected (U \ {z})

end MatedCRT
