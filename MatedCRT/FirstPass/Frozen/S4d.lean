import MatedCRT.Defs.Setting

/-!
# Frozen inputs of Proposition 4.2, strict obstacle gap

External facts of plane topology used by the deterministic comparison in `FirstPass/S4d/DeterministicComparison.lean`. They are about open connected planar sets, not about the paper's clusters, odometers, harmonic balls or IDLA processes. The potential-theoretic inputs (minimum principles, pole divergence of the disc Green function) are reused from `FirstPass/Frozen/S2g.lean` and `FirstPass/Frozen/S5c.lean`, and the disc Green function identity `GreenFunctionBallStmt` (Harmonic-Balls-LQG `Draft/Section2.lean`) enters as an explicit hypothesis.
-/

namespace MatedCRT

open Set

/-- Removing one point from a connected open planar set leaves it connected: for an open connected `U ⊆ ℂ` and `z ∈ U`, `U \ {z}` is connected. Source: standard plane topology (the complement of a point in a connected open subset of the plane is connected, since a path through `z` can be rerouted inside a small disc about `z`); standard; locator not yet pinned (e.g. Newman, *Elements of the Topology of Plane Sets of Points*; or Armitage-Gardiner, *Classical Potential Theory*, §1).
Truth check: TRUE.
Discharged: `MatedCRT.frozenPunctureConnected_holds` (`MatedCRT/FirstPass/LPBridge/PunctureConnected.lean:15`) proves it. -/
def FrozenPunctureConnected : Prop :=
  ∀ U : Set ℂ, IsOpen U → IsConnected U → ∀ z ∈ U, IsConnected (U \ {z})

end MatedCRT
