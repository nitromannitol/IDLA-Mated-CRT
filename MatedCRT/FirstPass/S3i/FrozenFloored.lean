import MatedCRT.FirstPass.S3i.Frozen

/-!
# The floored one-sided boundary continuity estimate (BE), a frozen cited input

`FrozenOneSidedBoundaryContinuity` (S3i/Frozen.lean:44) is false as
typed (see docs/campaign/FROZEN-PROVENANCE.md), since its boundary distance `dist(η x, ∂D)` has no floor at the cell scale. This module states the floored form
`FrozenOneSidedBoundaryContinuityFloored`: the estimate is restricted to the interior cell vertices, and the distance is
replaced by `max (dist (η x, ∂D)) (ε ^ β)` for an exponent `β` with `0 < β < 1`, placed as in correction [C6] of
Lemma 3.2 (`DiscreteHolderContinuityStmt`, Draft/Section3.lean:67; docs/campaign/CORRECTIONS.md).

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps*, arXiv:1807.07511, Theorem 3.9, equations
(3.30)–(3.31), pp. 30–31. The printed (3.31) has no floor. The floored statement is not yet quoted
verbatim from the source.

PENDING TRUTH CHECK (see docs/campaign/FROZEN-PROVENANCE.md): the truth of the floored form, and the range of `β` for which it holds, are not established.
This module is used only as a hypothesis (never a `∀ 𝒮` inside).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **(BE-floored)**, the floored one-sided boundary continuity estimate of discrete harmonic functions. It replaces
`FrozenOneSidedBoundaryContinuity` (S3i/Frozen.lean:44), which is false as typed (see docs/campaign/FROZEN-PROVENANCE.md). Two changes, both in the
statement of Frozen.lean:44–55:
the vertex `x` ranges over the interior cell vertices `interiorCellVertices ε (S.η ω) D`, and the distance
`infDist (vertexPoint ε (S.η ω) x) (frontier D)` is replaced by its floor `max (infDist …) (ε ^ β)`.
The exponents and the constant `κ, ν, A, b, β` are chosen after `S.IsValid 𝒮 γ`, per valid environment, as in the
repaired form of Frozen.lean. The exponent `β` is encoded as in correction [C6] (`0 < β ∧ β < 1`).
PENDING TRUTH CHECK (see docs/campaign/FROZEN-PROVENANCE.md). -/
def FrozenOneSidedBoundaryContinuityFloored (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ κ ν A b β : ℝ, 0 < κ ∧ 0 < ν ∧ 0 < A ∧ 0 < b ∧ 0 < β ∧ β < 1 ∧
  PolyHighProb S.P fun ε => {ω | ∀ (D : Set ℂ) (f : ℤ → ℝ),
    D ⊆ ball 0 ρ → IsOpen D → IsConnected D → SimplyConnectedSpace D →
    (∀ x ∈ interiorCellVertices ε (S.η ω) D, matedLaplacian (S.mult ε ω) f x = 0) →
    ∀ x ∈ interiorCellVertices ε (S.η ω) D, ∀ t : ℝ, 0 < t →
      f x ≤ boundarySupNear ε (S.η ω) D f x t
        + A * discreteSupNorm ε (S.η ω) D f
          * (t / max (infDist (vertexPoint ε (S.η ω) x) (frontier D)) (ε ^ β)) ^ (-ν)}

end FirstPass36
end MatedCRT
