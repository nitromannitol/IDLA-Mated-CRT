import MatedCRT.Draft.Section3HarmonicCorrected

/-!
# Boundary maxima and discrete sup norms

The two quantities of the one-sided boundary continuity estimate of Gwynne–Miller–Sheffield, *Harmonic functions on
mated-CRT maps*, arXiv:1807.07511, Theorem 3.9, equation (3.31): the maximum of a discrete function over the boundary
cells near a vertex, and its discrete sup norm on a domain. The floored estimate built from them is
`FrozenOneSidedBoundaryContinuityFloored` (`S3i/FrozenFloored.lean`).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The maximum of `f` over the discrete boundary cells `V^ε(∂D ∩ B_t(η(x)))` near the vertex `x` (PRO §2.2).
The supremum over the empty set is `0` (the convention of `sSup ∅` in `ℝ`); on the bounded domains used here the
index set is finite. -/
noncomputable def boundarySupNear (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) (f : ℤ → ℝ) (x : ℤ) (t : ℝ) : ℝ :=
  ⨆ k ∈ cellVertices ε η (frontier D ∩ ball (vertexPoint ε η x) t), f k

/-- The discrete sup norm of `f` over the vertices `V^ε(D)` (PRO §2.2). -/
noncomputable def discreteSupNorm (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) (f : ℤ → ℝ) : ℝ :=
  ⨆ k ∈ cellVertices ε η D, |f k|

end FirstPass36
end MatedCRT
