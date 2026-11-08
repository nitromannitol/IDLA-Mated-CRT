import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.DiscreteExitExcursion
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RateTailReduction

/-! Same-walk comparison at an arbitrary excursion distance. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- A boundary-cell hit-order estimate at any admissible distance gives a
Hölder discrepancy tail at that distance. -/
theorem srwLaw_sameWalkExitDiscrepancy_le_of_boundary_hit
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hψ : HolderOnWith H χ ψ (closedBall z r))
    {ε : ℝ} (hε : 0 < ε) (ω : Ω) (v : ℤ)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0)
    (hm : 0 < S.mε ε) (hη : Continuous (S.η ω))
    (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hv : v ∈ interiorCellVertices ε (S.η ω) (ball z r))
    {d s : ℝ} (hd : 0 < d) (hds : 2 * d ≤ s) (c : ℝ≥0∞)
    (hadj : ∀ j k, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hsmall : ∀ j ∈ interiorCellVertices ε (S.η ω) (ball z r) ∪
      cellVertices ε (S.η ω) (sphere z r), diam (cell ε (S.η ω) j) ≤ d)
    (hlarge : ∀ j ∈ cellVertices ε (S.η ω) (sphere z (r + 3 * d)),
      diam (cell ε (S.η ω) j) ≤ d)
    (hbound : ∀ j ∈ cellVertices ε (S.η ω) (sphere z r),
      srwLaw (S.mult ε ω) j {path |
        vHitTime (cellVertices ε (S.η ω)
          (sphere (vertexPoint ε (S.η ω) j) s)) path ≤
        vHitTime (cellVertices ε (S.η ω) (sphere z (r + 3 * d))) path} ≤ c) :
    srwLaw (S.mult ε ω) v
      {x | (H : ℝ) * (2 * s) ^ (χ : ℝ) < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤ c := by
  have hfin := srwLaw_ae_interpolatedWalk_exit_ball_lt_top
    (S.mult ε ω) hlf hcons hε hm hη hp z r v
  exact (srwLaw_sameWalkExitDiscrepancy_tail_le S hr z ψ hψ hε.le ω v hη hv hfin s).trans
    (srwLaw_discrete_exit_excursion_le (S.mult ε ω) v c hlf hcons hε hm hη hp
      hr hd hds hv hadj hsmall hlarge hbound)

end MatedCRT

#print axioms MatedCRT.srwLaw_sameWalkExitDiscrepancy_le_of_boundary_hit
