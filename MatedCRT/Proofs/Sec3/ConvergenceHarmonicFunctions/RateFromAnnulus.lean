import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.DiscreteExitExcursion
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RateTailReduction

/-! # Same-walk exit-value estimates from annulus crossing estimates -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- A uniform boundary-cell annulus hit-order estimate gives the quenched
same-walk exit-value tail at the polynomial comparison scale. -/
theorem srwLaw_sameWalkExitDiscrepancy_le_of_annulus_hit_order
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hχ : 0 < χ) (hψ : HolderOnWith H χ ψ (closedBall z r))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (ω : Ω) (v : ℤ)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0)
    (hm : 0 < S.mε ε) (hη : Continuous (S.η ω))
    (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hv : v ∈ interiorCellVertices ε (S.η ω) (ball z r))
    {d : ℝ} (hd : 0 < d) (q a b ν C : ℝ)
    (hdR : 2 * d ≤ ε ^ (q / (χ : ℝ)) / 2)
    (hν : 0 ≤ ν) (hC : 0 ≤ C)
    (hadj : ∀ j k, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hsmall : ∀ j ∈ interiorCellVertices ε (S.η ω) (ball z r) ∪
      cellVertices ε (S.η ω) (sphere z r), diam (cell ε (S.η ω) j) ≤ d)
    (hlarge : ∀ j ∈ cellVertices ε (S.η ω) (sphere z (r + 3 * d)),
      diam (cell ε (S.η ω) j) ≤ d)
    (hbound : ∀ j ∈ cellVertices ε (S.η ω) (sphere z r),
      srwLaw (S.mult ε ω) j {path |
        vHitTime (cellVertices ε (S.η ω)
          (sphere (vertexPoint ε (S.η ω) j) (ε ^ (q / (χ : ℝ)) / 2))) path ≤
        vHitTime (cellVertices ε (S.η ω) (sphere z (r + 3 * d))) path} ≤
      ENNReal.ofReal (C * ((100 * ε ^ a + ε ^ b) / (ε ^ (q / (χ : ℝ)) / 2)) ^ ν)) :
    srwLaw (S.mult ε ω) v
      {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
      ENNReal.ofReal ((C * (202 : ℝ) ^ ν) * ε ^ ((min a b - q / (χ : ℝ)) * ν)) := by
  have hfin := srwLaw_ae_interpolatedWalk_exit_ball_lt_top
    (S.mult ε ω) hlf hcons hε hm hη hp z r v
  apply srwLaw_sameWalkExitDiscrepancy_le_of_excursion_tail S hr z ψ hχ hψ hε hε1 ω v
    hη hv hfin q a b ν C hν hC
  exact srwLaw_discrete_exit_excursion_le (S.mult ε ω) v _ hlf hcons hε hm hη hp
    hr hd hdR hv hadj hsmall hlarge hbound

end MatedCRT

#print axioms MatedCRT.srwLaw_sameWalkExitDiscrepancy_le_of_annulus_hit_order
