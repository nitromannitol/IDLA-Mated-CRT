import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RateDiscrepancy
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellWindow
import MatedCRT.Proofs.Infra.RandomWalk

/-! # Reduction of the quenched exit-value tail to the excursion tail -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped NNReal

/-- For a walk started at an interior cell, a tail bound on the separation
of its two stopping locations bounds the same-walk exit-value tail. Finite
Euclidean exit is stated explicitly; it is supplied by the finite-domain
walk argument in the annulus iteration. -/
theorem srwLaw_sameWalkExitDiscrepancy_tail_le
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hψ : HolderOnWith H χ ψ (closedBall z r))
    {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω) (v : ℤ)
    (hη : Continuous (S.η ω))
    (hv : v ∈ interiorCellVertices ε (S.η ω) (ball z r))
    (hfin : ∀ᵐ x ∂srwLaw (S.mult ε ω) v,
      pathExitTime (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x) < ⊤)
    (s : ℝ) :
    (srwLaw (S.mult ε ω) v)
      {x | (H : ℝ) * (2 * s) ^ (χ : ℝ) < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
    (srwLaw (S.mult ε ω) v)
      {x | s < dist (pathExitPosition (ball z r)
          (interpolatedWalk ε (S.η ω) (S.mε ε) x))
        (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))} := by
  apply measure_mono_ae
  filter_upwards [srwLaw_ae_start (S.mult ε ω) v, hfin] with x hx hxf
  intro hbad
  have hstart : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 ∈ ball z r := by
    have hzero : interpolatedWalk ε (S.η ω) (S.mε ε) x 0 =
        vertexPoint ε (S.η ω) v := by
      simp [interpolatedWalk, hx]
    rw [hzero]
    exact Sec7.cell_subset_ball_of_mem_interiorCellVertices hη hv
      (Sec7.vertexPoint_mem_cell hε v)
  exact location_distance_lt_of_sameWalkExitDiscrepancy_gt S hr z ψ hψ ε ω x hstart hxf hbad

end MatedCRT
