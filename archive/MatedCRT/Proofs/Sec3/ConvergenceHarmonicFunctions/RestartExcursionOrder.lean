import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartEnlargedDisk
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartCellInterior

/-! # Excursion hit order after a random boundary restart -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- After the first hit at an original boundary cell, a large displacement
from its representative forces an outer-circle hit before the enlarged
boundary hit, when Euclidean exit occurs after the restart. -/
theorem srwLaw_ae_restart_outer_hit_le_enlarged_hit
    (m : ℤ → ℤ → ℕ) (D : Set ℤ) (a : ℤ)
    {ε mε r R d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hε : 0 < ε) (hm : 0 < mε) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hr : 0 < r) (hd : 0 < d) (hdR : d < R)
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsmall : ∀ b ∈ cellVertices ε η (sphere z r), diam (cell ε η b) ≤ d)
    (hlarge : ∀ b ∈ cellVertices ε η (sphere z (r + 3 * d)),
      diam (cell ε η b) ≤ d) :
    ∀ᵐ x ∂srwLaw m a, ∀ k : ℕ, vHitTime D x = k →
      x k ∈ cellVertices ε η (sphere z r) →
      (k : ℝ) ≤ mε * ((pathExitTime (ball z r)
        (interpolatedWalk ε η mε x)).toNNReal : ℝ) →
      R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
        (vertexPoint ε η (x k)) →
      vHitTime (cellVertices ε η (sphere (vertexPoint ε η (x k)) R)) (pathShift k x) ≤
        vHitTime (cellVertices ε η (sphere z (r + 3 * d))) (pathShift k x) := by
  have hsteps : ∀ᵐ x ∂srwLaw m a, ∀ n,
      x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0 := by
    rw [ae_all_iff]
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (WalkSteps.srwLaw_nonadjacent_null m n a)] with x hx
    exact Classical.not_not.1 hx
  have hfin := srwLaw_ae_restart_enlarged_sphereCellHit_ne_top m D a hlf hcons
    hε hη hp hr hd hadj hsmall
  filter_upwards [hsteps, hfin] with x hx hf k hk hb hlo hfar
  have hR : 0 < R := lt_trans hd hdR
  have hnb := (disk_dirichlet_decomposition_geometry (z := vertexPoint ε η (x k))
    hε hR hη hp hadj hlf hcons).2.2.1
  exact outer_hit_le_target_hit_of_large_excursion_of_small_restart_cell
    hε.le hm hd hη m x k hR ((hsmall _ hb).trans_lt hdR) hx hnb hlo hlarge (hf k hk hb) hfar

end MatedCRT

#print axioms MatedCRT.srwLaw_ae_restart_outer_hit_le_enlarged_hit
