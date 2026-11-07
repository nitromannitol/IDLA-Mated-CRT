import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.FirstBoundaryExcursion

/-! # Excursion probability at the discrete disk exit -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The discrete exit-position excursion is bounded by the same annulus
hit-order estimate, since the first disk-interior exit is the first visit to
a boundary cell. -/
theorem srwLaw_discrete_exit_excursion_le
    (m : ℤ → ℤ → ℕ) (a : ℤ) (c : ℝ≥0∞)
    {ε mε r R d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hε : 0 < ε) (hm : 0 < mε) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hr : 0 < r) (hd : 0 < d) (hdR : 2 * d ≤ R)
    (ha : a ∈ interiorCellVertices ε η (ball z r))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsmall : ∀ b ∈ interiorCellVertices ε η (ball z r) ∪
      cellVertices ε η (sphere z r), diam (cell ε η b) ≤ d)
    (hlarge : ∀ b ∈ cellVertices ε η (sphere z (r + 3 * d)),
      diam (cell ε η b) ≤ d)
    (hbound : ∀ b ∈ cellVertices ε η (sphere z r), srwLaw m b {path |
      vHitTime (cellVertices ε η (sphere (vertexPoint ε η b) R)) path ≤
        vHitTime (cellVertices ε η (sphere z (r + 3 * d))) path} ≤ c) :
    srwLaw m a {x | R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (vExitPosition (interiorCellVertices ε η (ball z r)) x))} ≤ c := by
  let I := interiorCellVertices ε η (ball z r)
  let B := cellVertices ε η (sphere z r)
  have hgeometry := disk_dirichlet_decomposition_geometry (z := z) hε hr hη hp hadj hlf hcons
  have hnb := hgeometry.2.2.1
  have hexit := hgeometry.2.2.2.2 a ha
  have heq := ae_sphereCellHit_eq_diskInteriorExit hr ha hnb
  calc
    _ ≤ srwLaw m a {x | ∃ k : ℕ, vHitTime B x = k ∧ x k ∈ B ∧
        R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
          (vertexPoint ε η (x k))} := by
      apply measure_mono_ae
      filter_upwards [hexit, heq] with x hfin heq hfar
      let k := (vExitTime I x).toNat
      have hfirst : vHitTime B x = (k : ℕ∞) := (heq hfin).trans (ENat.natCast_toNat hfin).symm
      have hhitfin : vHitTime B x ≠ ⊤ := by rw [heq hfin]; exact hfin
      have hb := apply_vHitTime_mem_of_ne_top hhitfin
      rw [hfirst, ENat.toNat_natCast] at hb
      exact ⟨k, hfirst, hb, by simpa [vExitPosition, k, I] using hfar⟩
    _ ≤ c := srwLaw_first_boundary_excursion_le m a c hlf hcons hε hm hη hp hr hd hdR ha
      hadj hsmall hlarge hbound

end MatedCRT

#print axioms MatedCRT.srwLaw_discrete_exit_excursion_le
