import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusBarriers
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedGeometry

/-! # Finite hitting of boundary cells -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- A walk started inside a disk hits its boundary cells almost surely when
its interior cell set is finite and edges leave it through the boundary. -/
theorem srwLaw_ae_sphereCellHit_ne_top_of_finite
    {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ} {a : ℤ}
    (hr : 0 < r) (ha : a ∈ interiorCellVertices ε η (ball z r))
    (hfin : (interiorCellVertices ε η (ball z r)).Finite)
    (hnb : ∀ v ∈ interiorCellVertices ε η (ball z r), ∀ w,
      m v w ≠ 0 → w ∈ interiorCellVertices ε η (ball z r) ∪
        cellVertices ε η (sphere z r)) :
    ∀ᵐ x ∂srwLaw m a, vHitTime (cellVertices ε η (sphere z r)) x ≠ ⊤ := by
  filter_upwards [projectedWalk_ae_finite_exit_of_finite m hlf hcons ε η r z hfin a ha,
    ae_sphereCellHit_eq_diskInteriorExit hr ha hnb] with x hx heq
  rw [heq hx]
  exact hx

/-- Properness of the embedding curve gives the finite-cell hypothesis for
almost-sure hitting of the boundary cells of a disk. -/
theorem srwLaw_ae_sphereCellHit_ne_top_of_proper
    {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ} {a : ℤ}
    (hε : 0 < ε) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hr : 0 < r) (ha : a ∈ interiorCellVertices ε η (ball z r))
    (hnb : ∀ v ∈ interiorCellVertices ε η (ball z r), ∀ w,
      m v w ≠ 0 → w ∈ interiorCellVertices ε η (ball z r) ∪
        cellVertices ε η (sphere z r)) :
    ∀ᵐ x ∂srwLaw m a, vHitTime (cellVertices ε η (sphere z r)) x ≠ ⊤ := by
  apply srwLaw_ae_sphereCellHit_ne_top_of_finite hlf hcons hr ha ?_ hnb
  exact (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset fun _ h => h.1

end MatedCRT

#print axioms MatedCRT.srwLaw_ae_sphereCellHit_ne_top_of_finite
#print axioms MatedCRT.srwLaw_ae_sphereCellHit_ne_top_of_proper
