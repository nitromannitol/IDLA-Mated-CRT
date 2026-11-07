import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedHarmonic
import MatedCRT.Audit.StatementsSec3Sec5M1

/-! # Finite exit and boundary geometry for projected harmonic functions -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology

/-- A walk on a locally finite graph with consecutive edges exits every finite
interior vertex set almost surely, simultaneously for all starting vertices. -/
theorem projectedWalk_ae_finite_exit_of_finite (m : ℤ → ℤ → ℕ)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (ε : ℝ) (η : ℝ → ℂ) (r : ℝ) (z : ℂ)
    (hfin : (interiorCellVertices ε η (ball z r)).Finite) :
    ∀ a ∈ interiorCellVertices ε η (ball z r),
      ∀ᵐ x ∂srwLaw m a, vExitTime (interiorCellVertices ε η (ball z r)) x ≠ ⊤ := by
  intro a _
  exact ae_vExitTime_ne_top_of_expectedExitTime_ne_top m _ a
    (Audit.StatementsSec3Sec5M1.finite_expectedExitTime hlf hcons hfin a)

/-- Properness of the curve makes the projected exit expectation discrete harmonic. -/
theorem projectedExitVertexValue_harmonic_of_proper (m : ℤ → ℤ → ℕ)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {r : ℝ} (hr : 0 < r)
    (z : ℂ) (ψ : ℂ → ℝ) {K : ℝ} (hψ : ∀ x ∈ closedBall z r, |ψ x| ≤ K)
    {a : ℤ} (ha : a ∈ interiorCellVertices ε η (ball z r)) :
    matedLaplacian m (projectedExitVertexValue m ε η r z ψ) a = 0 := by
  have hfin : (interiorCellVertices ε η (ball z r)).Finite :=
    (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset fun _ h => h.1
  exact matedLaplacian_projectedExitVertexValue m hlf ε η hr z ψ hψ
    (projectedWalk_ae_finite_exit_of_finite m hlf hcons ε η r z hfin) ha
    (mdeg_ne_zero_of_ne_zero hlf (hcons a))

/-- For sufficiently small mesh, representatives of all boundary cells lie in
any prescribed larger disk. -/
theorem boundary_vertexPoint_eventually_mem_closedBall {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z : ℂ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ a ∈ cellVertices ε η (frontier (ball z r)),
        vertexPoint ε η a ∈ closedBall z (r + s) := by
  have hb : Bornology.IsBounded (frontier (ball z r)) := by
    rw [frontier_ball z hr.ne']
    exact isBounded_sphere
  obtain ⟨ε₀, hε₀, hsmall⟩ := Tightness.exists_cell_near_vertexPoint hη hp hb hs
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall a ha
  obtain ⟨q, hqcell, hqfront⟩ := ha
  have hnear := hsmall ε hε hεsmall a ⟨q, hqcell, hqfront⟩ q hqcell
  have hq : dist q z = r := by simpa only [frontier_ball z hr.ne', mem_sphere] using hqfront
  apply mem_closedBall.mpr
  have htri := dist_triangle (vertexPoint ε η a) q z
  have hnear' : dist q (vertexPoint ε η a) < s := by simpa only [dist_eq_norm] using hnear
  rw [dist_comm (vertexPoint ε η a) q, hq] at htri
  linarith

end MatedCRT
