import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartDependentEvent
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.FiniteCircleHit
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.DiskDecompositionGeometry

/-! # Finite boundary hitting after a random restart -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- At the first hit of `D`, a walk restarted at a vertex in `B` almost
surely hits the target circle, if every vertex of `B` is interior to the
target disk. -/
theorem srwLaw_ae_restart_sphereCellHit_ne_top
    (m : ℤ → ℤ → ℕ) (D B : Set ℤ) (a : ℤ)
    {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hε : 0 < ε) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hr : 0 < r)
    (hB : B ⊆ interiorCellVertices ε η (ball z r))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) :
    ∀ᵐ x ∂srwLaw m a, ∀ k : ℕ, vHitTime D x = k → x k ∈ B →
      vHitTime (cellVertices ε η (sphere z r)) (pathShift k x) ≠ ⊤ := by
  let E : Set (ℕ → ℤ) := {x | vHitTime (cellVertices ε η (sphere z r)) x = ⊤}
  have hE : MeasurableSet E := (measurable_vHitTime _) (measurableSet_singleton ⊤)
  have hnb := (disk_dirichlet_decomposition_geometry (z := z) hε hr hη hp hadj hlf hcons).2.2.1
  have hnull : ∀ b ∈ B, srwLaw m b E ≤ 0 := by
    intro b hb
    apply le_of_eq
    apply measure_eq_zero_iff_ae_notMem.mpr
    exact srwLaw_ae_sphereCellHit_ne_top_of_proper hlf hcons hε hη hp hr (hB hb) hnb
  have hzero := srwLaw_hitTime_dependent_continuation_le m D B (fun _ => E)
    (fun _ => hE) a 0 hnull
  have hae := measure_eq_zero_iff_ae_notMem.mp (le_antisymm hzero bot_le)
  filter_upwards [hae] with x hx k hk hb htop
  apply hx
  exact mem_iUnion.mpr ⟨k, hk, hb, htop⟩

end MatedCRT

#print axioms MatedCRT.srwLaw_ae_restart_sphereCellHit_ne_top
