import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartDependentEvent
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSBoundaryHit

/-! # Restarting the annulus hitting estimate -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- A uniform concentric-boundary hitting estimate can be restarted at a
random hit vertex, with the center of the annulus chosen at its marked point. -/
theorem srwLaw_restart_sphere_hit_order_le
    (m : ℤ → ℤ → ℕ) (D B : Set ℤ) (ε : ℝ) (η : ℝ → ℂ)
    (z : ℂ) (R r : ℝ) (a : ℤ) (c : ℝ≥0∞)
    (hbound : ∀ b ∈ B, srwLaw m b {path |
      vHitTime (cellVertices ε η (sphere (vertexPoint ε η b) r)) path ≤
        vHitTime (cellVertices ε η (sphere z R)) path} ≤ c) :
    srwLaw m a (⋃ k : ℕ, {path | vHitTime D path = k ∧ path k ∈ B ∧
      vHitTime (cellVertices ε η (sphere (vertexPoint ε η (path k)) r))
          (pathShift k path) ≤
        vHitTime (cellVertices ε η (sphere z R)) (pathShift k path)}) ≤ c := by
  apply srwLaw_hitTime_dependent_continuation_le m D B
    (fun b => {path | vHitTime (cellVertices ε η (sphere (vertexPoint ε η b) r)) path ≤
      vHitTime (cellVertices ε η (sphere z R)) path}) ?_ a c hbound
  intro b
  exact ((measurable_vHitTime _).prodMk (measurable_vHitTime _))
    (MeasurableSet.of_discrete (s := {p : ℕ∞ × ℕ∞ | p.1 ≤ p.2}))

end MatedCRT

#print axioms MatedCRT.srwLaw_restart_sphere_hit_order_le
