import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartSphereOrder

/-! # Reduction of an excursion event to a restarted annulus crossing -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- If each exceptional excursion yields a boundary hit followed by an outer
annulus hit before the target boundary, a uniform estimate from the random
hit vertex bounds the excursion probability. The geometric witness is kept
explicit. -/
theorem srwLaw_excursion_le_of_restart_sphere_hit_order
    (m : ℤ → ℤ → ℕ) (D B : Set ℤ) (ε : ℝ) (η : ℝ → ℂ)
    (z : ℂ) (R r : ℝ) (a : ℤ) (c : ℝ≥0∞) (E : Set (ℕ → ℤ))
    (hbound : ∀ b ∈ B, srwLaw m b {path |
      vHitTime (cellVertices ε η (sphere (vertexPoint ε η b) r)) path ≤
        vHitTime (cellVertices ε η (sphere z R)) path} ≤ c)
    (hwitness : ∀ᵐ path ∂srwLaw m a, path ∈ E → ∃ k : ℕ,
      vHitTime D path = k ∧ path k ∈ B ∧
      vHitTime (cellVertices ε η (sphere (vertexPoint ε η (path k)) r))
          (pathShift k path) ≤
        vHitTime (cellVertices ε η (sphere z R)) (pathShift k path)) :
    srwLaw m a E ≤ c := by
  calc
    _ ≤ srwLaw m a (⋃ k : ℕ, {path | vHitTime D path = k ∧ path k ∈ B ∧
        vHitTime (cellVertices ε η (sphere (vertexPoint ε η (path k)) r))
            (pathShift k path) ≤
          vHitTime (cellVertices ε η (sphere z R)) (pathShift k path)}) := by
      apply measure_mono_ae
      filter_upwards [hwitness] with path hp
      intro hE
      obtain ⟨k, hk⟩ := hp hE
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
    _ ≤ c := srwLaw_restart_sphere_hit_order_le m D B ε η z R r a c hbound

end MatedCRT

#print axioms MatedCRT.srwLaw_excursion_le_of_restart_sphere_hit_order
