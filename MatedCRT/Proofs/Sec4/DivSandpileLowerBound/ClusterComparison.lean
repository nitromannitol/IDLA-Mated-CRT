import MatedCRT.Proofs.Sandpile.LeastAction

/-!
# Discrete obstacle cluster and divisible sandpile cluster

The lower odometer bound of Section 4 places the noncoincidence set inside the sites that
emit mass. Complementarity from the least-action principle puts those sites in the final cluster.
-/

namespace MatedCRT

open Set

/-- If the normalized odometer dominates the obstacle gap on `V^ε(B_ρ)`, every vertex of the
discrete obstacle cluster belongs to the divisible sandpile cluster. -/
theorem matedDiscreteCluster_subset_sandpileCluster {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hlf : IsLocallyFiniteMult m) (hloop : ∀ a, m a a = 0) (hdeg : ∀ a, 0 < mdeg m a)
    (hne : (Sandpile.admissible m (t / ε)).Nonempty)
    (hlower : ∀ a ∈ cellVertices ε η (Metric.ball 0 ρ),
      matedLeastSupersolution m ε η ρ t a - matedObstacle m ε η ρ t a ≤
        sandpileNormOdometer m (t / ε) a) :
    matedDiscreteCluster m ε η ρ t ⊆ sandpileCluster m (t / ε) := by
  intro a ha
  have ha' : a ∈ cellVertices ε η (Metric.ball 0 ρ) ∧
      matedObstacle m ε η ρ t a < matedLeastSupersolution m ε η ρ t a := ha
  have hpos : 0 < sandpileNormOdometer m (t / ε) a := by
    have := hlower a ha'.1
    linarith [ha'.2]
  change 0 < sandpileFinal m (t / ε) a
  rw [Sandpile.final_eq_one_of_normOdometer_pos hlf hloop hdeg hne hpos]
  norm_num

/-- Filling cells preserves the inclusion of the obstacle cluster in the sandpile cluster. -/
theorem fillCells_matedDiscreteCluster_subset_sandpileCluster {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ}
    {η : ℝ → ℂ} (h : matedDiscreteCluster m ε η ρ t ⊆ sandpileCluster m (t / ε)) :
    fillCells ε η (matedDiscreteCluster m ε η ρ t) ⊆ fillCells ε η (sandpileCluster m (t / ε)) := by
  intro x hx
  simp only [fillCells, mem_iUnion] at hx ⊢
  obtain ⟨a, ha, hxa⟩ := hx
  exact ⟨a, h ha, hxa⟩

end MatedCRT
