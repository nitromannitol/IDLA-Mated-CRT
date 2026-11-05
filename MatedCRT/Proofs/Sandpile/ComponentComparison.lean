import MatedCRT.Proofs.Sandpile.Witness
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Escape

/-! Comparison with the global sandpile on the component of the origin.

This combines worker x2's least-action comparison with worker c1's
origin-component obstacle construction. -/

namespace MatedCRT.Sandpile

open Set Metric Classical

/-- If the stopped cluster stays in the interior of the stopping domain, the
origin-component obstacle problem gives the global cluster comparison, without
requiring the whole stopping domain to be connected. -/
theorem global_cluster_subset_stopped_closure_of_regular
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hd : IsRegularMatedMap m ε η) (ht : 0 < t)
    (h0 : (0 : ℤ) ∈ ballInterior ε η ρ)
    (hint : matedDiscreteCluster m ε η ρ t ⊆ vInterior m (ballInterior ε η ρ)) :
    sandpileCluster m (t / ε) ⊆ insert 0 (vClosure m (matedDiscreteCluster m ε η ρ t)) := by
  let V := vComponent m (ballInterior ε η ρ) 0
  let φ := matedObstacle m ε η ρ t
  let w := discreteLeastSupersolution m V (vClosure m V)
    (fun a => (mdeg m a : ℝ)⁻¹) φ
  let A := discreteCluster (vClosure m V) w φ
  have hS : IsObstacleSetting m V 0 (fun a => (mdeg m a : ℝ)⁻¹) φ
      ((mdeg m 0 : ℝ)⁻¹ * (t / ε)) := by
    simpa [V, φ, matedDeg, mul_comm] using hd.isObstacleSetting ht h0
  have hA : matedDiscreteCluster m ε η ρ t = A := by
    simpa [A, V, w, φ, matedDeg] using hd.cluster_eq ht h0
  have hinterior : A ⊆ vInterior m V := by
    intro a ha
    have haV : a ∈ V := hS.cluster_subset ha
    have haI := hint (hA.symm ▸ ha)
    refine ⟨haV, ?_⟩
    intro b hab
    exact mem_vComponent_of_adj haV (vComponent_subset h0 haV) (haI.2 b hab) hab
  let v : ℤ → ℝ := fun a => if a ∈ vClosure m V then w a - φ a else 0
  have hv : v = sandpileNormOdometer m (t / ε) :=
    obstacle_odometer_eq_of_interior hS hinterior
  have hsub : Function.support v ⊆ A := by
    intro a ha
    by_cases haC : a ∈ vClosure m V
    · have hn : w a - φ a ≠ 0 := by simpa [v, haC] using ha
      exact ⟨haC, lt_of_le_of_ne (hS.obstacle_le_w a haC) (Ne.symm (sub_ne_zero.mp hn))⟩
    · exact False.elim (ha (by simp [v, haC]))
  intro a ha
  have ha' : a ∈ Function.support (sandpileFinal m (t / ε)) := ne_of_gt ha
  have hk := final_support_subset hS.hlf hS.symm ha'
  rw [← hv] at hk
  rcases hk with hzero | hk
  · exact Or.inl hzero
  · rcases hk with haS | ⟨haS, b, hb, hab⟩
    · exact Or.inr (Or.inl (hA.symm ▸ hsub haS))
    · by_cases haA : a ∈ matedDiscreteCluster m ε η ρ t
      · exact Or.inr (Or.inl haA)
      · exact Or.inr (Or.inr ⟨haA, b, hA.symm ▸ hsub hb, hab⟩)

end MatedCRT.Sandpile
