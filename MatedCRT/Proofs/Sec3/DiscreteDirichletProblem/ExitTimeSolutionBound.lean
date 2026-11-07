import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.EquicontinuityLemmas
import MatedCRT.Proofs.Sec4.SubsequentialProperties.DiscreteComparison

/-! Expected-exit-time barriers for the discrete Dirichlet problem. -/

namespace MatedCRT

open Set Metric Filter Topology
open scoped ENNReal

/-- On a finite disk, bounded boundary data and a bounded discrete Laplacian
    control the solution by the ordinary expected exit time. -/
theorem abs_solution_le_boundary_add_expectedExitTime
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 < ε) (hr : 0 < r) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsucc : ∀ k, m k (k + 1) ≠ 0)
    (u : ℤ → ℝ) {C M : ℝ}
    (hlap : ∀ a ∈ interiorCellVertices ε η (ball z r), |matedLaplacian m u a| ≤ C)
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r), |u b| ≤ M)
    (hQfin : ∀ a ∈ interiorCellVertices ε η (ball z r),
      expectedExitTime m (interiorCellVertices ε η (ball z r)) a ≠ ⊤) :
    ∀ a ∈ cellVertices ε η (ball z r),
      |u a| ≤ M + C * (expectedExitTime m (interiorCellVertices ε η (ball z r)) a).toReal := by
  let A := interiorCellVertices ε η (ball z r)
  have hlf := Tightness.isLocallyFiniteMult_of_cells hη hp hε hadj
  have hAfin : A.Finite :=
    (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset (fun _ ha => ha.1)
  have hesc := escape_of_adjacent_succ hsucc hAfin
  have hdeg : ∀ k, mdeg m k ≠ 0 := fun k => mdeg_ne_zero_of_ne_zero hlf (hsucc k)
  have hM' : ∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∉ A → |u b| ≤ M := by
    intro a ha b hab hb
    apply hbd b
    exact vBoundary_interiorCellVertices_subset hη hr hadj ⟨hb, a, ha, hab⟩
  have hu : ∀ a ∈ A, |lapSum hlf u a| ≤ C * (mdeg m a : ℝ) := by
    intro a ha
    rw [← mLaplacian_mul_mdeg hlf u a, abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right (hlap a ha) (Nat.cast_nonneg _)
  have hw0 : ∀ a ∉ A, (expectedExitTime m A a).toReal = 0 := fun a ha => by
    rw [expectedExitTime_eq_zero_of_not_mem m ha, ENNReal.toReal_zero]
  have hw : ∀ a ∈ A, lapSum hlf (fun b => (expectedExitTime m A b).toReal) a =
      -(mdeg m a : ℝ) := fun a ha => Tightness.lapSum_expectedExitTime hlf hQfin ha (hdeg a)
  obtain ⟨f, hfoff, _, hfbd, hdiff⟩ :=
    Tightness.exists_harmonic_decomposition hlf hAfin hesc hM' hu hw0 hw
  intro a ha
  by_cases haA : a ∈ A
  · have htri : |u a| ≤ |u a - f a| + |f a| := by
      have h := abs_add_le (u a - f a) (f a)
      simpa only [sub_add_cancel] using h
    linarith [hdiff a, hfbd a haA]
  · have habd : a ∈ cellVertices ε η (sphere z r) :=
      mem_cellVertices_sphere_of_not_mem_interior hr ha haA
    rw [hw0 a haA, mul_zero, add_zero]
    exact hbd a habd

end MatedCRT
