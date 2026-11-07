import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedGeometry
import MatedCRT.Proofs.Sec4.SubsequentialProperties.DiscreteComparison
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.External.SLE

/-! # Finite-domain geometry for the discrete disk -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology

/-- The interior and boundary cell sets of a disk are finite; neighbouring
vertices of an interior cell lie in their union, and the walk exits the
interior almost surely. -/
theorem disk_dirichlet_decomposition_geometry
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 < ε) (hr : 0 < r) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hlf : IsLocallyFiniteMult m) (hsucc : ∀ k, m k (k + 1) ≠ 0) :
    (interiorCellVertices ε η (ball z r)).Finite ∧
    (cellVertices ε η (sphere z r)).Finite ∧
    (∀ a ∈ interiorCellVertices ε η (ball z r), ∀ b,
      m a b ≠ 0 → b ∈ interiorCellVertices ε η (ball z r) ∪
        cellVertices ε η (sphere z r)) ∧
    (cellVertices ε η (ball z r) ⊆ interiorCellVertices ε η (ball z r) ∪
      cellVertices ε η (sphere z r)) ∧
    (∀ a ∈ interiorCellVertices ε η (ball z r),
      ∀ᵐ x ∂srwLaw m a, vExitTime (interiorCellVertices ε η (ball z r)) x ≠ ⊤) := by
  have hA : (interiorCellVertices ε η (ball z r)).Finite :=
    (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset (fun _ ha => ha.1)
  have hB : (cellVertices ε η (sphere z r)).Finite :=
    Tightness.cellVertices_finite hη hp hε isBounded_sphere
  refine ⟨hA, hB, ?_, ?_, projectedWalk_ae_finite_exit_of_finite m hlf hsucc ε η r z hA⟩
  · intro a ha b hab
    by_cases hb : b ∈ interiorCellVertices ε η (ball z r)
    · exact Or.inl hb
    · exact Or.inr (vBoundary_interiorCellVertices_subset hη hr hadj ⟨hb, a, ha, hab⟩)
  · intro a ha
    by_cases hb : a ∈ interiorCellVertices ε η (ball z r)
    · exact Or.inl hb
    · exact Or.inr (mem_cellVertices_sphere_of_not_mem_interior hr ha hb)

/-- Almost surely, the finite-domain decomposition prerequisites hold
simultaneously for every positive mesh and every Euclidean disk. -/
theorem MatedCRTEnv.IsValid.ae_disk_dirichlet_decomposition_geometry
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (interiorCellVertices ε (S.η ω) (ball z r)).Finite ∧
      (cellVertices ε (S.η ω) (sphere z r)).Finite ∧
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r), ∀ b,
        S.mult ε ω a b ≠ 0 → b ∈ interiorCellVertices ε (S.η ω) (ball z r) ∪
          cellVertices ε (S.η ω) (sphere z r)) ∧
      (cellVertices ε (S.η ω) (ball z r) ⊆
        interiorCellVertices ε (S.η ω) (ball z r) ∪ cellVertices ε (S.η ω) (sphere z r)) ∧
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        ∀ᵐ x ∂srwLaw (S.mult ε ω) a,
          vExitTime (interiorCellVertices ε (S.η ω) (ball z r)) x ≠ ⊤) := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hη hp hadj
  intro ε hε z r hr
  exact disk_dirichlet_decomposition_geometry hε hr hη.1 hp (hadj ε hε)
    (Tightness.isLocallyFiniteMult_of_cells hη.1 hp hε (hadj ε hε))
    (S.mult_succ_ne_zero hε.le ω)

end MatedCRT
