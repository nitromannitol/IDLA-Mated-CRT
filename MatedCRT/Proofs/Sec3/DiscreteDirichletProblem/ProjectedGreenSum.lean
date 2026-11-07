import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedRepresentationVersion
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationCellTail
import MatedCRT.Proofs.Sec7.OdometerBoundMass.Laplacian
import MatedCRT.Draft.Section3HarmonicCorrected

/-! Weighted Green occupation on the finite interior-cell domain. -/

namespace MatedCRT

open Set Metric MeasureTheory

/-- The Green occupation sum over cells meeting a disk is supported on its
interior cells, matching the finite-domain Dirichlet representation. -/
theorem cell_green_occupation_eq_interior_sum
    (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (z : ℂ) (r : ℝ) (a : ℤ)
    (g : ℤ → ℝ) (hC : (cellVertices ε η (ball z r)).Finite)
    (hA : (interiorCellVertices ε η (ball z r)).Finite) :
    (∑' b : cellVertices ε η (ball z r),
      greenFn m (interiorCellVertices ε η (ball z r)) a b * g b) =
      ∑ b ∈ hA.toFinset, g b * greenFn m (interiorCellVertices ε η (ball z r)) a b := by
  classical
  rw [green_occupation_tsum_eq_finset m _ _ hC a g]
  symm
  calc
    _ = ∑ b ∈ hA.toFinset, greenFn m (interiorCellVertices ε η (ball z r)) a b * g b := by
      apply Finset.sum_congr rfl
      intro b hb
      exact mul_comm _ _
    _ = ∑ b ∈ hC.toFinset, greenFn m (interiorCellVertices ε η (ball z r)) a b * g b := by
      apply Finset.sum_subset
      · intro b hb
        exact hC.mem_toFinset.mpr (hA.mem_toFinset.mp hb).1
      · intro b hb hbA
        have hnot : b ∉ interiorCellVertices ε η (ball z r) := fun h => hbA (hA.mem_toFinset.mpr h)
        simp [Sec7.greenFn_eq_zero_of_not_mem_right m a hnot]

/-- Finite-domain representation splits the rescaled solution into projected
harmonic extension and normalized weighted Green occupation. -/
theorem MatedCRTEnv.IsValid.ae_projected_dirichlet_green_decomposition
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hfinite : FiniteDomainDirichletRepresentation)
    (ε : ℝ) (hε : 0 < ε) (hscale : S.mε ε ≠ 0)
    {z y : ℂ} {r : ℝ} (hr : 0 < r) (hy : y ∈ ball z r)
    (ψ φ : ℂ → ℝ) (F : Ω → ℤ → ℝ)
    (hdata : ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ω b = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b))) :
    ∀ᵐ ω ∂S.P, rescale (S.mε ε) ε (S.η ω) (F ω) y =
      projectedDiscreteHarmonicExtension S r z φ ε ω y -
        (S.mε ε)⁻¹ * (∑' b : cellVertices ε (S.η ω) (ball z r),
          greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (vertexOf ε (S.η ω) y) b * ψ (vertexPoint ε (S.η ω) b)) := by
  classical
  filter_upwards [hdata, hS.ae_disk_dirichlet_decomposition_geometry hγ hγ2,
    hS.isAreaParametrized, hS.ae_tendsto_cocompact,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hF hgeom hη hp hadj
  obtain ⟨hA, hB, hnb, hsub, hexit⟩ := hgeom ε hε z r hr
  have hC : (cellVertices ε (S.η ω) (ball z r)).Finite :=
    Tightness.cellVertices_finite hη.1 hp hε isBounded_ball
  have hlf := Tightness.isLocallyFiniteMult_of_cells hη.1 hp hε (hadj ε hε)
  have hcell : vertexOf ε (S.η ω) y ∈ cellVertices ε (S.η ω) (ball z r) :=
    ⟨y, Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε y, hy⟩
  obtain ⟨hex, hrepr⟩ := hfinite (S.mult ε ω) hlf (S.mult_succ_ne_zero hε.le ω)
    _ _ hA hB hnb hexit (F ω) (fun b => ψ (vertexPoint ε (S.η ω) b)) hF.1 _ (hsub hcell)
  have hboundary : (∫ x, (cellVertices ε (S.η ω) (sphere z r)).indicator (F ω)
      (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) =
      S.mε ε * projectedDiscreteHarmonicExtension S r z φ ε ω y := by
    rw [projectedDiscreteHarmonicExtension, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hex] with x hx
    rw [Set.indicator_of_mem hx, hF.2 _ hx]
  rw [rescale, hrepr, hboundary,
    ← cell_green_occupation_eq_interior_sum _ _ _ _ _ _ _ hC hA]
  field_simp


end MatedCRT

#print axioms MatedCRT.cell_green_occupation_eq_interior_sum
