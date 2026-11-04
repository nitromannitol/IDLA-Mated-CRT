import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.SeparatedCells
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.SeparatedKernelBound
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCellsProb
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Infra.LocallyFinite

/-! # Local boundedness of the discrete Green kernel -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Away from the pole, the scaled killed Green kernel satisfies the size
bound required for discrete potential tightness with probability tending to one. -/
theorem scaled_greenKernel_bound_on_separated_cells (𝒮 : SpaceFillingSLEModel)
    (h214 : GreenKernelUpperBoundStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r d : ℝ} {z y : ℂ} {D : Set ℂ} (hr : 0 < r) (hd : 0 < d)
    (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r) (hD : D ⊆ ball z r)
    (hsep : ∀ x ∈ D, 4 * d ≤ dist y x) :
    ∃ K : ℝ, 0 < K ∧ ProbTendsToOne S.P fun ε => {ω |
      ∀ b ∈ cellVertices ε (S.η ω) D,
        |ε⁻¹ * greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (vertexOf ε (S.η ω) y) b| ≤ K / ε} := by
  obtain ⟨K, hK, hbound⟩ := separated_greenKernel_bound_in_probability 𝒮 h214
    hγ hγ2 hρ hρ1 S hS (show 0 < 2 * d by positivity)
  let G : Set Ω := {ω | IsAreaParametrized (S.μ ω) (S.η ω) ∧
    Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
    (∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))}
  have hG : ∀ᵐ ω ∂S.P, ω ∈ G := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)] with ω hη hp hl
    exact ⟨hη, hp, hl⟩
  have hpG : ProbTendsToOne S.P fun _ => G := probTendsToOne_of_ae hG
  have hpdiam := hS.probTendsToOne_small_cells ρ d hd
  refine ⟨K, hK, ((hpG.inter hpdiam).inter hbound).mono_pos ?_⟩
  intro ε hε ω hω
  rcases hω with ⟨⟨⟨hη, hp, hlf⟩, hdiam⟩, hboundω⟩
  have hsmall : ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ∀ x ∈ cell ε (S.η ω) b, ∀ w ∈ cell ε (S.η ω) b, dist x w ≤ d := by
    intro b hb x hx w hw
    exact (dist_le_diam_of_mem (isCompact_Icc.image hη.1).isBounded hx hw).trans (hdiam b hb)
  have hycell := Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε y
  have haρ : vertexOf ε (S.η ω) y ∈ cellVertices ε (S.η ω) (ball 0 ρ) :=
    ⟨y, hycell, hball hy⟩
  have hsub := interiorCellVertices_ball_mono (ε := ε) hη.1 hr hball
  have hA : (interiorCellVertices ε (S.η ω) (ball z r)).Finite :=
    (Tightness.cellVertices_finite hη.1 hp hε (isBounded_ball : Bornology.IsBounded (ball z r))).subset
      (by unfold interiorCellVertices; exact sdiff_subset)
  have hB : (interiorCellVertices ε (S.η ω) (ball 0 ρ)).Finite :=
    (Tightness.cellVertices_finite hη.1 hp hε (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) ρ))).subset
      (by unfold interiorCellVertices; exact sdiff_subset)
  have hsepp := separated_vertexPoints_of_small_cells hη hp hε (hball hy) (hD.trans hball) hsep hsmall
  intro b hb
  have hbρ : b ∈ cellVertices ε (S.η ω) (ball 0 ρ) := by
    obtain ⟨x, hx, hxD⟩ := hb
    exact ⟨x, hx, hball (hD hxD)⟩
  have hbnd := hboundω _ hA hsub hB (hlf ε hε) _ haρ b hbρ (hsepp b hb)
  have hnonneg : 0 ≤ greenKernel (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) b := by
    unfold greenKernel
    exact div_nonneg (greenFn_nonnegative _ _ _ _) (Nat.cast_nonneg _)
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hε.le) hnonneg)]
  calc
    ε⁻¹ * greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
        (vertexOf ε (S.η ω) y) b ≤ ε⁻¹ * K := mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr hε.le)
    _ = K / ε := by ring

end MatedCRT
