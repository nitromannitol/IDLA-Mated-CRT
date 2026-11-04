import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.SeparatedCells
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PoleLocation
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.HarmonicAwayFromPole
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCellsProb
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Infra.LocallyFinite

/-! # Local harmonicity of the discrete Green kernel -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- On cells separated from the pole and the boundary, the scaled killed
Green kernel is harmonic with probability tending to one. -/
theorem scaled_greenKernel_harmonic_on_separated_cells (𝒮 : SpaceFillingSLEModel)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r d : ℝ} {z y : ℂ} {D : Set ℂ} (hd : 0 < d)
    (hball : ball z r ⊆ ball 0 ρ) (hy : dist y z + d < r)
    (hD : ∀ x ∈ D, dist x z + d < r) (hsep : ∀ x ∈ D, 4 * d ≤ dist y x) :
    ProbTendsToOne S.P fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) D,
      matedLaplacian (S.mult ε ω)
        (fun a => ε⁻¹ * greenKernel (S.mult ε ω)
          (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) a) b = 0} := by
  let G : Set Ω := {ω | IsAreaParametrized (S.μ ω) (S.η ω) ∧
    Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
    (∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))}
  have hG : ∀ᵐ ω ∂S.P, ω ∈ G := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)] with ω hη hp hl
    exact ⟨hη, hp, hl⟩
  have hpG : ProbTendsToOne S.P fun _ => G := probTendsToOne_of_ae hG
  have hpdiam := hS.probTendsToOne_small_cells ρ d hd
  refine (hpG.inter hpdiam).mono_pos ?_
  intro ε hε ω hω
  rcases hω with ⟨⟨hη, hp, hlf⟩, hdiam⟩
  have hsmall : ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ∀ x ∈ cell ε (S.η ω) b, ∀ w ∈ cell ε (S.η ω) b, dist x w ≤ d := by
    intro b hb x hx w hw
    exact (dist_le_diam_of_mem (isCompact_Icc.image hη.1).isBounded hx hw).trans (hdiam b hb)
  have hyball : y ∈ ball z r := by change dist y z < r; linarith
  have hDball : D ⊆ ball z r := by
    intro x hx
    change dist x z < r
    linarith [hD x hx]
  have hycell := Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε y
  have haρ : vertexOf ε (S.η ω) y ∈ cellVertices ε (S.η ω) (ball 0 ρ) :=
    ⟨y, hycell, hball hyball⟩
  have ho := vertexOf_mem_interiorCellVertices_ball hη hp hε hy (hsmall _ haρ)
  have hA : (interiorCellVertices ε (S.η ω) (ball z r)).Finite :=
    (Tightness.cellVertices_finite hη.1 hp hε (isBounded_ball : Bornology.IsBounded (ball z r))).subset
      (by unfold interiorCellVertices; exact sdiff_subset)
  have hsepp := separated_vertexPoints_of_small_cells hη hp hε (hball hyball)
    (hDball.trans hball) hsep hsmall
  intro b hb
  obtain ⟨x, hxb, hxD⟩ := hb
  have hbD : b ∈ cellVertices ε (S.η ω) D := ⟨x, hxb, hxD⟩
  have hbρ : b ∈ cellVertices ε (S.η ω) (ball 0 ρ) := ⟨x, hxb, hball (hDball hxD)⟩
  have hcell : cell ε (S.η ω) b ⊆ ball z r := by
    intro w hwb
    have hwx := hsmall b hbρ w hwb x hxb
    have htri := dist_triangle w x z
    change dist w z < r
    linarith [hD x hxD]
  have hbA : b ∈ interiorCellVertices ε (S.η ω) (ball z r) := by
    constructor
    · exact ⟨x, hxb, hcell hxb⟩
    · rintro ⟨w, hwb, hwfront⟩
      rw [isOpen_ball.frontier_eq] at hwfront
      exact hwfront.2 (hcell hwb)
  have hne : b ≠ vertexOf ε (S.η ω) y := by
    intro heq
    have hh := hsepp b hbD
    rw [heq, sub_self, norm_zero] at hh
    linarith
  exact matedLaplacian_scaled_greenKernel_eq_zero (S.mult_symm ε ω) (hlf ε hε)
    (S.mult_succ_ne_zero hε.le ω) hA ho hbA hne ε

end MatedCRT
