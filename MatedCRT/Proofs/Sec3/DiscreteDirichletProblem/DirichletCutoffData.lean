import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundedBoundaryCutoff
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.EnvSigmaRepresentation
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryDataBounds

/-! # Measurable cutoff data for the discrete Dirichlet problem -/

namespace MatedCRT

open Set Metric MeasureTheory _root_.HarmonicBalls

/-- Hölder source and boundary data admit environment-measurable vertex
cutoffs. The source cutoff agrees almost surely on interior cells, while
the bounded boundary cutoff agrees on boundary cells with polynomially high
probability. -/
theorem MatedCRTEnv.IsValid.exists_measurable_dirichlet_cutoff_data
    {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮)
    {γ ρ r s : ℝ} {z : ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (hs : 0 < s) (hD : ball z r ⊆ ball 0 ρ)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (ψ φ : ℂ → ℝ) (hψ : IsHolderContinuousOn ψ (ball z r))
    (hφ : IsHolderContinuousOn φ (closedBall z (r + s))) :
    ∃ q g : ℝ → Ω → ℤ → ℝ,
      (∀ ε b, Measurable[S.envSigma] fun ω => q ε ω b) ∧
      (∀ ε b, Measurable[S.envSigma] fun ω => g ε ω b) ∧
      (∃ C : ℝ, ∀ ε ω b, |g ε ω b| ≤ |S.mε ε| * C) ∧
      (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
        ∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
          q ε ω a = ψ (vertexPoint ε (S.η ω) a)) ∧
      PolyHighProb S.P (fun ε => {ω |
        ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
          g ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b)}) := by
  obtain ⟨ψcut, hψcutm, hψcut⟩ :=
    exists_measurable_cutoff_of_holderOn isOpen_ball.measurableSet hψ
  obtain ⟨φcut, hφcutm, ⟨C, hC⟩, hφcut⟩ :=
    exists_bounded_measurable_boundary_cutoff_polyHighProb h28 hγ hγ2 hρ hρ1
      hr hs hD S hS φ hφ
  refine ⟨(fun ε ω b => ψcut (vertexPoint ε (S.η ω) b)),
    (fun ε ω b => S.mε ε * φcut (vertexPoint ε (S.η ω) b)), ?_, ?_, ?_, ?_, ?_⟩
  · intro ε b
    simpa only [one_mul] using S.measurable_envSigma_vertex_data ε 1 ψcut hψcutm b
  · exact fun ε b => S.measurable_envSigma_vertex_data ε (S.mε ε) φcut hφcutm b
  · refine ⟨C, ?_⟩
    intro ε ω b
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
  · intro ε hε
    filter_upwards [hS.isAreaParametrized] with ω hη a ha
    exact hψcut _ (Sec7.cell_subset_ball_of_mem_interiorCellVertices hη.1 ha
      (Sec7.vertexPoint_mem_cell hε.le a))
  · exact polyHighProb_mono_ae hφcut (ae_of_all _ fun _ => True.intro)
      (fun _ _ _ h _ b hb => congrArg (S.mε _ * ·) (h b hb))

end MatedCRT
