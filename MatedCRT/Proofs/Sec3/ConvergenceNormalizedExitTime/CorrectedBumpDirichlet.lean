import MatedCRT.Draft.Section3DirichletCorrected
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BumpDirichlet

/-! Zero-boundary Dirichlet convergence from the projected-data statement. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- The Green construction is an admissible family for Lemma 3.5, given
the adjacency-to-intersection step used to establish local finiteness. -/
theorem finitePoissonSolution_converges_corrected
    (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (ψ : ℂ → ℝ) (hψbound : ∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M)
    (hψholder : IsHolderContinuousOn ψ (ball z r)) :
    ∃ fbar : Ω → ℂ → ℝ,
      (∀ᵐ ω ∂S.P, ContinuousOn (fbar ω) (closedBall z r) ∧
        HasLaplacian (fbar ω) ((S.μ ω).withDensity fun x => ENNReal.ofReal (S.c₀ * ψ x))
          ((S.μ ω).withDensity fun x => ENNReal.ofReal (-(S.c₀ * ψ x))) (ball z r) ∧
        (∀ x ∈ sphere z r, fbar ω x = 0) ∧ IsHolderContinuousOn (fbar ω) (closedBall z r)) ∧
      TendstoUniformlyOnInProbability S.P
        (fun ε ω => rescale (S.mε ε) ε (S.η ω)
          (finitePoissonSolution (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (fun a => ψ (vertexPoint ε (S.η ω) a)))) fbar (closedBall z r) := by
  have hzero : IsHolderContinuousOn (fun _ : ℂ => (0 : ℝ)) (closedBall z r) := by
    refine ⟨0, 1, zero_lt_one, le_rfl, ?_⟩
    exact (LipschitzWith.const (0 : ℝ)).holderWith.holderOnWith _
  apply h35 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ (fun _ => 0) hψbound hψholder hzero
  intro ε hε
  filter_upwards [hS.ae_isLocallyFiniteMult hγ hγ2 hcell,
    hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hlf hp harea
  let A := interiorCellVertices ε (S.η ω) (ball z r)
  have hA : A.Finite := (Tightness.cellVertices_finite harea.1 hp hε isBounded_ball).subset
    (by intro b hb; exact hb.1)
  constructor
  · intro a ha
    exact finitePoissonSolution_laplacian (hlf ε hε)
      (S.mult_succ_ne_zero hε.le ω) hA _ ha
  · intro b hb
    have hbA : b ∉ A := by
      intro h
      apply h.2
      simpa only [frontier_ball z hr.ne'] using hb
    simpa only [mul_zero] using finitePoissonSolution_zero hA _ hbA

end MatedCRT

#print axioms MatedCRT.finitePoissonSolution_converges_corrected
