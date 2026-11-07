import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CorrectedBumpDirichlet
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.NearPoleComparison

/-! Near-pole comparison using the corrected projected Dirichlet statement. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- The near-pole error is controlled in probability by the continuum
Dirichlet limit for the buffered bump. -/
theorem nearPole_controlled_by_dirichlet_limit_corrected
    (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r δ : ℝ} {z y : ℂ} (hr : 0 < r) (hδ : 0 < δ)
    (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (φ : ℂ → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hone : ∀ x ∈ ball y (δ + δ), φ x = 1)
    (hholder : IsHolderContinuousOn φ (ball z r)) :
    ∃ fbar : Ω → ℂ → ℝ,
      (∀ᵐ ω ∂S.P, ContinuousOn (fbar ω) (closedBall z r) ∧
        HasLaplacian (fbar ω)
          ((S.μ ω).withDensity fun x => ENNReal.ofReal (S.c₀ * -φ x))
          ((S.μ ω).withDensity fun x => ENNReal.ofReal (-(S.c₀ * -φ x))) (ball z r) ∧
        (∀ x ∈ sphere z r, fbar ω x = 0) ∧ IsHolderContinuousOn (fbar ω) (closedBall z r)) ∧
      TendstoUniformlyOnInProbability S.P
        (fun ε ω => rescale (S.mε ε) ε (S.η ω)
          (finitePoissonSolution (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (fun b => -φ (vertexPoint ε (S.η ω) b)))) fbar (closedBall z r) ∧
      ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          S.P {ω | 2 * t < rescale (S.mε ε) ε (S.η ω)
                (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y -
              (S.mε ε)⁻¹ * ∑ b ∈ truncatedGreenCells ε (S.η ω) z y r δ,
                greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
                  (vertexOf ε (S.η ω) y) b} ≤ S.P {ω | t < fbar ω y} + e := by
  have hneg : IsHolderContinuousOn (fun x => -φ x) (ball z r) := by
    obtain ⟨C, α, hα, hα1, h⟩ := hholder
    refine ⟨C, α, hα, hα1, ?_⟩
    intro x hx x' hx'
    simpa only [edist_neg_neg] using h x hx x' hx'
  have hbound : ∃ M : ℝ, ∀ x ∈ ball z r, |-φ x| ≤ M := by
    refine ⟨1, ?_⟩
    intro x hx
    rw [abs_neg, abs_of_nonneg (hφ x).1]
    exact (hφ x).2
  obtain ⟨fbar, hpde, hconv⟩ := finitePoissonSolution_converges_corrected 𝒮 h35 hcell
    hγ hγ2 hρ hρ1 S hS hr hball (fun x => -φ x) hbound hneg
  refine ⟨fbar, hpde, hconv, ?_⟩
  let G : ℝ → Ω → ℝ := fun ε ω => rescale (S.mε ε) ε (S.η ω)
    (finitePoissonSolution (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
      (fun b => -φ (vertexPoint ε (S.η ω) b))) y
  have hpoint : TendstoInProbability S.P G (fun ω => fbar ω y) := by
    intro t ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv t ht)
      (fun _ => zero_le)
    intro ε
    apply measure_mono
    intro ω hω
    exact ⟨y, ball_subset_closedBall hy, hω⟩
  intro t ht e he
  apply eventually_measure_gt_le_of_compare S.P
    (fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      diam (cell ε (S.η ω) b) ≤ δ}) _ G (fun ω => fbar ω y) ?_
    (hS.probTendsToOne_small_cells ρ δ hδ) hpoint ht he
  intro ε hε
  filter_upwards [hS.ae_nearPole_le_poissonSolution hγ hγ2 hcell z y r δ hball φ
    (fun x => (hφ x).1) hone] with ω hω hdiam
  exact (hω ε hε hdiam).2

end MatedCRT

#print axioms MatedCRT.nearPole_controlled_by_dirichlet_limit_corrected
