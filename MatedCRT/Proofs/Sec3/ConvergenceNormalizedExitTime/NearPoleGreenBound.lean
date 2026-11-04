import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.NearPoleComparison
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.WeightedDirichletEnvironment
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DirichletUniqueness

/-! Identify the limiting buffered Dirichlet solution with its Green potential. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory Laplacian _root_.HarmonicBalls
open scoped ENNReal

/-- The tail of the discrete near-pole error is controlled by the Green
potential of the buffered source. -/
theorem nearPole_controlled_by_greenPotential
    (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hcell : AdjacentCellsMeetAeStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r δ : ℝ} {z y : ℂ} (hr : 0 < r) (hδ : 0 < δ)
    (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (φ : ℂ → ℝ) (hφm : Measurable φ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hone : ∀ x ∈ ball y (δ + δ), φ x = 1)
    (hholder : IsHolderContinuousOn φ (ball z r))
    {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P {ω | 2 * t < rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y -
        (S.mε ε)⁻¹ * ∑ b ∈ truncatedGreenCells ε (S.η ω) z y r δ,
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (vertexOf ε (S.η ω) y) b} ≤
      S.P {ω | t < S.c₀ * ∫ w in ball z r, greenFunction (ball z r) y w * φ w ∂S.μ ω} + e := by
  obtain ⟨fbar, hpde, _, hbound⟩ := nearPole_controlled_by_dirichlet_limit
    𝒮 h35 hcell hγ hγ2 hρ hρ1 S hS hr hδ hball hy φ hφ hone hholder
  have hq := weightedGreenPotential_ae_satisfies_dirichlet 𝒮 h217
    hγ hγ2 hρ hρ1 S hS hr hball φ hφm (fun x => (hφ x).1) (fun x => (hφ x).2)
  have heq : {ω | t < fbar ω y} =ᵐ[S.P]
      {ω | t < S.c₀ * ∫ w in ball z r, greenFunction (ball z r) y w * φ w ∂S.μ ω} := by
    filter_upwards [hpde, hq] with ω hf hq
    have h := eqOn_closedBall_of_hasLaplacian_eq hf.1 hq.1 hf.2.1 hq.2.1
      (fun x hx => (hf.2.2.1 x hx).trans (hq.2.2 x hx).symm)
      (ball_subset_closedBall hy)
    change (t < fbar ω y) =
      (t < S.c₀ * ∫ w in ball z r, greenFunction (ball z r) y w * φ w ∂S.μ ω)
    rw [h]
  have hmeasure := measure_congr heq
  filter_upwards [hbound t ht e he] with ε hε
  simpa only [hmeasure] using hε

end MatedCRT
