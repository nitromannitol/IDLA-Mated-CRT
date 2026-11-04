import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.NearPoleGreenBound
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.NonnegativeTail
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! Absolute near-pole error controlled by a buffered Green potential. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory Laplacian _root_.HarmonicBalls
open scoped ENNReal

/-- The one-sided Green-potential bound controls the absolute error as well,
because the error is nonnegative on the small-cell event. -/
theorem nearPole_absolute_controlled_by_greenPotential
    (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r δ : ℝ} {z y : ℂ} (hr : 0 < r) (hδ : 0 < δ)
    (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (φ : ℂ → ℝ) (hφm : Measurable φ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hone : ∀ x ∈ ball y (δ + δ), φ x = 1)
    (hholder : IsHolderContinuousOn φ (ball z r))
    {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P {ω | 2 * t < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y -
        (S.mε ε)⁻¹ * ∑ b ∈ truncatedGreenCells ε (S.η ω) z y r δ,
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (vertexOf ε (S.η ω) y) b|} ≤
      (S.P {ω | t < S.c₀ * ∫ w in ball z r, greenFunction (ball z r) y w * φ w ∂S.μ ω} + e) + e := by
  let E : ℝ → Set Ω := fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
    diam (cell ε (S.η ω) b) ≤ δ}
  let F : ℝ → Ω → ℝ := fun ε ω => rescale (S.mε ε) ε (S.η ω)
      (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y -
    (S.mε ε)⁻¹ * ∑ b ∈ truncatedGreenCells ε (S.η ω) z y r δ,
      greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
        (vertexOf ε (S.η ω) y) b
  have hnonneg : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε → 0 ≤ F ε ω := by
    intro ε hε
    filter_upwards [hS.ae_nearPole_le_poissonSolution hγ hγ2 (adjacentCellsMeetAeStep 𝒮)
      z y r δ hball φ (fun x => (hφ x).1) hone] with ω hω hE
    exact (hω ε hε hE).1
  have htail := nearPole_controlled_by_greenPotential 𝒮 h35 h217 (adjacentCellsMeetAeStep 𝒮)
    hγ hγ2 hρ hρ1 S hS hr hδ hball hy φ hφm hφ hone hholder ht he
  exact eventually_abs_tail_le_of_nonneg S.P E F hnonneg
    (hS.probTendsToOne_small_cells ρ δ hδ) he htail

end MatedCRT
