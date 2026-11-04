import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3

/-!
# Lemma 3.7: normalized expected exit time

The Green potential below uses the normalization of correction C1. The open
steps separate its continuum Dirichlet identification, local convergence in
the ball, and control near the boundary. In particular, the local step must
use Lemma 3.3 directly away from the pole; it does not use Lemma 3.2.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- Continuum Green potential appearing in Lemma 3.7. -/
noncomputable def normalizedExitGreenPotential {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ω : Ω) (x : ℂ) : ℝ :=
  S.c₀ / 6 * ∫ y in ball z r, greenFunction (ball z r) x y ∂S.μ ω

/-- Identification of the continuum Green potential with the Dirichlet
solution, including continuity up to the boundary. -/
def NormalizedExitPotentialStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ᵐ ω ∂S.P,
    ContinuousOn (normalizedExitGreenPotential S r z ω) (closedBall z r) ∧
    HasLaplacian (normalizedExitGreenPotential S r z ω) 0
      (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) (ball z r) ∧
    ∀ x ∈ sphere z r, normalizedExitGreenPotential S r z ω x = 0

/-- Local uniform convergence to the Green potential, on every smaller
closed ball. This is the subsequential identification in Steps 1--3 of the
proof, using uniform Green-kernel convergence away from the pole. -/
def NormalizedExitInteriorStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  UniformConvergenceGreenKernelStmt 𝒮 → CountingMeasureConvergenceStmt 𝒮 →
  ExpectedExitTimeExplicitBoundStmt 𝒮 → DiscreteDirichletProblemStmt 𝒮 →
  DiscretePotentialTightnessStmt 𝒮 → CellSizeEstimateStmt 𝒮 → BoundedExitTimeRVStmt →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ r' : ℝ, 0 < r' → r' < r →
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))))
      (normalizedExitGreenPotential S r z) (closedBall z r')

/-- Boundary control for both the discrete exit time and the continuum
potential. For any error and failure-probability tolerances, a sufficiently
thin deterministic boundary layer works for all sufficiently small scales. -/
def NormalizedExitBoundaryStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ExpectedExitTimeExplicitBoundStmt 𝒮 → CellSizeEstimateStmt 𝒮 → BoundedExitTimeRVStmt →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ δ : ℝ, 0 < δ → ∀ e : ℝ≥0∞, 0 < e → ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
        δ < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x| ∨
        δ < |normalizedExitGreenPotential S r z ω x|} ≤ e

end MatedCRT
