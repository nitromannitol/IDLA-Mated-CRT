import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions

/-! Corrected Lemma 3.5: boundary data are evaluated on the projected cell
representatives, as in corrected paper lines 1392–1402 [C13]. -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- Lemma 3.5 [C1, C13], with boundary data Hölder on the closed disk and
cell representatives projected to that disk before evaluating those data. -/
def DiscreteDirichletProblemCorrectedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ φ : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M) →
    IsHolderContinuousOn ψ (ball z r) → IsHolderContinuousOn φ (closedBall z r) →
  ∀ F : ℝ → Ω → ℤ → ℝ,
    (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b))) →
  ∃ fbar : Ω → ℂ → ℝ,
    (∀ᵐ ω ∂S.P, ContinuousOn (fbar ω) (closedBall z r) ∧
      HasLaplacian (fbar ω) ((S.μ ω).withDensity fun x => ENNReal.ofReal (S.c₀ * ψ x))
        ((S.μ ω).withDensity fun x => ENNReal.ofReal (-(S.c₀ * ψ x))) (ball z r) ∧
      (∀ x ∈ sphere z r, fbar ω x = φ x) ∧ IsHolderContinuousOn (fbar ω) (closedBall z r)) ∧
    TendstoUniformlyOnInProbability S.P (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω)) fbar (closedBall z r)

end MatedCRT
