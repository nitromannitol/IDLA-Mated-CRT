import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.Limit
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.SeparateModuli
import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime

/-!
# Lemma 3.5, Steps 1-2: reduction of the interior step to pointwise convergence and two moduli

`DirichletInteriorStep` (local uniform convergence in probability on `cl B_{r'}(z)`, `r' < r`) follows from
(`uniformInProbability_of_separate_moduli`):

* `DirichletPointwiseStep`: pointwise convergence in probability at every `y ∈ B_r(z)` (paper, Step 1, lines
  1323-1343: the discrete solution is `m_ε` times the expected exit value of `φ ∘ η` minus the discrete Green potential
  of `ψ ∘ η` (Lawler-Limic, Corollary 6.2.4); Lemma 3.6 and Lemma 3.4 give the limits);
* `DirichletDiscreteModulusStep`: an asymptotic modulus of continuity in probability for the rescaled discrete
  solutions on `cl B_{r'}(z)` (Step 2, lines 1346-1354: maximum principle, Lemma 2.19, Lemma 3.1);
* `DirichletLimitModulusStep`: a modulus of continuity in probability for the continuum candidate on `cl B_{r'}(z)`
  (it is a.s. continuous on `cl B_r(z)`, `dirichletLimitStep_of_volumeGrowth`).
-/

open MeasureTheory Metric Filter Topology Set _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- Step 1 of Lemma 3.5: pointwise convergence in probability inside the disc. -/
def DirichletPointwiseStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConvergenceHarmonicFunctionsStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
  ExpectedExitTimeExplicitBoundStmt 𝒮 → CellSizeEstimateStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ φ : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M) →
    IsHolderContinuousOn ψ (ball z r) →
    (∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s))) →
  ∀ F : ℝ → Ω → ℤ → ℝ,
    (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b)) →
  ∀ y ∈ ball z r,
    TendstoInProbability S.P (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω) y)
      (fun ω => dirichletLimit S r z ψ φ ω y)

/-- Step 2 of Lemma 3.5: an asymptotic modulus of continuity in probability for the rescaled discrete solutions on
a smaller closed disc. -/
def DirichletDiscreteModulusStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscretePotentialTightnessAeStep 𝒮 → MaximumPrincipleStmt 𝒮 →
  ExpectedExitTimeExplicitBoundStmt 𝒮 → CellSizeEstimateStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ φ : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M) →
    IsHolderContinuousOn ψ (ball z r) →
    (∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s))) →
  ∀ F : ℝ → Ω → ℤ → ℝ,
    (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b)) →
  ∀ r' : ℝ, 0 < r' → r' < r →
  ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ closedBall z r', ∃ y ∈ closedBall z r', dist x y < δ ∧
      t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x - rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e

/-- The continuum candidate has a modulus of continuity in probability on a smaller closed disc. -/
def DirichletLimitModulusStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConvergenceHarmonicFunctionsStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ φ : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M) →
    IsHolderContinuousOn ψ (ball z r) →
    (∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s))) →
  ∀ r' : ℝ, 0 < r' → r' < r →
  ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
    S.P {ω | ∃ x ∈ closedBall z r', ∃ y ∈ closedBall z r', dist x y < δ ∧
      t < |dirichletLimit S r z ψ φ ω x - dirichletLimit S r z ψ φ ω y|} ≤ e

/-- **Lemma 3.5, interior step**, from pointwise convergence and the two moduli. -/
theorem dirichletInteriorStep_of_moduli (𝒮 : SpaceFillingSLEModel)
    (hAe : DiscretePotentialTightnessAeStep 𝒮) (hP : DirichletPointwiseStep 𝒮)
    (hM : DirichletDiscreteModulusStep 𝒮) (hC : DirichletLimitModulusStep 𝒮) :
    DirichletInteriorStep 𝒮 := by
  intro h36 h34 _ h213 h219 h28 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ F hF
    r' hr' hr'r
  exact uniformInProbability_of_separate_moduli S.P (closedBall z r') (isCompact_closedBall z r')
    (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω)) (dirichletLimit S r z ψ φ)
    (fun y hy => hP h36 h34 h219 h28 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφ F hF y
      (mem_ball.2 ((mem_closedBall.1 hy).trans_lt hr'r)))
    (hM hAe h213 h219 h28 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφ F hF r' hr' hr'r)
    (hC h36 h34 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφ r' hr' hr'r)

end MatedCRT
