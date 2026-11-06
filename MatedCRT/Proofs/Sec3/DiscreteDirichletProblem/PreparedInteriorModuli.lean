import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.InteriorSteps
import MatedCRT.Steps.Sec3.DiscreteDirichletProblemPrepared

/-! Prepared-sequence reduction of Lemma 3.5, interior convergence. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Corrected paper, Lemma 3.5 Step 2 (lines 1472–1501): an asymptotic modulus of continuity in probability for the rescaled discrete solutions on
a smaller closed disc. -/
def DirichletDiscreteModulusPreparedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscretePotentialTightnessPreparedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
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

/-- Local uniform convergence from pointwise convergence and the discrete and
continuum moduli, with the corrected prepared-sequence tightness input. -/
theorem dirichletInteriorPreparedStep_of_moduli (𝒮 : SpaceFillingSLEModel)
    (hP : DirichletPointwiseStep 𝒮) (hM : DirichletDiscreteModulusPreparedStep 𝒮)
    (hC : DirichletLimitModulusStep 𝒮) : DirichletInteriorPreparedStep 𝒮 := by
  intro h36 h34 h31 h213 h219 h28 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ F hF
    r' hr' hr'r
  exact uniformInProbability_of_separate_moduli S.P (closedBall z r') (isCompact_closedBall z r')
    (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω)) (dirichletLimit S r z ψ φ)
    (fun y hy => hP h36 h34 h219 h28 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφ F hF y
      (mem_ball.2 ((mem_closedBall.1 hy).trans_lt hr'r)))
    (hM h31 h213 h219 h28 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφ F hF r' hr' hr'r)
    (hC h36 h34 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφ r' hr' hr'r)

/-- Lemma 3.5 from its continuum and boundary steps and the three interior
pointwise and modulus obligations. -/
theorem discreteDirichletProblem_of_prepared_moduli (𝒮 : SpaceFillingSLEModel)
    (hGP : HarmonicBalls.GreenPotentialHolderStmt.{0})
    (h36 : ConvergenceHarmonicFunctionsStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (h213 : MaximumPrincipleStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hlimit : DirichletLimitStep 𝒮)
    (hP : DirichletPointwiseStep 𝒮) (hM : DirichletDiscreteModulusPreparedStep 𝒮)
    (hC : DirichletLimitModulusStep 𝒮) (hboundary : DirichletBoundaryPreparedStep 𝒮) :
    DiscreteDirichletProblemStmt 𝒮 :=
  discreteDirichletProblem_of_prepared_steps 𝒮 hGP h36 h34 h31 h213 h219 h28 hlimit
    (dirichletInteriorPreparedStep_of_moduli 𝒮 hP hM hC) hboundary

end MatedCRT
