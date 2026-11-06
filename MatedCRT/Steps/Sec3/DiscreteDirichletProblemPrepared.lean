import MatedCRT.Steps.Sec3.DiscreteDirichletProblem
import MatedCRT.Draft.Section3Prepared

/-! Prepared-sequence obligations for Lemma 3.5, corrected paper proof lines 1474–1522.
The interior and boundary steps remain open and must handle almost-sure eventual bounds. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- Steps 1 and 2: pointwise identification and local uniform convergence. The harmonic
component uses the scaled boundary-data part of corrected Lemma 3.1. -/
def DirichletInteriorPreparedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConvergenceHarmonicFunctionsStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
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
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω))
      (dirichletLimit S r z ψ φ) (closedBall z r')

/-- Step 3: the exit-time barrier controls the discrepancy in a thin boundary layer.
The failure tolerance is explicit because the continuum barrier is random. -/
def DirichletBoundaryPreparedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  HarmonicBalls.GreenPotentialHolderStmt.{0} →
  ConvergenceHarmonicFunctionsStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
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
  ∀ δ : ℝ, 0 < δ → ∀ e : ℝ≥0∞, 0 < e → ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
        δ < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
          dirichletLimit S r z ψ φ ω x|} ≤ e

/-- Lemma 3.5 from the continuum, local convergence, and boundary steps. -/
theorem discreteDirichletProblem_of_prepared_steps (𝒮 : SpaceFillingSLEModel)
    (hGP : HarmonicBalls.GreenPotentialHolderStmt.{0})
    (h36 : ConvergenceHarmonicFunctionsStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (h213 : MaximumPrincipleStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hlimit : DirichletLimitStep 𝒮)
    (hinterior : DirichletInteriorPreparedStep 𝒮) (hboundary : DirichletBoundaryPreparedStep 𝒮) :
    DiscreteDirichletProblemStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ F hF
  refine ⟨dirichletLimit S r z ψ φ,
    hlimit hGP γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφ, ?_⟩
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨r', hr'0, hr'r, hb⟩ := hboundary hGP h36 h34 h31 h213 h219 h28
    γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφ F hF δ hδ (e / 2) he2
  have hi := ENNReal.tendsto_nhds_zero.1
    (hinterior h36 h34 h31 h213 h219 h28 γ hγ hγ2 ρ hρ hρ1 Ω S hS
      r z hr hball ψ φ hψb hψh hφ F hF r' hr'0 hr'r δ hδ) (e / 2) he2
  filter_upwards [hi, hb] with ε hi hb
  calc
    S.P {ω | ∃ x ∈ closedBall z r,
        δ < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x - dirichletLimit S r z ψ φ ω x|} ≤
      S.P ({ω | ∃ x ∈ closedBall z r',
        δ < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x - dirichletLimit S r z ψ φ ω x|} ∪
      {ω | ∃ x ∈ closedBall z r \ closedBall z r',
        δ < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x - dirichletLimit S r z ψ φ ω x|}) := by
      apply measure_mono
      intro ω hω
      obtain ⟨x, hx, herr⟩ := hω
      by_cases hx' : x ∈ closedBall z r'
      · exact Or.inl ⟨x, hx', herr⟩
      · exact Or.inr ⟨x, ⟨hx, hx'⟩, herr⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hi hb
    _ = e := ENNReal.add_halves e

end MatedCRT
