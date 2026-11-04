import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3
import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import HarmonicBalls.Draft.Section2

/-!
# Lemma 3.5: convergence of the discrete Dirichlet problem

The continuum candidate is the harmonic extension of the boundary data minus the Green
potential of the source. The three steps isolate its continuum properties, convergence on
smaller closed balls, and the boundary barrier. The local step uses the N1-corrected
Lemma 3.1: the boundary Hölder constant is of order `ε⁻¹`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- The continuum candidate in Lemma 3.5, expressed using the exit distribution and Green
potential. The boundary values are prescribed directly outside the open ball. -/
noncomputable def dirichletLimit {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (r : ℝ) (z : ℂ) (ψ φ : ℂ → ℝ) (ω : Ω) (x : ℂ) : ℝ := by
  classical
  exact if x ∈ ball z r then
    (∫ b, φ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
      ∂planarBrownianMotion x) -
      S.c₀ * ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂S.μ ω
  else φ x

/-- The continuum candidate solves the signed Poisson problem and is Hölder continuous up to
the boundary. Its Green-potential regularity uses HB22 Proposition 2.5. -/
def DirichletLimitStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  HarmonicBalls.GreenPotentialHolderStmt.{0} →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ φ : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M) →
    IsHolderContinuousOn ψ (ball z r) →
    (∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s))) →
  ∀ᵐ ω ∂S.P,
    ContinuousOn (dirichletLimit S r z ψ φ ω) (closedBall z r) ∧
    HasLaplacian (dirichletLimit S r z ψ φ ω)
      ((S.μ ω).withDensity fun x => ENNReal.ofReal (S.c₀ * ψ x))
      ((S.μ ω).withDensity fun x => ENNReal.ofReal (-(S.c₀ * ψ x))) (ball z r) ∧
    (∀ x ∈ sphere z r, dirichletLimit S r z ψ φ ω x = φ x) ∧
    IsHolderContinuousOn (dirichletLimit S r z ψ φ ω) (closedBall z r)

/-- Steps 1 and 2: pointwise identification and local uniform convergence. The harmonic
component uses the scaled boundary-data part of corrected Lemma 3.1. -/
def DirichletInteriorStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConvergenceHarmonicFunctionsStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
  DiscretePotentialTightnessCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
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
def DirichletBoundaryStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  HarmonicBalls.GreenPotentialHolderStmt.{0} →
  ConvergenceHarmonicFunctionsStmt 𝒮 → IntegralConvergenceGreenFunctionStmt 𝒮 →
  DiscretePotentialTightnessCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
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
theorem discreteDirichletProblem_of_steps (𝒮 : SpaceFillingSLEModel)
    (hGP : HarmonicBalls.GreenPotentialHolderStmt.{0})
    (h36 : ConvergenceHarmonicFunctionsStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h31 : DiscretePotentialTightnessCorrectedStmt 𝒮)
    (h213 : MaximumPrincipleStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hlimit : DirichletLimitStep 𝒮)
    (hinterior : DirichletInteriorStep 𝒮) (hboundary : DirichletBoundaryStep 𝒮) :
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
