import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section4

/-! # Lemma 4.8: subsequential obstacle bounds and distributional Laplacians -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls Laplacian
open scoped ENNReal

/-- The rescaled discrete obstacle. -/
noncomputable def rescaledMatedObstacle {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ρ t ε : ℝ) (ω : Ω) : ℂ → ℝ :=
  rescale (S.mε ε) ε (S.η ω) (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t)

/-- Selection of a deterministic subsequence on which the discrete obstacle converges at
every point away from the pole, and the rescaled discrete obstacle bounds hold. This includes
the identification of the source vertex in the Green-kernel convergence. -/
def OdometerObstacleApproximationStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  UniformConvergenceGreenKernelStmt 𝒮 → DiscreteBasicPropertiesStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t →
    (∀ n x, x ∈ closedBall (0 : ℂ) ρ →
      rescaledMatedObstacle S ρ t (εs (φ n)) ω x ≤
        rescaledMatedLeastSupersolution S ρ t (εs (φ n)) ω x ∧
      rescaledMatedLeastSupersolution S ρ t (εs (φ n)) ω x ≤ 0) ∧
    ∀ x ∈ closedBall (0 : ℂ) ρ, x ≠ 0 →
      Tendsto (fun n => rescaledMatedObstacle S ρ t (εs (φ n)) ω x) atTop
        (𝓝 (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x))

/-- Discrete-to-continuum passage against test functions for all uniform subsequential limits,
including tests supported in the non-coincidence set containing the pole. -/
def OdometerDistributionalLimitStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteDirichletProblemStmt 𝒮 → ConvergenceNormalizedExitTimeStmt 𝒮 →
  SubsequentialConvergenceStmt 𝒮 → DiscreteLaplacianBoundStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t → ∀ w : ℂ → ℝ,
    (ContinuousOn w (closedBall 0 ρ) ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εs (φ (ψ k))) ω)
        w atTop (closedBall 0 ρ)) →
    (∀ f : ℂ → ℝ, IsTestFunction (ball 0 ρ) f → 0 ≤ f →
      0 ≤ ∫ x, w x * Δ f x) ∧
    (∀ f : ℂ → ℝ, IsTestFunction (ball 0 ρ) f → 0 ≤ f →
      Integrable f (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) →
      ∫ x, w x * Δ f x ≤ ∫ x, f x ∂(ENNReal.ofReal (S.c₀ / 6) • S.μ ω)) ∧
    (∀ f : ℂ → ℝ, IsTestFunction
        {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x < w x} f →
      Integrable f (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) ∧
      ∫ x, w x * Δ f x = ∫ x, f x ∂(ENNReal.ofReal (S.c₀ / 6) • S.μ ω))

/-- Lemma 4.8 follows by composing the deterministic subsequences and passing the discrete
obstacle inequalities to each uniform limit. -/
theorem subsequentialProperties_of_steps (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h46 : SubsequentialConvergenceStmt 𝒮)
    (h43 : DiscreteBasicPropertiesStmt 𝒮) (h44 : DiscreteLaplacianBoundStmt 𝒮)
    (h213 : MaximumPrincipleStmt 𝒮) (hobs : OdometerObstacleApproximationStep 𝒮)
    (hlap : OdometerDistributionalLimitStep 𝒮) : SubsequentialPropertiesStmt 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS εs hε hε0
  obtain ⟨φ, hφ, hφae⟩ := hobs h33 h43 γ hγ hγ' ρ hρ hρ' Ω S hS εs hε hε0
  obtain ⟨χ, hχ, hχae⟩ := hlap h35 h37 h46 h44 h213 γ hγ hγ' ρ hρ hρ' Ω S hS
    (εs ∘ φ) (fun n => hε _) (hε0.comp hφ.tendsto_atTop)
  refine ⟨φ ∘ χ, hφ.comp hχ, ?_⟩
  filter_upwards [hφae, hχae] with ω ho hl
  intro t ht w hw
  obtain ⟨hwc, ψ, hψ, hconv⟩ := hw
  have htest := hl t ht w ⟨hwc, ψ, hψ, hconv⟩
  have hint : LocallyIntegrableOn w (ball 0 ρ) :=
    (hwc.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball
  have hge : LaplacianGE w 0 (ball 0 ρ) := by
    refine ⟨hint, ?_⟩
    intro f hf hf0
    exact ⟨integrable_zero_measure, by simpa using htest.1 f hf hf0⟩
  have heq : HasLaplacian w (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) 0
      {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x < w x} := by
    refine ⟨hint.mono_set (fun x hx => hx.1), ?_⟩
    intro f hf
    obtain ⟨hfi, hfe⟩ := htest.2.2 f hf
    exact ⟨hfi, integrable_zero_measure, by simpa using hfe⟩
  refine ⟨?_, hge, ⟨hint, htest.2.1⟩, heq⟩
  intro x hx
  have hwx := hconv.tendsto_at hx
  refine ⟨le_of_tendsto hwx (Filter.Eventually.of_forall fun n =>
    (ho t ht).1 (χ (ψ n)) x hx |>.2), ?_⟩
  intro hx0
  have hob := ((ho t ht).2 x hx hx0).comp (hχ.tendsto_atTop.comp hψ.tendsto_atTop)
  exact le_of_tendsto_of_tendsto hob hwx (Filter.Eventually.of_forall fun n =>
    (ho t ht).1 (χ (ψ n)) x hx |>.1)

end MatedCRT
