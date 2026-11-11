import MatedCRT.Steps.Sec4.SubsequentialProperties
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final

/-!
# Lemma 4.8 from the corrected Lemma 4.4, without Lemma 4.6

`subsequentialProperties_of_steps` (MatedCRT/Steps/Sec4/SubsequentialProperties.lean) passes the Draft Lemma 4.4
(`DiscreteLaplacianBoundStmt`, false in Lean: `not_discreteLaplacianBoundStmt`) and the Draft Lemma 4.6
(`SubsequentialConvergenceStmt`, whose all-sequences event is not justified) to the step
`OdometerDistributionalLimitStep`. This file reroutes Lemma 4.8:

* `OdometerDistributionalLimitCorrectedStep` is `OdometerDistributionalLimitStep` with the corrected Lemma 4.4
  (`DiscreteLaplacianBoundCorrectedStmt`) in place of the Draft one and without Lemma 4.6. The proof of Lemma 4.8
  (paper/idla_mated_crt-corrected.tex, l.1786-1915) uses only the conjunct `0 ≤ Δ^ε w̃^ε_t ≤ (deg^ε)⁻¹` on
  `V^ε(B_ρ) \ V^ε(∂B_ρ)` and the equality `Δ^ε w̃^ε_t = (deg^ε)⁻¹` on `Λ^ε_t`, which the corrected form keeps, and it
  only considers uniform subsequential limits that are given (the hypothesis on `w`), so Lemma 4.6 is not used.
* `subsequentialProperties_of_corrected`: **Lemma 4.8** from Lemmas 3.3, 3.5, 3.7 and 2.13 (Draft) and the two steps,
  with Lemma 4.3 (`discreteBasicProperties`) and the corrected Lemma 4.4 (`discreteLaplacianBoundCorrected`)
  discharged.
* `odometerDistributionalLimitStep_of_corrected`: the corrected step implies `OdometerDistributionalLimitStep`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls Laplacian
open scoped ENNReal

/-- Discrete-to-continuum passage against test functions for all uniform subsequential limits along a deterministic
subsequence, including tests supported in the non-coincidence set containing the pole: `OdometerDistributionalLimitStep`
with the corrected Lemma 4.4 and without Lemma 4.6 (Steps 2 and 3 of the proof of Lemma 4.8, l.1803-1915). -/
def OdometerDistributionalLimitCorrectedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteDirichletProblemStmt 𝒮 → ConvergenceNormalizedExitTimeStmt 𝒮 →
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
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

/-- The corrected step implies `OdometerDistributionalLimitStep` (its Lemma 4.6 and Draft 4.4 antecedents are
unused). -/
theorem odometerDistributionalLimitStep_of_corrected {𝒮 : SpaceFillingSLEModel}
    (hlap : OdometerDistributionalLimitCorrectedStep 𝒮) : OdometerDistributionalLimitStep 𝒮 :=
  fun h35 h37 _ _ h213 => hlap h35 h37 (discreteLaplacianBoundCorrected 𝒮) h213

/-- **Lemma 4.8** (lemma:subsequential-properties, l.1774 of paper/idla_mated_crt-corrected.tex) from Lemmas 3.3, 3.5,
3.7 and 2.13, the obstacle approximation step and the corrected distributional limit step. Lemma 4.3 and the corrected
Lemma 4.4 are discharged; neither the Draft Lemma 4.4 nor Lemma 4.6 is used. -/
theorem subsequentialProperties_of_corrected (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hobs : OdometerObstacleApproximationStep 𝒮) (hlap : OdometerDistributionalLimitCorrectedStep 𝒮) :
    SubsequentialPropertiesStmt 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS εs hε hε0
  obtain ⟨φ, hφ, hφae⟩ := hobs h33 (discreteBasicProperties 𝒮) γ hγ hγ' ρ hρ hρ' Ω S hS εs hε hε0
  obtain ⟨χ, hχ, hχae⟩ := hlap h35 h37 (discreteLaplacianBoundCorrected 𝒮) h213 γ hγ hγ' ρ hρ hρ' Ω S hS
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
