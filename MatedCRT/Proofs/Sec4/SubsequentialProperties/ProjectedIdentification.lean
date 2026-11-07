import MatedCRT.Proofs.Sec4.SubsequentialProperties.ProjectedHatDirichlet
import MatedCRT.Proofs.Sec4.SubsequentialProperties.Final
import MatedCRT.Proofs.Sec4.SubsequentialProperties.PreparedIdentification
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.CorrectedDirichletInputs

/-! Distributional identification conditional on hat projection stability. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls Real Laplacian
open scoped ENNReal

/-- Discrete-to-continuum passage against test functions for all uniform subsequential limits along a deterministic
subsequence, including tests supported in the non-coincidence set containing the pole: `OdometerDistributionalLimitStep`
with the corrected Lemma 4.4 and without Lemma 4.6 (Steps 2 and 3 of the proof of Lemma 4.8, l.1803-1915). -/
def OdometerDistributionalLimitProjectedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteDirichletProblemCorrectedStmt 𝒮 → ConvergenceNormalizedExitTimeStmt 𝒮 →
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


theorem odometerDistributionalLimitProjectedStep_of_greenKernel (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hstability : HatDirichletProjectionStabilityStep 𝒮) : OdometerDistributionalLimitProjectedStep 𝒮 := by
  intro h35 h37 h44 h213 γ hγ hγ' ρ hρ hρ' Ω _ S hS εs hε hε0
  obtain ⟨φ₁, hφ₁, hdirae⟩ := ae_tendsto_hatDirichletAtCentre_of_projection_stability 𝒮 h35 h28 hstability hγ hγ' hρ hρ' S hS hε hε0
  obtain ⟨φ₂, hφ₂, hgae⟩ := ae_greenKernel_unif_annuli 𝒮 h33 hγ hγ' hρ hρ' S hS (εs := εs ∘ φ₁)
    (fun n => hε _) (hε0.comp hφ₁.tendsto_atTop)
  obtain ⟨qbar, hqae, hqconvP⟩ := h37 γ hγ hγ' ρ hρ hρ' Ω S hS ρ 0 hρ subset_rfl
  obtain ⟨φ₃, hφ₃, hqae'⟩ := exists_strictMono_ae_tendstoUniformlyOn hqconvP (εs := εs ∘ φ₁ ∘ φ₂)
    (fun n => hε _) ((hε0.comp hφ₁.tendsto_atTop).comp hφ₂.tendsto_atTop)
  have hc : 0 < S.c₀ / 6 := matedCRTScalingConstantPositive 𝒮 γ hγ hγ' Ω S hS
  refine ⟨φ₁ ∘ φ₂ ∘ φ₃, hφ₁.comp (hφ₂.comp hφ₃), ?_⟩
  filter_upwards [hdirae, hgae, hqae, hqae', hS.ae_isLocallyFiniteMult hγ hγ' (adjacentCellsMeetAeStep 𝒮),
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ' Ω S hS, h213 γ hγ hγ' Ω S hS, h44 γ hγ hγ' ρ hρ hρ' Ω S hS,
    hS.ae_tendsto_cocompact, hS.isAreaParametrized, hS.ae_vertexOf_zero_eq_zero] with
    ω hdir hg hq hqconv hlf hcells hmax h44ω hp harea hv0
  intro t ht w hw
  obtain ⟨hwc, ψ, hψ, hconv⟩ := hw
  obtain ⟨hqc, hqlap, -⟩ := hq
  have hmono : StrictMono (φ₂ ∘ φ₃ ∘ ψ) := hφ₂.comp (hφ₃.comp hψ)
  have hεk : ∀ k, 0 < εs (φ₁ (φ₂ (φ₃ (ψ k)))) := fun k => hε _
  have hεk0 : Tendsto (fun k => εs (φ₁ (φ₂ (φ₃ (ψ k))))) atTop (𝓝 0) :=
    hε0.comp (hφ₁.comp hmono).tendsto_atTop
  have hdirk : ∀ (q₁ q₂ s : ℚ) (n : ℕ) (j l : ℤ), (0 : ℝ) < s → ‖ratPoint q₁ q₂‖ + s < ρ →
      Tendsto (fun k => hatDirichletAtCentre S (ratPoint q₁ q₂) s n j l (εs (φ₁ (φ₂ (φ₃ (ψ k))))) ω) atTop
        (𝓝 (circleAverage (hat n j l) (ratPoint q₁ q₂) s)) :=
    fun q₁ q₂ s n j l hs hzr => (hdir q₁ q₂ s n j l hs hzr).comp hmono.tendsto_atTop
  have hgk : ∀ j : ℕ, ∀ᶠ k in atTop, ∀ x ∈ closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2)),
      |rescaledGreenKernel S ρ (εs (φ₁ (φ₂ (φ₃ (ψ k))))) ω x - S.c₀ / 6 * greenFunction (ball 0 ρ) 0 x| ≤
        1 / ((j : ℝ) + 1) :=
    fun j => (hφ₃.comp hψ).tendsto_atTop.eventually (hg j)
  have hqk : TendstoUniformlyOn (fun k => rescale (S.mε (εs (φ₁ (φ₂ (φ₃ (ψ k)))))) (εs (φ₁ (φ₂ (φ₃ (ψ k)))))
      (S.η ω) (normExitTime (S.mult (εs (φ₁ (φ₂ (φ₃ (ψ k))))) ω)
        (interiorCellVertices (εs (φ₁ (φ₂ (φ₃ (ψ k))))) (S.η ω) (ball 0 ρ)))) (qbar ω) atTop
      (closedBall 0 ρ) :=
    TendstoUniformlyOn.comp_subseq hqconv hψ.tendsto_atTop
  have hconv' : TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εs (φ₁ (φ₂ (φ₃ (ψ k))))) ω)
      w atTop (closedBall 0 ρ) := hconv
  refine ⟨odometer_integral_mul_laplacian_nonneg S ω hρ harea hp hlf hcells hmax hεk hεk0 hdirk
      (fun ε hε' a ha => ((h44ω t ε ht hε').2.1 a ha).1) hwc hconv',
    (odometer_integral_mul_laplacian_le S ω hρ harea hp hlf hcells hmax hεk hεk0 hdirk
      (fun ε hε' a ha => ((h44ω t ε ht hε').2.1 a ha).2) hqc hqlap hqk hwc hconv').2,
    odometer_hasLaplacian_noncoincidence S ω hρ harea hp hlf hcells hmax hεk hεk0 hdirk hv0 hgk hc ht
      (fun ε hε' a ha => (h44ω t ε ht hε').1 a ha) (fun ε hε' a ha => ((h44ω t ε ht hε').2.1 a ha).2)
      hqc hqlap hqk hwc hconv'⟩


theorem subsequentialProperties_of_projected (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hobs : OdometerObstacleApproximationStep 𝒮) (hlap : OdometerDistributionalLimitProjectedStep 𝒮) :
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

/-- Prepared every-limit identification under the corrected Dirichlet statement
and the explicit boundary projection stability obligation. -/
theorem odometerPropertiesPreparedIdentificationStep_of_projection_stability
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮)
    (h213 : MaximumPrincipleStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hstability : HatDirichletProjectionStabilityStep 𝒮) :
    OdometerPropertiesPreparedIdentificationStep 𝒮 :=
  odometerPropertiesPreparedIdentificationStep_of_subsequentialProperties 𝒮
    (subsequentialProperties_of_projected 𝒮 h33 h35 h37 h213 (odometerObstacleApproximationStep 𝒮)
      (odometerDistributionalLimitProjectedStep_of_greenKernel 𝒮 h33 h28 hstability))

end MatedCRT

#print axioms MatedCRT.odometerPropertiesPreparedIdentificationStep_of_projection_stability
