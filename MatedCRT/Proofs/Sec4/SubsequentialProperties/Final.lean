import MatedCRT.Proofs.Sec4.SubsequentialProperties.Equality
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ExitCDF

/-!
# Lemma 4.8: final form

* `odometerDistributionalLimitCorrectedStep_of_greenKernel`: the step `OdometerDistributionalLimitCorrectedStep`
  (Steps 2 and 3 of the proof of Lemma 4.8) holds given Lemma 3.3. The deterministic subsequence is composed of three
  extractions: Lemma 3.5 with hat data on rational discs (`ae_tendsto_hatDirichletAtCentre`), Lemma 3.3 uniformly on
  annuli (`ae_greenKernel_unif_annuli`) and Lemma 3.7 on `B_ρ` (`exists_strictMono_ae_tendstoUniformlyOn`). The three
  items are `odometer_integral_mul_laplacian_nonneg`, `odometer_integral_mul_laplacian_le` and
  `odometer_hasLaplacian_noncoincidence`; `0 < c₀/6` is `matedCRTScalingConstantPositive` (x3).
* `subsequentialProperties_of_inputs`: **Lemma 4.8** from Lemmas 3.3, 3.5, 3.7 and 2.13 (Draft statements; 3.3, 3.5,
  3.7 are proved elsewhere from their inputs, 2.13 is the corrected maximum principle). Lemma 4.3, the corrected
  Lemma 4.4 and both steps are discharged; neither the Draft Lemma 4.4 nor Lemma 4.6 is used.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls Real Laplacian

/-- Uniform convergence along a sequence passes to subsequences. -/
theorem TendstoUniformlyOn.comp_subseq {F : ℕ → ℂ → ℝ} {f : ℂ → ℝ} {K : Set ℂ}
    (h : TendstoUniformlyOn F f atTop K) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    TendstoUniformlyOn (fun k => F (ψ k)) f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro δ hδ
  exact hψ.eventually (h δ hδ)

/-- **`OdometerDistributionalLimitCorrectedStep` from Lemma 3.3** (Steps 2 and 3 of the proof of Lemma 4.8). -/
theorem odometerDistributionalLimitCorrectedStep_of_greenKernel (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) : OdometerDistributionalLimitCorrectedStep 𝒮 := by
  intro h35 h37 h44 h213 γ hγ hγ' ρ hρ hρ' Ω _ S hS εs hε hε0
  obtain ⟨φ₁, hφ₁, hdirae⟩ := ae_tendsto_hatDirichletAtCentre 𝒮 h35 hγ hγ' hρ hρ' S hS hε hε0
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

/-- x3's `OdometerDistributionalLimitStep` from Lemma 3.3. -/
theorem odometerDistributionalLimitStep_of_greenKernel (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) : OdometerDistributionalLimitStep 𝒮 :=
  odometerDistributionalLimitStep_of_corrected (odometerDistributionalLimitCorrectedStep_of_greenKernel 𝒮 h33)

/-- **Lemma 4.8** (lemma:subsequential-properties, l.1774 of paper/idla_mated_crt-corrected.tex) from Lemmas 3.3,
3.5, 3.7 and 2.13. -/
theorem subsequentialProperties_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮) :
    SubsequentialPropertiesStmt 𝒮 :=
  subsequentialProperties_of_distributionalLimit 𝒮 h33 h35 h37 h213
    (odometerDistributionalLimitCorrectedStep_of_greenKernel 𝒮 h33)

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.subsequentialProperties_of_inputs

section Audit

open MatedCRT

variable (𝒮 : SpaceFillingSLEModel)

/-- **Lemma 4.8** from Lemmas 3.3, 3.5, 3.7 and 2.13. -/
example (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮) :
    SubsequentialPropertiesStmt 𝒮 :=
  subsequentialProperties_of_inputs 𝒮 h33 h35 h37 h213

end Audit
