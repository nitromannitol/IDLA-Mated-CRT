import MatedCRT.FirstPass.Derived.LBMReversibilityOfLimit
import MatedCRT.FirstPass.Derived.MarkovTimeChange

/-!
# Reversibility of the LQG measure in the form of Definition 7.3 (BG20 Lemma 7.6)

Berestycki-Gwynne, *Random walks on mated-CRT maps and Liouville Brownian motion* (arXiv 2003.10320),
Definition 7.3 calls a measure `μ` reversible for a family of path laws `P` if
`∫_B P_z[X_t ∈ A] dμ(z) = ∫_A P_w[X_t ∈ B] dμ(w)` for all Borel `A, B` and every `t ≥ 0`
(`MatedCRT.IsReversibleFor`). This is the swap invariance of the space-time measure
`m_t(dz, dw) = μ(dz) P_z(X_t ∈ dw) = μ ⊗ₘ evalLawKernel P t`: evaluating `m_t ∘ swap⁻¹ = m_t` at the
rectangle `B ×ˢ A` gives the identity of Definition 7.3.

* `isReversibleFor_of_compProd_evalLawKernel_swap`: swap invariance of `μ ⊗ₘ evalLawKernel P t` for
  every `t` gives reversibility of `μ` for `P`.
* `ae_isReversibleFor_of_tendsto_law`: for a subsequential limit `ν` in law of the data and the
  interpolated walk laws, the LQG measure is reversible for the limiting family `ν`-almost surely
  (BG20 Lemma 7.6, from `ae_compProd_evalLawKernel_swap_of_tendsto_law`).
* `ae_isInvariantFor_of_tendsto_law`: the same with invariance (take `B = ℂ`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

/-- **Swap invariance of the space-time measure gives reversibility** (BG20 Definition 7.3). If for
every `t ≥ 0` the measure `μ(dz) P_z(X_t ∈ dw)` is invariant under `(z, w) ↦ (w, z)`, then
`∫_B P_z[X_t ∈ A] dμ(z) = ∫_A P_w[X_t ∈ B] dμ(w)` for all Borel `A, B`. -/
theorem isReversibleFor_of_compProd_evalLawKernel_swap {P : PathLawFamily} {μ : Measure ℂ} [SFinite μ]
    (h : ∀ s : ℝ≥0, (μ ⊗ₘ evalLawKernel P s).map Prod.swap = μ ⊗ₘ evalLawKernel P s) :
    IsReversibleFor P μ := by
  intro t A B hA hB
  have hev : Measurable fun x : ContinuousPath ℂ => x t := (continuous_eval_const t).measurable
  have key : ∀ C : Set ℂ, MeasurableSet C → ∀ z,
      evalLawKernel P t z C = (P z : Measure (ContinuousPath ℂ)) {x | x t ∈ C} := fun C hC z => by
    rw [evalLawKernel_apply, Measure.map_apply hev hC]
    rfl
  have h1 : ((μ ⊗ₘ evalLawKernel P t).map Prod.swap) (B ×ˢ A) =
      (μ ⊗ₘ evalLawKernel P t) (B ×ˢ A) := by
    rw [h t]
  rw [Measure.map_apply measurable_swap (hB.prod hA), preimage_swap_prod,
    Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod hB hA] at h1
  simp only [key A hA, key B hB] at h1
  exact h1.symm

/-- **The LQG measure is reversible for a subsequential limit of the walk laws** (BG20 Lemma 7.6, in
the form of Definition 7.3). Under the hypotheses of `ae_compProd_evalLawKernel_swap_of_tendsto_law`,
for `ν`-almost every `(d, P)` the measure `μX d` is reversible for the family `P`. -/
theorem ae_isReversibleFor_of_tendsto_law
    {𝒮 : SpaceFillingSLEModel} (hD27 : DegreeMeasureConvergenceStmt 𝒮) (hM : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {D : ℕ → Ω → X} (hD : ∀ n, AEMeasurable (D n) S.P)
    (μX : X → Measure ℂ) [∀ d, IsLocallyFiniteMeasure (μX d)]
    (hμXD : ∀ n, ∀ᵐ ω ∂S.P, μX (D n ω) = S.μ ω)
    (hπ : ∀ (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ), (∀ z, 0 ≤ ψ z) →
      Continuous fun d => LevyProkhorov.ofMeasure (cutoffWeightedMeasure (μX d) hψ hψc 6))
    {ν : Measure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hlaw : ∀ F : (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ p, F p ∂ν))) :
    ∀ᵐ p ∂ν, IsReversibleFor p.2 (μX p.1) :=
  (ae_compProd_evalLawKernel_swap_of_tendsto_law hD27 hM hγ hγ2 hS hη' hae hε0 hε hEqLaw hD μX
    hμXD hπ hlaw).mono fun _ hp => isReversibleFor_of_compProd_evalLawKernel_swap hp

/-- **The LQG measure is invariant for a subsequential limit of the walk laws** (BG20 Lemma 7.6 and
Definition 7.3, taking `B = ℂ`). Under the hypotheses of `ae_compProd_evalLawKernel_swap_of_tendsto_law`,
for `ν`-almost every `(d, P)` the measure `μX d` is invariant for the family `P`. -/
theorem ae_isInvariantFor_of_tendsto_law
    {𝒮 : SpaceFillingSLEModel} (hD27 : DegreeMeasureConvergenceStmt 𝒮) (hM : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {D : ℕ → Ω → X} (hD : ∀ n, AEMeasurable (D n) S.P)
    (μX : X → Measure ℂ) [∀ d, IsLocallyFiniteMeasure (μX d)]
    (hμXD : ∀ n, ∀ᵐ ω ∂S.P, μX (D n ω) = S.μ ω)
    (hπ : ∀ (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ), (∀ z, 0 ≤ ψ z) →
      Continuous fun d => LevyProkhorov.ofMeasure (cutoffWeightedMeasure (μX d) hψ hψc 6))
    {ν : Measure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hlaw : ∀ F : (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ p, F p ∂ν))) :
    ∀ᵐ p ∂ν, IsInvariantFor p.2 (μX p.1) :=
  (ae_isReversibleFor_of_tendsto_law hD27 hM hγ hγ2 hS hη' hae hε0 hε hEqLaw hD μX hμXD hπ
    hlaw).mono fun _ hp => hp.isInvariantFor

end MatedCRT.FirstPass.Derived
