import MatedCRT.FirstPass.Derived.LBMReversibilityIsReversible
import MatedCRT.FirstPass.Derived.LBMReversibilityLowerScaling
import MatedCRT.FirstPass.Derived.MepsTendstoAtTop

/-!
# Reversibility of the LQG measure for a subsequential limit, from the uniform-start input

BG20 Lemma 7.6 (`ae_isReversibleFor_of_tendsto_law`) uses the scaling input `m_ε ≍ ε⁻¹`
(`MepsScalingInput`, eq:meps-scaling) only through `m_{ε_n} → ∞` along the given sequence
(`ae_compProd_evalLawKernel_swap_of_tendsto_law_of_tendsto_mε`). For every valid environment and
every sequence of positive `ε_n → 0`, `m_{ε_n} → ∞` follows from the Green kernel lower bound
(Lemma 2.13), the exit-time upper bound (Lemma 2.14) and the uniform-start invariance principle
([GMS21, Theorem 3.4]) (`tendsto_mε_atTop_of_uniformStart`). So the LQG measure is reversible, and
hence invariant, for a subsequential limit of the walk laws (BG20 Definition 7.3) with
`MepsScalingInput` replaced by these three inputs.

* `ae_isReversibleFor_of_tendsto_law_of_uniformStart`: for `ν`-almost every `(d, P)`, the measure
  `μX d` is reversible for the family `P`.
* `ae_isInvariantFor_of_tendsto_law_of_uniformStart`: the same with invariance.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

/-- **The LQG measure is reversible for a subsequential limit of the walk laws** (BG20 Lemma 7.6, in
the form of Definition 7.3), with the scaling input `m_ε ≍ ε⁻¹` replaced by the Green kernel lower
bound (Lemma 2.13), the exit-time upper bound (Lemma 2.14) and the uniform-start invariance
principle. Under the remaining hypotheses of `ae_isReversibleFor_of_tendsto_law`, for `ν`-almost
every `(d, P)` the measure `μX d` is reversible for the family `P`. -/
theorem ae_isReversibleFor_of_tendsto_law_of_uniformStart
    {𝒮 : SpaceFillingSLEModel} (hD27 : DegreeMeasureConvergenceStmt 𝒮)
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
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
  (ae_compProd_evalLawKernel_swap_of_tendsto_law_of_tendsto_mε hD27 hγ hγ2 hS hη' hae hε0 hε
    (tendsto_mε_atTop_of_uniformStart h213 h214 hN4 hγ hγ2 hS hε0 hε) hEqLaw hD μX hμXD hπ
    hlaw).mono fun _ hp => isReversibleFor_of_compProd_evalLawKernel_swap hp

/-- **The LQG measure is invariant for a subsequential limit of the walk laws** (BG20 Lemma 7.6 and
Definition 7.3, taking `B = ℂ`), with the scaling input `m_ε ≍ ε⁻¹` replaced by the Green kernel
lower bound (Lemma 2.13), the exit-time upper bound (Lemma 2.14) and the uniform-start invariance
principle. Under the remaining hypotheses of `ae_isInvariantFor_of_tendsto_law`, for `ν`-almost
every `(d, P)` the measure `μX d` is invariant for the family `P`. -/
theorem ae_isInvariantFor_of_tendsto_law_of_uniformStart
    {𝒮 : SpaceFillingSLEModel} (hD27 : DegreeMeasureConvergenceStmt 𝒮)
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
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
  (ae_isReversibleFor_of_tendsto_law_of_uniformStart hD27 h213 h214 hN4 hγ hγ2 hS hη' hae hε0 hε
    hEqLaw hD μX hμXD hπ hlaw).mono fun _ hp => hp.isInvariantFor

end MatedCRT.FirstPass.Derived
