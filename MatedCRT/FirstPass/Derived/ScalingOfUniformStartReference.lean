import MatedCRT.FirstPass.Derived.ScalingOfUniformStart
import MatedCRT.FirstPass.Derived.HbdOfReference

/-!
# The scaling theorems of Berestycki-Gwynne Section 6.4 from the uniform-start principle and a reference environment

`ScalingOfUniformStart` supplies the estimates (6.32) and (6.36) of Lemmas 6.9 and 6.10 from the uniform-start
invariance principle `GMS21UniformStartInput`. The remaining localization binder `hbd` (the last assertion of
Lemma 6.13 at radius `1/2`) is supplied by `hbd_of_reference` from the normalized SLE law and a reference
environment with the mating-rigid set of the transfer. The forms below therefore carry only: the Hölder
continuity, the Green kernel and exit time bounds (Lemmas 2.13, 2.14, 2.17, 2.19), the cell size estimate
(Lemma 2.8), the cone scaling of valid environments, the uniform-start principle and the reference environment.
Same conclusions as `hEqLaw_of_scaling` and `isTightMeasureSet_data_interpWalkLaw_of_scaling`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology
open MarkovProcess (ContinuousPath)

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Equicontinuity in law of the quenched walks (`hEqLaw_of_scaling`) from the uniform-start invariance principle
and a reference environment.** The binders `h632`, `h636` and `hbd` are supplied. -/
theorem hEqLaw_of_uniformStart_of_reference {𝒮 : SpaceFillingSLEModel}
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (h28 : CellSizeEstimateStmt 𝒮)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0)) :
    ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R δ ω} ≤ ENNReal.ofReal a :=
  hEqLaw_of_uniformStart h32 h213 h214 h217 h219 hEnvS hN4 hγ hγ2
    (hbd_of_reference hν hνref href hU h28 hγ hγ2) hS hae hε0 hε

/-- **Tightness of the pairs (datum, interpolated quenched walk law) from the uniform-start invariance principle
and a reference environment.** The binders `h632`, `h636` and `hbd` are supplied. -/
theorem isTightMeasureSet_data_interpWalkLaw_of_uniformStart_of_reference {𝒮 : SpaceFillingSLEModel}
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (h28 : CellSizeEstimateStmt 𝒮)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0))
    {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [PolishSpace Data]
    [BorelSpace Data] (D : Ω → Data) (hD : AEMeasurable D S.P) :
    IsTightMeasureSet {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) |
      ∃ n, ν = S.P.map fun ω => (D ω, interpWalkLaw S η' (eps n) ω)} :=
  isTightMeasureSet_data_interpWalkLaw_of_uniformStart h32 h213 h214 h217 h219 hEnvS hN4 hγ hγ2
    (hbd_of_reference hν hνref href hU h28 hγ hγ2) hS hη' hae hε0 hε D hD

end MatedCRT.FirstPass.Derived
