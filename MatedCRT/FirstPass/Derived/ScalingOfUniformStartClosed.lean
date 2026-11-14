import MatedCRT.FirstPass.Derived.ScalingOfUniformStartReference
import MatedCRT.FirstPass.Derived.ReferenceBoundsForallGamma
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd
import MatedCRT.FirstPass.Derived.CoreExitTimeFromBG20
import MatedCRT.Steps.Sec2.ExpectedExitTimeExplicitBound

/-!
# The scaling theorems of Berestycki-Gwynne Section 6.4 with the paper-owned lemmas of Section 2 supplied

`ScalingOfUniformStartReference` carries the Green kernel lower bound (Lemma 2.13), the bounded exit time
(Lemma 2.17), the explicit expected exit time bound (Lemma 2.19) and the cell size estimate (Lemma 2.8) as binders.
All four are theorems for the data already present:

* Lemma 2.8 (`cellSizeEstimateStmt_holds`) is unconditional;
* Lemma 2.17 is `firstPass_2_17` applied to the volume growth `volumeGrowthStmt_holds` (Berestycki-Gwynne Lemma A.1);
* Lemma 2.19 is `expectedExitTimeExplicitBound_of_steps` from Lemmas 2.17 and 2.18;
* Lemma 2.13 (Berestycki-Gwynne Lemma 4.4) is `greenKernelLowerBoundStmt_of_reference_of_forall_gamma` from the
  normalized SLE law, a reference environment and the mating-rigid sets.

The forms below keep the conclusions of `hEqLaw_of_scaling` and `isTightMeasureSet_data_interpWalkLaw_of_scaling`
and carry only the Hölder continuity (Lemma 2.15), the exit time upper bound (Lemma 2.14), the cone scaling of valid
environments, the uniform-start principle, and the normalized SLE law with its reference environment.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology
open MarkovProcess (ContinuousPath)

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Equicontinuity in law of the quenched walks from the uniform-start invariance principle and a reference
environment.** The Green kernel lower bound, the bounded exit time, the explicit expected exit time bound and the
cell size estimate (Lemmas 2.13, 2.17, 2.19, 2.8) are supplied. -/
theorem hEqLaw_of_uniformStart_closed {𝒮 : SpaceFillingSLEModel}
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h214 : ExitTimeUpperBoundStmt 𝒮)
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0)) :
    ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R δ ω} ≤ ENNReal.ofReal a :=
  hEqLaw_of_uniformStart_of_reference h32
    (greenKernelLowerBoundStmt_of_reference_of_forall_gamma hν hνref href hU) h214
    (firstPass_2_17 volumeGrowthStmt_holds)
    (expectedExitTimeExplicitBound_of_steps (firstPass_2_17 volumeGrowthStmt_holds) h214)
    hEnvS hN4 hγ hγ2 hν hνref href hU (cellSizeEstimateStmt_holds 𝒮) hS hae hε0 hε

/-- **Tightness of the pairs (datum, interpolated quenched walk law) from the uniform-start invariance principle and
a reference environment.** The Green kernel lower bound, the bounded exit time, the explicit expected exit time bound
and the cell size estimate (Lemmas 2.13, 2.17, 2.19, 2.8) are supplied. -/
theorem isTightMeasureSet_data_interpWalkLaw_of_uniformStart_closed {𝒮 : SpaceFillingSLEModel}
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h214 : ExitTimeUpperBoundStmt 𝒮)
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0))
    {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [PolishSpace Data]
    [BorelSpace Data] (D : Ω → Data) (hD : AEMeasurable D S.P) :
    IsTightMeasureSet {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) |
      ∃ n, ν = S.P.map fun ω => (D ω, interpWalkLaw S η' (eps n) ω)} :=
  isTightMeasureSet_data_interpWalkLaw_of_uniformStart_of_reference h32
    (greenKernelLowerBoundStmt_of_reference_of_forall_gamma hν hνref href hU) h214
    (firstPass_2_17 volumeGrowthStmt_holds)
    (expectedExitTimeExplicitBound_of_steps (firstPass_2_17 volumeGrowthStmt_holds) h214)
    hEnvS hN4 hγ hγ2 hν hνref href hU (cellSizeEstimateStmt_holds 𝒮) hS hη' hae hε0 hε D hD

end MatedCRT.FirstPass.Derived
