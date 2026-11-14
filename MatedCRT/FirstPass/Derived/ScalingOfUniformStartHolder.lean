import MatedCRT.FirstPass.Derived.ScalingOfUniformStartSelfReference
import MatedCRT.FirstPass.Derived.DiscreteHolderOfReference
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd

/-!
# The scaling theorems of Berestycki-Gwynne Section 6.4 with the Hölder continuity supplied

`ScalingOfUniformStartSelfReference` keeps the discrete Hölder continuity of harmonic functions
(Lemma 2.15, Gwynne-Miller-Sheffield Theorem 3.9 in its corrected form,
`FrozenDiscreteHolderContinuityCorrected`) as a binder. On the reference environments of the model itself it is a
theorem, `frozenDiscreteHolderContinuityCorrected_of_reference`, from the normalized space-filling SLE law, the
reference environments, the mating-rigid sets and the cell size estimate (Lemma 2.8, a theorem:
`cellSizeEstimateStmt_holds`). The forms below have the conclusions of `hEqLaw_of_uniformStart_selfReference` and
`isTightMeasureSet_data_interpWalkLaw_of_uniformStart_selfReference` and carry only the cone scaling of valid
environments, the uniform-start principle, and the normalized SLE law of `𝒮` with its reference environments and the
mating-rigid sets.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology
open MarkovProcess (ContinuousPath)

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Equicontinuity in law of the quenched walks from the uniform-start invariance principle and the reference
environments of the model itself.** The exit time upper bound (Lemma 2.14) and the Hölder continuity (Lemma 2.15)
are supplied. -/
theorem hEqLaw_of_uniformStart_holder {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0)) :
    ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R δ ω} ≤ ENNReal.ofReal a :=
  hEqLaw_of_uniformStart_selfReference
    (frozenDiscreteHolderContinuityCorrected_of_reference hν href hU (cellSizeEstimateStmt_holds 𝒮))
    hEnvS hN4 hγ hγ2 hν href hU hS hae hε0 hε

/-- **Tightness of the pairs (datum, interpolated quenched walk law) from the uniform-start invariance principle and
the reference environments of the model itself.** The exit time upper bound (Lemma 2.14) and the Hölder continuity
(Lemma 2.15) are supplied. -/
theorem isTightMeasureSet_data_interpWalkLaw_of_uniformStart_holder {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
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
  isTightMeasureSet_data_interpWalkLaw_of_uniformStart_selfReference
    (frozenDiscreteHolderContinuityCorrected_of_reference hν href hU (cellSizeEstimateStmt_holds 𝒮))
    hEnvS hN4 hγ hγ2 hν href hU hS hη' hae hε0 hε D hD

end MatedCRT.FirstPass.Derived
