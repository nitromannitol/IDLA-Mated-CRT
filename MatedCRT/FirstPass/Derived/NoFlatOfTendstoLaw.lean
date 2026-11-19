import MatedCRT.FirstPass.Derived.NoStickingLimitDerived
import MatedCRT.FirstPass.Derived.ScalingOfUniformStartClosed
import MatedCRT.FirstPass.Derived.RandomWalkToLBMIdentificationAssembly

/-!
# No flat intervals for a subsequential limit of the interpolated walk laws, from the uniform-start principle

Berestycki–Gwynne (2020), Proposition 6.1, last claim, in the form needed for Lemma 7.4: if the interpolated
quenched walk laws `P̃^{ε_n}` converge in law to `ν₂` then `ν₂`-almost every `P` satisfies, for every `z`, that
`P_z` gives mass zero to the paths that are constant on an interval of positive length.  This is
`NoStickingLimitDerived.ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_of_inputs` with the data space
a point and with the inputs of the window estimate (Lemmas 2.13, 2.14, 2.17, 2.19, 6.10) supplied from the
uniform-start invariance principle and the reference environments of the model, exactly as in the
equicontinuity-in-law producer `hEqLaw_of_uniformStart_holder`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]

/-- **No flat intervals for a subsequential limit of the interpolated walk laws** (BG20, Proposition 6.1, last
claim), from the uniform-start invariance principle. -/
theorem ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_interpWalkLaw {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {ν₂ : Measure PathLawFamily}
    (hlaw : ∀ f : PathLawFamily →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) :
    ∀ᵐ P ∂ν₂, ∀ z : ℂ,
      ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        {f : C(ℝ≥0, ℂ) | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} = 0 := by
  have h213 := greenKernelLowerBoundStmt_of_reference_of_forall_gamma hν hν href hU
  have h214 := exitTimeUpperBoundStmt_of_greenKernelUpper
    (greenKernelUpperBoundStmt_of_reference_of_forall_gamma hν href hU)
  have h219 := expectedExitTimeExplicitBound_of_steps (firstPass_2_17 volumeGrowthStmt_holds) h214
  have h610 := ExitTimeUpperTailV.exitTimeUpperTailV_of_uniformStart hN4 γ hγ hγ2
  have hmeas : Measurable fun P : PathLawFamily => ((PUnit.unit : PUnit), P) := measurable_prodMk_left
  have key := NoStickingLimitDerived.ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_of_inputs
    hEnvS h213 h214 h219 hN4 hγ hγ2 h610 hS hη' hae hε0 hε (X := PUnit)
    (D := fun _ _ => PUnit.unit) (fun _ => aemeasurable_const)
    (ν := ν₂.map fun P : PathLawFamily => ((PUnit.unit : PUnit), P)) (fun F => by
      rw [integral_map hmeas.aemeasurable F.continuous.aestronglyMeasurable]
      exact hlaw (F.compContinuous ⟨fun P => ((PUnit.unit : PUnit), P), by fun_prop⟩))
  exact ae_of_ae_map hmeas.aemeasurable key

end MatedCRT.FirstPass.Derived
