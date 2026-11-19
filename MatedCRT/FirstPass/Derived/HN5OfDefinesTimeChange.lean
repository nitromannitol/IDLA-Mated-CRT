import MatedCRT.FirstPass.Derived.MarkovHalfOfHN5
import MatedCRT.FirstPass.Derived.MarkovLimitFamily
import MatedCRT.FirstPass.Derived.RandomWalkToLBMIdentificationAssembly
import MatedCRT.FirstPass.Derived.MepsTendstoAtTop
import MatedCRT.FirstPass.Derived.ScalingOfUniformStartHolder
import MatedCRT.FirstPass.Derived.ConvergenceOfIDLAOfMarkovLimit

/-!
# Berestycki–Gwynne (2020), Lemma 7.4, from its time-change half

Berestycki–Gwynne (2020), Lemma 7.4 says that every subsequential limit `ν₂` of the interpolated quenched walk
laws `P̃^{ε_n}` is concentrated on Markovian time changes of Brownian motion (`IsMarkovTCBM`).  By
`ae_markovAt_of_tendsto_law_interpWalkLaw` the Markov half is a theorem once the equicontinuity in law of the
walk laws and `m_{ε_n} → ∞` are available, and both follow from the uniform-start invariance principle
([GMS21, Theorem 3.4]).  What remains of Lemma 7.4 is the other half, that `ν₂`-almost every `P` defines a time
change of Brownian motion (`DefinesTimeChangedBM`), which is a consequence of the same principle together with
[GMS21, Propositions 6.1 and 6.14] and the Skorokhod representation theorem.

* `ae_isMarkovTCBM_of_tendsto_law_interpWalkLaw`: the Markov half plus `DefinesTimeChangedBM` almost surely give
  `IsMarkovTCBM` almost surely, with `hEqLaw` and `m_{ε_n} → ∞` explicit;
* `hN5_of_defines`: the binder `hN5` of `randomWalkToLBMStmt_of_markovLimit_derived`, from the binder `hN5a` that
  has the same premises and the conclusion `DefinesTimeChangedBM` only;
* `randomWalkToLBMStmt_of_markovLimit_derived_hN5a`: `randomWalkToLBMStmt_of_markovLimit_derived` with `hN5`
  replaced by `hN5a`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Lemma 7.4 from its time-change half.**  A subsequential limit `ν₂` of the interpolated walk laws that is
almost surely a time change of Brownian motion is almost surely a Markovian time change of Brownian motion,
given the equicontinuity in law `hEqLaw` and `m_{ε_n} → ∞` (conclusions of the uniform-start principle). -/
theorem ae_isMarkovTCBM_of_tendsto_law_interpWalkLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hmpos : ∀ n, 0 < S.mε (ε n)) (hmε : Tendsto (fun n => S.mε (ε n)) atTop atTop)
    {ν₂ : Measure PathLawFamily} [IsProbabilityMeasure ν₂]
    (hlaw : ∀ f : PathLawFamily →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂)))
    (hdef : ∀ᵐ P ∂ν₂, DefinesTimeChangedBM P) : ∀ᵐ P ∂ν₂, IsMarkovTCBM P :=
  ae_isMarkovTCBM_of_defines (K := fun P => P) hdef fun z s =>
    ae_markovAt_of_tendsto_law_interpWalkLaw hS hη' hae hε0 hε hEqLaw hmpos hmε hlaw z s

/-- **The binder `hN5` from its time-change half `hN5a`** (Berestycki–Gwynne (2020), Lemma 7.4): from the
uniform-start invariance principle the Markov half of Lemma 7.4 is a theorem, so the premise
`∀ᵐ P ∂ν₂, IsMarkovTCBM P` needs only `∀ᵐ P ∂ν₂, DefinesTimeChangedBM P` as an input. -/
theorem hN5_of_defines {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hN5a : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, DefinesTimeChangedBM P) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae ε hε0 hε ν₂ hν₂ hlaw
  have h213 := greenKernelLowerBoundStmt_of_reference_of_forall_gamma hν hν href hU
  have h214 := exitTimeUpperBoundStmt_of_greenKernelUpper
    (greenKernelUpperBoundStmt_of_reference_of_forall_gamma hν href hU)
  have hmε := tendsto_mε_atTop_of_uniformStart h213 h214 hN4 hγ hγ2 hS hε0 hε
  -- shift the sequence so that `0 < m_{ε_n}` for every `n`
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hmε.eventually_gt_atTop 0)
  have hε0' : ∀ n, 0 < ε (n + N) := fun n => hε0 _
  have hε' : Tendsto (fun n => ε (n + N)) atTop (𝓝 0) := hε.comp (tendsto_add_atTop_nat N)
  have hEqLaw := hEqLaw_of_uniformStart_holder hEnvS hN4 hγ hγ2 hν href hU hS hae hε0' hε'
  exact ae_isMarkovTCBM_of_tendsto_law_interpWalkLaw hS hη' hae hε0' hε' hEqLaw
    (fun n => hN (n + N) (Nat.le_add_left N n))
    (hmε.comp (tendsto_add_atTop_nat N))
    (fun f => (tendsto_add_atTop_iff_nat N).2 (hlaw f))
    (hN5a γ hγ hγ2 Ω S hS η' hη' hae ε hε0 hε ν₂ hν₂ hlaw)

end MatedCRT.FirstPass.Derived
