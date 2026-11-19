import MatedCRT.FirstPass.Derived.LQGDataEncode
import MatedCRT.FirstPass.Derived.LQGDataWeakContinuity
import MatedCRT.FirstPass.Derived.RandomWalkToLBMPremiseN8
import MatedCRT.FirstPass.Derived.RandomWalkToLBMIdentificationAssembly
import MatedCRT.FirstPass.Derived.CircleProcessLawValid

/-!
# Theorem 2.11 with the LQG measure coordinatized by `LQGData`

`hid_of_markovLimit` and `randomWalkToLBMStmt_of_markovLimit` take a Polish space `M` with a family `μX` of locally
finite measures on the plane, the Lévy–Prokhorov continuity `hπ` of the cutoff measures `ψ μX d`, and a measurable
coordinate `E` of the LQG measure `μ_h` with `μX (E ω) = μ_h` almost surely in every valid environment (`hK3`). Here
these are supplied by the Polish space `LQGData` of annulus masses and normalized annulus localizations, with
`μX := LQGData.toMeasure`:

* `hπ` is `LQGData.continuous_levyProkhorov_cutoffWeightedMeasure`;
* `hK3` is `hK3_lqgData`: `E := LQGData.encode ∘ μ̃_h` for a measurable version `μ̃_h` of the random measure `μ_h`
  (`aemeasurable_mu_of_valid`); `LQGData.encode` is measurable and `(LQGData.encode μ).toMeasure = μ` for the
  almost surely locally finite `μ = μ_h`.

The Markov premise `hN8` of the inputs is replaced by its first two items `hN8'` (the Liouville Brownian law field is a
Markovian time change of Brownian motion with `μ_h` invariant), the other two items holding for every valid
environment (`hN8_of_isMarkovTCBM_isInvariantFor`).

## Main statements

* `hK3_lqgData`: the coordinate premise `hK3` at `M := LQGData`, `μX := LQGData.toMeasure`.
* `hid_of_markovLimit_lqgData`: the identification hypothesis of Theorem 2.11 from `hN8'`, `hN5`, `hN9`, `hexit`.
* `randomWalkToLBMStmt_of_markovLimit_lqgData`: Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2) from the same
  premises.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open MatedCRT.TruncatedLaws (RegularExit)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

namespace MatedCRT.FirstPass.Derived

/-- **A measurable `LQGData` coordinate of the LQG measure.** In every valid environment at `0 < γ < 2` there is a
measurable `E : Ω → LQGData` with `(E ω).toMeasure = μ_h` almost surely: `E` is the encoding `LQGData.encode` of a
measurable version of the random measure `μ_h`, which is almost surely locally finite. -/
theorem hK3_lqgData (𝒮 : SpaceFillingSLEModel) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ E : Ω → LQGData, Measurable E ∧ ∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω := by
  intro γ hγ hγ2 Ω _ S hS
  have hμ : AEMeasurable S.μ S.P := aemeasurable_mu_of_valid hγ hγ2 hS
  have hloc : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) :=
    hS.isLQGMeasure.mono fun ω h => h.isLocallyFiniteMeasure
  refine ⟨fun ω => LQGData.encode (hμ.mk S.μ ω), LQGData.measurable_encode.comp hμ.measurable_mk, ?_⟩
  filter_upwards [hμ.ae_eq_mk, hloc] with ω hω hlocω
  exact (congrArg (fun μ => LQGData.toMeasure (LQGData.encode μ)) hω).symm.trans
    (@LQGData.toMeasure_encode (S.μ ω) hlocω)

/-- **The identification hypothesis of Theorem 2.11 at `M := LQGData`** (Berestycki–Gwynne (2020), §7.1–7.4).
The binders `M`, `μX`, `hπ`, `hK3` of `hid_of_markovLimit` are supplied by `LQGData`, `LQGData.toMeasure`,
`LQGData.continuous_levyProkhorov_cutoffWeightedMeasure` and `hK3_lqgData`. The remaining premises are

* `hN8'`: for almost every value `d` of the data `(pairJ ⊤ H, E)`, the Liouville Brownian law field
  `lbmPathLawField γ d.1` is a Markovian time change of Brownian motion leaving `d.2.toMeasure` invariant (the
  literature input that Liouville Brownian motion is a time change of Brownian motion by its positive continuous
  additive functional with Revuz measure `μ_h`, Garban–Rhodes–Vargas); the nondegeneracy items of `hN8` follow
  (`hN8_of_isMarkovTCBM_isInvariantFor`);
* `hN5`: every subsequential weak limit of the interpolated walk laws is almost surely a Markovian time change of
  Brownian motion (Lemma 7.4);
* `hN9`: if almost surely the limiting family is a linear time change of the Liouville Brownian law field, the
  constant is deterministic (Lemma 7.18);
* `hexit`: Brownian motion makes an outward excursion right after its exit time (Mörters–Peres);
* `hEnvS`, `hN4`, `hν`, `href`, `hU`: the consumer binders of `randomWalkToLBMStmt_of_identification`, as in
  `hid_of_markovLimit`. -/
theorem hid_of_markovLimit_lqgData {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hexit : BrownianOutwardExcursionAtExitStep)
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∃ (Data : Type) (_ : TopologicalSpace Data) (_ : MeasurableSpace Data) (_ : PolishSpace Data)
        (_ : BorelSpace Data) (D : Ω → Data) (Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))),
        Measurable D ∧ Measurable Λ ∧
        (∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
          ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
            ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) z : Measure (ContinuousPath ℂ))) ∧
        ∀ (e : ℕ → ℝ) (φ : ℕ → ℕ), (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) → StrictMono φ →
          ∀ ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))), IsProbabilityMeasure ν →
          (∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
            Tendsto (fun k => ∫ ω, f (D ω, interpWalkLaw S η' (e (φ k)) ω) ∂S.P) atTop
              (𝓝 (∫ p, f p ∂ν))) →
          ν = S.P.map fun ω => (D ω, Λ (D ω)) :=
  hid_of_markovLimit hEnvS hN4 hν href hU hexit LQGData.toMeasure
    LQGData.continuous_levyProkhorov_cutoffWeightedMeasure (hK3_lqgData 𝒮)
    (hN8_of_isMarkovTCBM_isInvariantFor LQGData.toMeasure
      LQGData.continuous_levyProkhorov_cutoffWeightedMeasure hN8') hN5 hN9

/-- **Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2) from the Markovian time-change structure of the limits,
with the LQG measure coordinatized by `LQGData`.** The premises are those of `hid_of_markovLimit_lqgData`: `hN8'`
(Liouville Brownian motion is a Markovian time change of Brownian motion leaving `μ_h` invariant,
Garban–Rhodes–Vargas), `hN5`, `hN9`, `hexit`, and `hEnvS`, `hN4`, `hν`, `href`, `hU` as in
`randomWalkToLBMStmt_of_markovLimit`. -/
theorem randomWalkToLBMStmt_of_markovLimit_lqgData {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hexit : BrownianOutwardExcursionAtExitStep)
    (hN8' : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → (∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) →
      ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
        IsMarkovTCBM (lbmPathLawField γ d.1) ∧ IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2))
    (hN5 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, IsMarkovTCBM P)
    (hN9 : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z) :
    RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_markovLimit hEnvS hN4 hν href hU hexit LQGData.toMeasure
    LQGData.continuous_levyProkhorov_cutoffWeightedMeasure (hK3_lqgData 𝒮)
    (hN8_of_isMarkovTCBM_isInvariantFor LQGData.toMeasure
      LQGData.continuous_levyProkhorov_cutoffWeightedMeasure hN8') hN5 hN9

end MatedCRT.FirstPass.Derived
