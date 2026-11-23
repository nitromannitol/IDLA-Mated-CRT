import MatedCRT.FirstPass.Derived.ReferenceTripleLaw
import MatedCRT.FirstPass.Derived.ReferenceEnvMeasurableVersion
import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfBG20
import MatedCRT.FirstPass.S6j.LitUniformStartInvariance

/-!
# The uniform-start invariance principle from one reference environment

The event of `GMS21UniformStartInput` at mesh `ε` depends on the environment only through the embedded vertices
`η(εk)` and the edge multiplicities `S.mult ε`. Written on the data space `C(ℝ, ℂ) × (ℤ → ℤ → ℕ)` of (continuous
curve, edge multiplicities), it is the preimage of one deterministic set `uniformStartGoodData ε ρ R κ` under the
data map `ω ↦ (η' ω, S.mult ε ω)` of a measurable continuous version `η'` of the curve.

The law of the data is the same in all valid environments of models with the same normalized space-filling SLE law
and the same `γ` (`map_curveVersion_mult_eq_of_valid`, from the law of the triple (field, curve, edge
multiplicities), `map_distribution_curveVersion_mult_eq_of_valid`, and the mating-rigid full set
`exists_matingRigidLEOn_full_derived`). The probability of the complement of the good event is at most the mass that
the law of the data gives to the complement of `uniformStartGoodData` (`Measure.le_map_apply`; no measurability of
the event is used). Hence a bound on that mass in ONE valid environment (Gwynne–Miller–Sheffield, arXiv:1705.11161,
Theorem 3.4, is a statement about the law of the mated-CRT map embedded by whole-plane space-filling SLE in an
independent `γ`-quantum cone) gives `GMS21UniformStartInput` for every model with the same law.

## Main results

* `uniformStartGoodData`: the good set at mesh `ε` on the data space.
* `map_curveVersion_mult_eq_of_valid`: the law of (curve, edge multiplicities) is the same in valid environments of
  models with the same normalized law.
* `measure_compl_uniformStartGood_le_map`: the probability of the failure event is at most the mass of the
  complement of the good set under the law of the data.
* `gms21UniformStartInput_of_reference`: `GMS21UniformStartInput 𝒮` from the normalized law of `𝒮` and the bound
  on one reference environment for each `γ`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- The good set of the uniform-start comparison at mesh `ε` on the data space of (continuous curve, edge
multiplicities): for every vertex `x` embedded in `closedBall 0 ρ` and every set `A` of paths, the walk of the
multiplicities `d.2` from `x`, embedded by `d.1(ε ·)`, interpolated and stopped at its exit time from `B_R(0)`, lies in
`A` with probability at most `κ` plus the probability that planar Brownian motion from the embedded vertex, stopped
at its exit time from `B_R(0)`, is within `cmpEDist`-distance `κ` of `A`. -/
def uniformStartGoodData (ε ρ R κ : ℝ) : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
  {d | ∀ x : ℤ, vertexPoint ε d.1 x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
    srwLaw d.2 x {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε d.1 1 w) ∈ A} ≤
      planarBrownianMotion (vertexPoint ε d.1 x)
        {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
        ENNReal.ofReal κ}

/-- **The law of (curve, edge multiplicities) is the same in valid environments with the same normalized law.**
For valid environments `S, S'` of models with the same normalized space-filling SLE law `ν` and the same
`0 < γ < 2`, measurable continuous versions `η', ζ'` of their curves and every `ε`, the pairs `(η', S.mult ε)` and
`(ζ', S'.mult ε)` have the same law. -/
theorem map_curveVersion_mult_eq_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ζ' : Ω' → C(ℝ, ℂ)} (hζ'm : Measurable ζ') (hζ' : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω) (ε : ℝ) :
    S.P.map (fun ω => (η' ω, S.mult ε ω)) = S'.P.map (fun ω => (ζ' ω, S'.mult ε ω)) := by
  obtain ⟨G, hGnull, hG⟩ := exists_matingRigidLEOn_full_derived
  obtain ⟨H, hHm, hrep⟩ := hS.exists_measurable_fieldVersion hγ0 hγ2
  obtain ⟨H', hH'm, hrep'⟩ := hS'.exists_measurable_fieldVersion hγ0 hγ2
  have htrip := FirstPass.Derived.map_distribution_curveVersion_mult_eq_of_valid hν hν' hγ0 hγ2 hS hS'
    (fun γ hγ0 hγ2 => ⟨G, hGnull γ hγ0 hγ2, hG⟩) hHm hH'm hrep hrep' hη'm hη' hζ'm hζ' ε
  have hsnd : Measurable (Prod.snd : LQGMetric.DistC × C(ℝ, ℂ) × (ℤ → ℤ → ℕ) → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
    measurable_snd
  have h1 : Measurable fun ω => (H ω, η' ω, S.mult ε ω) :=
    hHm.prodMk (hη'm.prodMk (hS.measurable_mult_array ε))
  have h2 : Measurable fun ω => (H' ω, ζ' ω, S'.mult ε ω) :=
    hH'm.prodMk (hζ'm.prodMk (hS'.measurable_mult_array ε))
  have := congrArg (Measure.map Prod.snd) htrip
  rwa [Measure.map_map hsnd h1, Measure.map_map hsnd h2] at this

/-- **The failure probability is at most the mass of the bad data.** For a valid environment `S` and a measurable
continuous version `η'` of its curve, the probability of the complement of the good event of
`GMS21UniformStartInput` at mesh `ε` is at most the mass that the law of `(η', S.mult ε)` gives to the complement of
`uniformStartGoodData ε ρ R κ`. -/
theorem measure_compl_uniformStartGood_le_map {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) (ε ρ R κ : ℝ) :
    S.P {ω | ∀ x : ℤ, vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
        srwLaw (S.mult ε ω) x {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A} ≤
          planarBrownianMotion (vertexPoint ε (S.η ω) x)
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
            ENNReal.ofReal κ}ᶜ ≤
      S.P.map (fun ω => (η' ω, S.mult ε ω)) (uniformStartGoodData ε ρ R κ)ᶜ := by
  have hD : Measurable fun ω => (η' ω, S.mult ε ω) := hη'm.prodMk (hS.measurable_mult_array ε)
  refine le_trans (measure_mono_ae ?_) (Measure.le_map_apply hD.aemeasurable _)
  filter_upwards [hη'] with ω hω
  intro h
  simpa [uniformStartGoodData, hω] using h

/-- **The uniform-start invariance principle from one reference environment.** Let `𝒮` have normalized
space-filling SLE law `ν`. Suppose that for each `0 < γ < 2` some model `𝒮₀` with the same law `ν` has a valid
environment `S₀` (on any carrier) with a measurable continuous version `η₀` of its curve, such that for all
`0 < ρ < R` and `κ, θ > 0`, for all small positive `ε` the law of `(η₀, S₀.mult ε)` gives mass at most `θ` to the
complement of `uniformStartGoodData ε ρ R κ` (Gwynne–Miller–Sheffield, arXiv:1705.11161, Theorem 3.4, on the
reference environment). Then `GMS21UniformStartInput 𝒮`. -/
theorem gms21UniformStartInput_of_reference {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν)
    (hRef : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult ε ω)) (uniformStartGoodData ε ρ R κ)ᶜ ≤ ENNReal.ofReal θ) :
    GMS21UniformStartInput 𝒮 := by
  intro γ hγ0 hγ2 Ω _ S hS R ρ hρ hρR κ hκ θ hθ
  obtain ⟨𝒮₀, hν₀, Ω₀, _, S₀, hS₀, η₀, hη₀m, hη₀, hbd⟩ := hRef γ hγ0 hγ2
  obtain ⟨ε₀, hε₀, hε⟩ := hbd R ρ hρ hρR κ hκ θ hθ
  obtain ⟨η', hη'm, hη'⟩ := hS.exists_curveVersion
  refine ⟨ε₀, hε₀, fun ε hε0 hεε₀ => ?_⟩
  refine (measure_compl_uniformStartGood_le_map hS hη'm hη' ε ρ R κ).trans ?_
  rw [map_curveVersion_mult_eq_of_valid h1 hν₀ hγ0 hγ2 hS hS₀ hη'm hη' hη₀m hη₀ ε]
  exact hε ε hε0 hεε₀

end MatedCRT
