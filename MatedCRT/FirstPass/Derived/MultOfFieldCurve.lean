import MatedCRT.FirstPass.Derived.BoundaryPairDecoderTransfer
import MatedCRT.FirstPass.Derived.MatingRigidityOneSided

/-!
# The edge multiplicity as a function of the field and the space-filling curve

Let `G` be a set of pairs of paths whose complement is null for every law of a `γ`-correlated two-sided Brownian
motion, and on which the mating relation determines the pair up to the swap `L ↔ R` from one inclusion of mating
relations (`MatingRigidLEOn G`). Then the edge multiplicities of the mated-CRT map are, almost surely, one and the same
function of the field and the space-filling curve, for every valid environment with a given normalized
space-filling SLE law:

* `ae_mult_eq_boundaryLength_of_reference`: with the boundary-length decoder `BL₀` of a reference valid environment,
  `S.mult ε = bmEdgeCount ε (BL₀ (H, η'))` almost surely on every other valid environment `S`;
* `exists_decoder_mult_eq`: one measurable decoder `BL` serves every valid environment with the given law.

The rigidity of the mating relation (mating-of-trees uniqueness at the level of the identifications) is an explicit
hypothesis here.
-/

open MeasureTheory ProbabilityTheory Set

namespace MatedCRT.FirstPass.Derived

/-- **Edge multiplicities from field and curve, through a reference environment.** Let `S₀` be a valid environment
with the same normalized space-filling SLE law and the same `0 < γ < 2` as `S`, and `BL₀` a measurable decoder of its
boundary-length pair from (field, curve). On a one-sided mating-rigid set `G` that is full for every `γ`-correlated
two-sided Brownian law, the edge multiplicity of `S` is almost surely the mated-CRT edge count of `BL₀ (H, η')`. -/
theorem ae_mult_eq_boundaryLength_of_reference {𝒮 𝒮₀ : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hν₀ : HasNormalizedSLELaw 𝒮₀ ν)
    {Ω Ω₀ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {S : MatedCRTEnv Ω} {S₀ : MatedCRTEnv Ω₀}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS₀ : S₀.IsValid 𝒮₀ γ)
    {H : Ω → LQGMetric.DistC} {H₀ : Ω₀ → LQGMetric.DistC} (hH : Measurable H) (hH₀ : Measurable H₀)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep₀ : ∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {η₀' : Ω₀ → C(ℝ, ℂ)} (hη₀'m : Measurable η₀') (hη₀' : ∀ᵐ ω ∂S₀.P, ⇑(η₀' ω) = S₀.η ω)
    {BL₀ : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) → MatedCRTHarmonic.MatedCRT.Path2}
    (hBL₀m : Measurable BL₀) (hBL₀ : ∀ᵐ ω ∂S₀.P, S₀.bm ω = BL₀ (H₀ ω, η₀' ω))
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) (ε : ℝ) :
    ∀ᵐ ω ∂S.P, S.mult ε ω =
      bmEdgeCount ε (fun t => (BL₀ (H ω, η' ω) t).1) (fun t => (BL₀ (H ω, η' ω) t).2) :=
  hS.ae_mult_eq_of_matingRigidLEOn hGnull hG hη' (Y := fun ω => BL₀ (H ω, η' ω))
    (ae_boundaryLength_mem_of_valid hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀ hrep hrep₀ hη'm hη' hη₀'m hη₀' hBL₀m hBL₀
      hGnull)
    (ae_merge_boundaryLength_of_valid hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀ hrep hrep₀ hη'm hη' hη₀'m hη₀' hBL₀m hBL₀) ε

/-- **One decoder for all valid environments.** Fix a normalized space-filling SLE law `ν`, `0 < γ < 2`, and a
one-sided mating-rigid set `G` that is full for every `γ`-correlated two-sided Brownian law. There is a measurable
`BL : Field × C(ℝ, ℂ) → Path2` such that, for every valid environment `S` whose model has law `ν`, every measurable
version `H` of its field and every measurable continuous version `η'` of its curve, almost surely
`S.mult ε = bmEdgeCount ε (BL (H, η'))` for every `ε`. (If no valid environment with measurable versions exists, the
statement is vacuous.) -/
theorem exists_decoder_mult_eq {ν : ℝ → Measure SLEPathCode} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) :
    ∃ BL : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) → MatedCRTHarmonic.MatedCRT.Path2, Measurable BL ∧
      ∀ (𝒮 : SpaceFillingSLEModel), HasNormalizedSLELaw 𝒮 ν →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℝ, ∀ᵐ ω ∂S.P, S.mult ε ω =
        bmEdgeCount ε (fun t => (BL (H ω, η' ω) t).1) (fun t => (BL (H ω, η' ω) t).2) := by
  by_cases hex : ∃ (𝒮₀ : SpaceFillingSLEModel) (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀)
      (H₀ : Ω₀ → LQGMetric.DistC) (η₀' : Ω₀ → C(ℝ, ℂ)), HasNormalizedSLELaw 𝒮₀ ν ∧ S₀.IsValid 𝒮₀ γ ∧
      Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧ Measurable η₀' ∧
      (∀ᵐ ω ∂S₀.P, ⇑(η₀' ω) = S₀.η ω)
  · obtain ⟨𝒮₀, Ω₀, _, S₀, H₀, η₀', hν₀, hS₀, hH₀, hrep₀, hη₀'m, hη₀'⟩ := hex
    obtain ⟨BL₀, hBL₀m, hBL₀⟩ := exists_bm_eq_boundaryLength hS₀ hrep₀ hη₀'
    refine ⟨BL₀, hBL₀m, fun 𝒮 hν Ω _ S hS H hH hrep η' hη'm hη' ε => ?_⟩
    exact ae_mult_eq_boundaryLength_of_reference hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀ hrep hrep₀ hη'm hη' hη₀'m hη₀'
      hBL₀m hBL₀ hGnull hG ε
  · refine ⟨fun _ => 0, measurable_const, fun 𝒮 hν Ω _ S hS H hH hrep η' hη'm hη' ε => ?_⟩
    exact (hex ⟨𝒮, Ω, inferInstance, S, H, η', hν, hS, hH, hrep, hη'm, hη'⟩).elim

end MatedCRT.FirstPass.Derived
