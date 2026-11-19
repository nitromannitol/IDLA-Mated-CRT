import MatedCRT.FirstPass.Derived.DyadicVagueRelValid
import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfConeInputs
import MatedCRT.FirstPass.Derived.MarkovTimeChange
import MatedCRT.FirstPass.Derived.FieldCoordinateCircleAverages

/-!
# From a measurable good set of field coordinates to the law-a.e. Markov and invariance statement

The statement `hN8'` asks that, for every valid environment `S` with measurable versions `H` of the field and `E`
of the LQG data, the field of laws of the rescaled Liouville Brownian motion `lbmPathLawField γ x` is a Markovian
time-changed Brownian motion with invariant measure `toMeasure e`, for almost every `(x, e)` under the law of
`(pairJ ⊤ (H ω), E ω)`. The good set of pairs need not be measurable, so an almost sure statement in `ω` does not
pass to the law directly.

`ae_markovTCBM_invariant_of_goodCoordSet` reduces `hN8'` to a measurable set `A` of field coordinates of full
`quantumConeCoordLaw γ` measure on which a good locally finite measure exists, identified by the dyadic vague
limits along a countable test family `f` whose integrals determine locally finite measures (`hdet`). The measurable
subset `{(x, e) | x ∈ A ∧ IsDyadicVagueLimitAlong γ f x e.toMeasure}` of the good set has full measure: its first
condition by the coordinate law of valid environments, its second almost surely in a valid environment.
-/

open MeasureTheory Filter Topology
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure IsDyadicVagueLimitAlong)

namespace MatedCRT

/-- **The law-a.e. Markov and invariance statement from a measurable good set of field coordinates.**
Let `f` be a countable family of continuous, compactly supported, nonnegative test functions on `ℂ` whose integrals
determine locally finite measures. Let `A` be a measurable set of field coordinates of full `quantumConeCoordLaw γ`
measure such that for every `x ∈ A` some locally finite measure `μ` is the dyadic vague limit along `f` of the
γ-LQG approximations of `x`, with `lbmPathLawField γ x` a Markovian time-changed Brownian motion for which `μ` is
invariant. Then, for every valid environment `S` and measurable versions `H` of the field and `E` of the LQG data,
for almost every `(x, e)` under the law of `(pairJ ⊤ (H ω), E ω)`, `lbmPathLawField γ x` is a Markovian
time-changed Brownian motion for which `toMeasure e` is invariant. -/
theorem ae_markovTCBM_invariant_of_goodCoordSet {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {ι : Type*} [Countable ι] (f : ι → ℂ → ℝ) (hfc : ∀ i, Continuous (f i))
    (hfs : ∀ i, HasCompactSupport (f i)) (hf0 : ∀ i w, 0 ≤ f i w)
    (hdet : ∀ ν ν' : Measure ℂ, IsLocallyFiniteMeasure ν → IsLocallyFiniteMeasure ν' →
      (∀ i, ∫ w, f i w ∂ν = ∫ w, f i w ∂ν') → ν = ν')
    {A : Set (LQGMetric.CoordJ → ℝ)} (hA : MeasurableSet A) (hAq : quantumConeCoordLaw γ Aᶜ = 0)
    (hAgood : ∀ x ∈ A, ∃ μ : Measure ℂ, IsLocallyFiniteMeasure μ ∧ IsDyadicVagueLimitAlong γ f x μ ∧
      IsMarkovTCBM (lbmPathLawField γ x) ∧ IsInvariantFor (lbmPathLawField γ x) μ)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {E : Ω → LQGData} (hEm : Measurable E) (hE : ∀ᵐ ω ∂S.P, LQGData.toMeasure (E ω) = S.μ ω) :
    ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
      IsMarkovTCBM (lbmPathLawField γ d.1) ∧
        IsInvariantFor (lbmPathLawField γ d.1) (LQGData.toMeasure d.2) := by
  -- the measurable part of the good set
  set A₀ : Set ((LQGMetric.CoordJ → ℝ) × LQGData) :=
    {p | p.1 ∈ A ∧ IsDyadicVagueLimitAlong γ f p.1 (LQGData.toMeasure p.2)}
  have hA₀ : MeasurableSet A₀ :=
    (hA.preimage measurable_fst).inter
      (FirstPass.Derived.measurableSet_isDyadicVagueLimitAlong_toMeasure γ (fun i => (hfc i).measurable) hf0)
  -- it lies in the good set: the two dyadic vague limits agree along `f`, hence as measures
  have hsub : ∀ p ∈ A₀, IsMarkovTCBM (lbmPathLawField γ p.1) ∧
      IsInvariantFor (lbmPathLawField γ p.1) (LQGData.toMeasure p.2) := by
    rintro ⟨x, e⟩ ⟨hx, hrel⟩
    obtain ⟨μ, hμ, hrel', hM, hI⟩ := hAgood x hx
    have heq : LQGData.toMeasure e = μ :=
      hdet _ _ inferInstance hμ fun i => tendsto_nhds_unique (hrel i) (hrel' i)
    exact ⟨hM, heq ▸ hI⟩
  -- it has full measure
  have hpair : Measurable fun ω => LQGMetric.pairJ ⊤ (H ω) := measurable_pairJ_top.comp hH
  have hD : Measurable fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω) := hpair.prodMk hEm
  have hxA : ∀ᵐ ω ∂S.P, LQGMetric.pairJ ⊤ (H ω) ∈ A := by
    have hlaw : ∀ᵐ x ∂(S.P.map fun ω => LQGMetric.pairJ ⊤ (H ω)), x ∈ A := by
      rw [hS.map_pairJ_eq_quantumConeCoordLaw hH hrep]
      exact mem_ae_iff.2 hAq
    exact (ae_map_iff hpair.aemeasurable hA).1 hlaw
  have hfull : ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)), d ∈ A₀ := by
    refine (ae_map_iff hD.aemeasurable hA₀).2 ?_
    filter_upwards [hxA, hS.ae_isDyadicVagueLimitAlong_toMeasure hγ0 hγ2 hrep hE f hfc hfs] with ω hω hrel
    exact ⟨hω, hrel.1⟩
  filter_upwards [hfull] with d hd
  exact hsub d hd

end MatedCRT
