import MatedCRT.FirstPass.Derived.CurveMultEventTransfer
import LatticeProb.Prob.MapApplyStandardBorel
import LatticeProb.Topology.PolishContinuousMap

/-!
# Outer-measure transfer of events of the curve and the edge multiplicities to a standard Borel environment

Fix a normalized space-filling SLE law `ν`, `0 < γ < 2`, and a one-sided mating-rigid set `G` of pairs of paths that
is full for every `γ`-correlated two-sided Brownian law (`MatingRigidLEOn G`). For two valid environments `S, S'` of
models with law `ν`:

* `map_curve_mult_eq_of_valid`: for measurable continuous versions `η', ζ'` of the curves, the pair (curve, edge
  multiplicities) has the same law under `S` and `S'`;
* `measure_curve_mult_preimage_le_of_valid`: if the carrier of `S'` is a standard Borel space, then for EVERY set
  `B ⊆ C(ℝ, ℂ) × (ℤ → ℤ → ℕ)`, measurable or not, `S.P {(η', S.mult ε) ∈ B} ≤ S'.P {(ζ', S'.mult ε) ∈ B}` (outer
  measures);
* `measure_eta_mult_preimage_le_of_valid`: the same for the curves `S.η, S'.η` themselves and every set
  `B ⊆ (ℝ → ℂ) × (ℤ → ℤ → ℕ)`.

The edge multiplicities are one measurable function of (field, curve) (`exists_decoder_mult_eq`), and (field, curve)
has the same law in every valid environment with the given space-filling SLE law
(`identDistrib_distribution_curveVersion_of_valid`). The space `C(ℝ, ℂ) × (ℤ → ℤ → ℕ)` is standard Borel, so the
outer measure of an arbitrary set under the common law is the outer measure of its preimage on the standard Borel
carrier (`LatticeProb.measure_preimage_le_of_map_eq`). The rigidity of the mating relation is an explicit hypothesis.
-/

open MeasureTheory ProbabilityTheory Set

namespace MatedCRT.FirstPass.Derived

/-- **The pair (curve, edge multiplicities) is a measurable function of (field, curve).** For every `ε` there is one
measurable map `F` from (field, continuous curve) to (continuous curve, edge multiplicities) such that, in every
valid environment of a model with normalized space-filling SLE law `ν` and every measurable random distribution `H`
with a.s. the pairings of its field and measurable continuous version `η'` of its curve, almost surely
`(η', S.mult ε) = F (H, η')`. -/
theorem exists_measurable_curve_mult_ae_eq {ν : ℝ → Measure SLEPathCode} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) (ε : ℝ) :
    ∃ F : LQGMetric.DistC × C(ℝ, ℂ) → C(ℝ, ℂ) × (ℤ → ℤ → ℕ), Measurable F ∧
      ∀ (𝒮 : SpaceFillingSLEModel), HasNormalizedSLELaw 𝒮 ν →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      (fun ω => (η' ω, S.mult ε ω)) =ᵐ[S.P] fun ω => F (H ω, η' ω) := by
  obtain ⟨BL, hBLm, hBL⟩ := exists_decoder_mult_eq (ν := ν) hγ0 hγ2 hGnull hG
  refine ⟨fun x => (x.2, bmEdgeCount ε (fun t => (BL x t).1) (fun t => (BL x t).2)), ?_, ?_⟩
  · exact measurable_snd.prodMk (Measurable.of_eval fun j => Measurable.of_eval fun k =>
      (measurable_bmEdgeCount_path ε j k).comp hBLm)
  · intro 𝒮 hν Ω _ S hS H hH hrep η' hη'm hη'
    filter_upwards [hBL 𝒮 hν Ω S hS H hH hrep η' hη'm hη' ε] with ω hω
    change (η' ω, S.mult ε ω) =
      (η' ω, bmEdgeCount ε (fun t => (BL (H ω, η' ω) t).1) (fun t => (BL (H ω, η' ω) t).2))
    rw [hω]

/-- **The pair (curve, edge multiplicities) has the same law in every valid environment.** Let `S, S'` be valid
environments of models with the same normalized space-filling SLE law `ν` and the same `0 < γ < 2`, `H, H'`
measurable random distributions with a.s. the pairings of their fields, and `η', ζ'` measurable continuous versions
of their curves. On a one-sided mating-rigid set `G` that is full for every `γ`-correlated two-sided Brownian law,
for every `ε` the laws of `(η', S.mult ε)` under `S.P` and of `(ζ', S'.mult ε)` under `S'.P` coincide. -/
theorem map_curve_mult_eq_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G)
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC} (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂S'.P, ∀ φ : LQGMetric.TestC, S'.hC ω φ = H' ω φ)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ζ' : Ω' → C(ℝ, ℂ)} (hζ'm : Measurable ζ') (hζ' : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω) (ε : ℝ) :
    S.P.map (fun ω => (η' ω, S.mult ε ω)) = S'.P.map (fun ω => (ζ' ω, S'.mult ε ω)) := by
  obtain ⟨F, hFm, hF⟩ := exists_measurable_curve_mult_ae_eq (ν := ν) hγ0 hγ2 hGnull hG ε
  rw [Measure.map_congr (hF 𝒮 hν Ω S hS H hH hrep η' hη'm hη'),
    Measure.map_congr (hF 𝒮' hν' Ω' S' hS' H' hH' hrep' ζ' hζ'm hζ')]
  exact ((identDistrib_distribution_curveVersion_of_valid hν hν' hγ0 hγ2 hS hS' hH hH' hrep hrep' hη'm hη'
    hζ'm hζ').comp hFm).map_eq

/-- **Outer-measure transfer of events of (curve, edge multiplicities) to a standard Borel valid environment.** Let
`S, S'` be valid environments of models with the same normalized space-filling SLE law `ν` and the same
`0 < γ < 2`, the carrier of `S'` a standard Borel space, `H, H'` measurable random distributions with a.s. the
pairings of their fields, and `η', ζ'` measurable continuous versions of their curves. On a one-sided mating-rigid
set `G` that is full for every `γ`-correlated two-sided Brownian law, for every `ε` and EVERY set `B` of pairs
(curve, edge multiplicity), measurable or not, `S.P {(η', S.mult ε) ∈ B} ≤ S'.P {(ζ', S'.mult ε) ∈ B}` (outer
measures). -/
theorem measure_curve_mult_preimage_le_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G)
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC} (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂S'.P, ∀ φ : LQGMetric.TestC, S'.hC ω φ = H' ω φ)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ζ' : Ω' → C(ℝ, ℂ)} (hζ'm : Measurable ζ') (hζ' : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω)
    (ε : ℝ) (B : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ))) :
    S.P {ω | (η' ω, S.mult ε ω) ∈ B} ≤ S'.P {ω | (ζ' ω, S'.mult ε ω) ∈ B} := by
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have : StandardBorelSpace (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) := inferInstance
  have : IsProbabilityMeasure S'.P := hS'.isProbabilityMeasure
  obtain ⟨F, hFm, hF⟩ := exists_measurable_curve_mult_ae_eq (ν := ν) hγ0 hγ2 hGnull hG ε
  have hA := hF 𝒮 hν Ω S hS H hH hrep η' hη'm hη'
  have hB := hF 𝒮' hν' Ω' S' hS' H' hH' hrep' ζ' hζ'm hζ'
  have hg₁ : Measurable fun ω => F (H ω, η' ω) := hFm.comp (hH.prodMk hη'm)
  have hg : Measurable fun ω => F (H' ω, ζ' ω) := hFm.comp (hH'.prodMk hζ'm)
  have hlaw : S.P.map (fun ω => F (H ω, η' ω)) = S'.P.map (fun ω => F (H' ω, ζ' ω)) := by
    rw [← Measure.map_congr hA, ← Measure.map_congr hB]
    exact map_curve_mult_eq_of_valid hν hν' hγ0 hγ2 hS hS' hGnull hG hH hH' hrep hrep' hη'm hη' hζ'm hζ' ε
  have h₁ : {ω | (η' ω, S.mult ε ω) ∈ B} =ᵐ[S.P] (fun ω => F (H ω, η' ω)) ⁻¹' B := by
    filter_upwards [hA] with ω hω
    change ((η' ω, S.mult ε ω) ∈ B) = (F (H ω, η' ω) ∈ B)
    rw [show (η' ω, S.mult ε ω) = F (H ω, η' ω) from hω]
  have h₂ : {ω | (ζ' ω, S'.mult ε ω) ∈ B} =ᵐ[S'.P] (fun ω => F (H' ω, ζ' ω)) ⁻¹' B := by
    filter_upwards [hB] with ω hω
    change ((ζ' ω, S'.mult ε ω) ∈ B) = (F (H' ω, ζ' ω) ∈ B)
    rw [show (ζ' ω, S'.mult ε ω) = F (H' ω, ζ' ω) from hω]
  rw [measure_congr h₁, measure_congr h₂]
  exact LatticeProb.measure_preimage_le_of_map_eq hg₁.aemeasurable S'.P hg hlaw B

/-- **Outer-measure transfer of events of (curve, edge multiplicities) to a standard Borel valid environment, for
the curves themselves.** Let `S, S'` be valid environments of models with the same normalized space-filling SLE law
`ν` and the same `0 < γ < 2`, the carrier of `S'` a standard Borel space. On a one-sided mating-rigid set `G` that
is full for every `γ`-correlated two-sided Brownian law, for every `ε` and EVERY set `B` of pairs (curve, edge
multiplicity), measurable or not, `S.P {(S.η, S.mult ε) ∈ B} ≤ S'.P {(S'.η, S'.mult ε) ∈ B}` (outer measures). The
measurable versions of the fields and the curves are supplied by validity. -/
theorem measure_eta_mult_preimage_le_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) (ε : ℝ) (B : Set ((ℝ → ℂ) × (ℤ → ℤ → ℕ))) :
    S.P {ω | (S.η ω, S.mult ε ω) ∈ B} ≤ S'.P {ω | (S'.η ω, S'.mult ε ω) ∈ B} := by
  obtain ⟨H, hHm, hrep⟩ := MatedCRT.Sec1.exists_fieldMeasurable_coneDistribution hS
  obtain ⟨H', hH'm, hrep'⟩ := MatedCRT.Sec1.exists_fieldMeasurable_coneDistribution hS'
  obtain ⟨_, _, _, _, _, _, _, _, _, η', _, hC, hae⟩ := hS.matingOfTrees
  obtain ⟨_, _, _, _, _, _, _, _, _, ζ', _, hC', hae'⟩ := hS'.matingOfTrees
  have hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω := hae.mono fun ω h => h.1
  have hζ' : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω := hae'.mono fun ω h => h.1
  let c : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) → (ℝ → ℂ) × (ℤ → ℤ → ℕ) := fun p => (⇑p.1, p.2)
  have key := measure_curve_mult_preimage_le_of_valid hν hν' hγ0 hγ2 hS hS' hGnull hG
    (hHm.mono (S.fieldSigma_le hS) le_rfl) (hH'm.mono (S'.fieldSigma_le hS') le_rfl) hrep hrep'
    hC.measurable_curves.2.1 hη' hC'.measurable_curves.2.1 hζ' ε (c ⁻¹' B)
  have h₁ : {ω | (S.η ω, S.mult ε ω) ∈ B} =ᵐ[S.P] {ω | (η' ω, S.mult ε ω) ∈ c ⁻¹' B} := by
    filter_upwards [hη'] with ω hω
    change ((S.η ω, S.mult ε ω) ∈ B) = ((⇑(η' ω), S.mult ε ω) ∈ B)
    rw [hω]
  have h₂ : {ω | (ζ' ω, S'.mult ε ω) ∈ c ⁻¹' B} =ᵐ[S'.P] {ω | (S'.η ω, S'.mult ε ω) ∈ B} := by
    filter_upwards [hζ'] with ω hω
    change ((⇑(ζ' ω), S'.mult ε ω) ∈ B) = ((S'.η ω, S'.mult ε ω) ∈ B)
    rw [hω]
  rw [measure_congr h₁, ← measure_congr h₂]
  exact key

end MatedCRT.FirstPass.Derived
