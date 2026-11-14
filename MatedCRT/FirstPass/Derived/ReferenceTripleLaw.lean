import MatedCRT.FirstPass.Derived.CurveMultEventTransfer
import MatedCRT.FirstPass.SLERef.Reference

/-!
# The field, the space-filling curve and the edge multiplicities have the same joint law in valid environments

Fix a normalized space-filling SLE law `ν`, `0 < γ < 2`, and a one-sided mating-rigid set `G` of pairs of paths that
is full for every `γ`-correlated two-sided Brownian law (`MatingRigidLEOn G`). For two valid environments `S, S'` of
models with law `ν`, on arbitrary carriers, the triple (field of the `γ`-quantum cone, space-filling SLE curve, edge
multiplicities of the mated-CRT map at scale `ε`) has the same law under `S.P` and under `S'.P`:

* `identDistrib_distribution_curveVersion_mult_of_valid`: for measurable random distributions `H, H'` with a.s. the
  pairings of the fields and measurable continuous versions `η', ζ'` of the curves, the triples
  `(H, η', S.mult ε)` and `(H', ζ', S'.mult ε)` are identically distributed;
* `map_distribution_curveVersion_mult_eq_of_valid`: the same as an equality of push-forward measures, with the
  mating-rigid full set supplied for every `γ` (the hypothesis form of Theorem 2.11);
* `exists_reference_map_distribution_curveVersion_mult_eq`: a model with valid reference environments has, for each
  `0 < γ < 2`, a reference environment `S₀` on `ℝ` with measurable versions `H₀, η₀` of its field and its curve such
  that the triple of every valid environment of the model has the law of the triple of `S₀`.

The proof writes the edge multiplicities as one measurable function of (field, curve), `bmEdgeCount ε (BL (H, η'))`
(`exists_decoder_mult_eq`), so the triple is a.s. a measurable function of the pair (field, curve), whose law is the
same in every valid environment with the given space-filling SLE law
(`identDistrib_distribution_curveVersion_of_valid`).
-/

open MeasureTheory ProbabilityTheory Set

namespace MatedCRT.FirstPass.Derived

/-- **The triple (field, curve, edge multiplicities) has the same law in two valid environments.** Let `S, S'` be
valid environments of models with the same normalized space-filling SLE law `ν` and the same `0 < γ < 2`, `H, H'`
measurable random distributions with a.s. the pairings of their fields, and `η', ζ'` measurable continuous versions of
their curves. On a one-sided mating-rigid set `G` that is full for every `γ`-correlated two-sided Brownian law, for
every `ε` the triples `(H, η', S.mult ε)` and `(H', ζ', S'.mult ε)` are identically distributed in
`𝒟'(ℂ) × C(ℝ, ℂ) × (ℤ → ℤ → ℕ)`. -/
theorem identDistrib_distribution_curveVersion_mult_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
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
    IdentDistrib (fun ω => (H ω, η' ω, S.mult ε ω)) (fun ω => (H' ω, ζ' ω, S'.mult ε ω)) S.P S'.P := by
  obtain ⟨BL, hBLm, hBL⟩ := exists_decoder_mult_eq (ν := ν) hγ0 hγ2 hGnull hG
  let F : LQGMetric.DistC × C(ℝ, ℂ) → LQGMetric.DistC × C(ℝ, ℂ) × (ℤ → ℤ → ℕ) := fun x =>
    (x.1, x.2, bmEdgeCount ε (fun t => (BL x t).1) (fun t => (BL x t).2))
  have hFm : Measurable F :=
    measurable_fst.prodMk (measurable_snd.prodMk (Measurable.of_eval fun j => Measurable.of_eval fun k =>
      (measurable_bmEdgeCount_path ε j k).comp hBLm))
  have hA : (fun ω => (H ω, η' ω, S.mult ε ω)) =ᵐ[S.P] F ∘ fun ω => (H ω, η' ω) := by
    filter_upwards [hBL 𝒮 hν Ω S hS H hH hrep η' hη'm hη' ε] with ω hω
    change (H ω, η' ω, S.mult ε ω) =
      (H ω, η' ω, bmEdgeCount ε (fun t => (BL (H ω, η' ω) t).1) (fun t => (BL (H ω, η' ω) t).2))
    rw [hω]
  have hB : (fun ω => (H' ω, ζ' ω, S'.mult ε ω)) =ᵐ[S'.P] F ∘ fun ω => (H' ω, ζ' ω) := by
    filter_upwards [hBL 𝒮' hν' Ω' S' hS' H' hH' hrep' ζ' hζ'm hζ' ε] with ω hω
    change (H' ω, ζ' ω, S'.mult ε ω) =
      (H' ω, ζ' ω, bmEdgeCount ε (fun t => (BL (H' ω, ζ' ω) t).1) (fun t => (BL (H' ω, ζ' ω) t).2))
    rw [hω]
  have hid := (identDistrib_distribution_curveVersion_of_valid hν hν' hγ0 hγ2 hS hS' hH hH' hrep hrep' hη'm hη'
    hζ'm hζ').comp hFm
  exact ⟨hid.aemeasurable_fst.congr hA.symm, hid.aemeasurable_snd.congr hB.symm,
    (Measure.map_congr hA).trans (hid.map_eq.trans (Measure.map_congr hB).symm)⟩

/-- **The law of (field, curve, edge multiplicities) in two valid environments, with the mating-rigid sets of
Theorem 2.11.** Let `S, S'` be valid environments of models with the same normalized space-filling SLE law `ν` and the
same `0 < γ < 2`. If every `0 < γ < 2` has a one-sided mating-rigid set that is full for every `γ`-correlated
two-sided Brownian law, then for measurable random distributions `H, H'` with a.s. the pairings of the fields,
measurable continuous versions `η', ζ'` of the curves and every `ε`,
`S.P.map (H, η', S.mult ε) = S'.P.map (H', ζ', S'.mult ε)`. -/
theorem map_distribution_curveVersion_mult_eq_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC} (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂S'.P, ∀ φ : LQGMetric.TestC, S'.hC ω φ = H' ω φ)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ζ' : Ω' → C(ℝ, ℂ)} (hζ'm : Measurable ζ') (hζ' : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω) (ε : ℝ) :
    S.P.map (fun ω => (H ω, η' ω, S.mult ε ω)) = S'.P.map (fun ω => (H' ω, ζ' ω, S'.mult ε ω)) := by
  obtain ⟨G, hGnull, hG⟩ := hU γ hγ0 hγ2
  exact (identDistrib_distribution_curveVersion_mult_of_valid hν hν' hγ0 hγ2 hS hS' hGnull hG hH hH' hrep hrep'
    hη'm hη' hζ'm hζ' ε).map_eq

/-- **Every valid environment has the (field, curve, edge multiplicities) law of a reference environment.** Let `𝒮`
be a model with normalized space-filling SLE law `ν` and valid reference environments, and let every `0 < γ < 2` have
a one-sided mating-rigid set that is full for every `γ`-correlated two-sided Brownian law. For `0 < γ < 2` there are a
valid reference environment `S₀` of `𝒮` on `ℝ`, a measurable random distribution `H₀` with a.s. the pairings of its
field and a measurable continuous version `η₀` of its curve such that for every valid environment `S` of `𝒮`, on any
carrier, with measurable versions `H, η'` of its field and its curve, and every `ε`,
`S.P.map (H, η', S.mult ε) = S₀.P.map (H₀, η₀, S₀.mult ε)`. -/
theorem exists_reference_map_distribution_curveVersion_mult_eq {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ (S₀ : MatedCRTEnv ℝ) (H₀ : ℝ → LQGMetric.DistC) (η₀ : ℝ → C(ℝ, ℂ)), S₀.IsValid 𝒮 γ ∧
      Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
        ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) → ∀ ε : ℝ,
          S.P.map (fun ω => (H ω, η' ω, S.mult ε ω)) = S₀.P.map (fun ω => (H₀ ω, η₀ ω, S₀.mult ε ω)) := by
  obtain ⟨S₀, hS₀⟩ := href γ hγ0 hγ2
  obtain ⟨H₀, hH₀m, hrep₀⟩ := MatedCRT.Sec1.exists_fieldMeasurable_coneDistribution hS₀
  obtain ⟨_, _, _, _, _, _, _, _, _, η₀, _, hC, hae⟩ := hS₀.matingOfTrees
  have hH₀ : Measurable H₀ := hH₀m.mono (S₀.fieldSigma_le hS₀) le_rfl
  have hη₀ : ∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω := hae.mono fun ω h => h.1
  refine ⟨S₀, H₀, η₀, hS₀, hH₀, hrep₀, hC.measurable_curves.2.1, hη₀, ?_⟩
  intro Ω _ S hS H hH hrep η' hη'm hη' ε
  exact map_distribution_curveVersion_mult_eq_of_valid hν hν hγ0 hγ2 hS hS₀ hU hH hH₀ hrep hrep₀ hη'm hη'
    hC.measurable_curves.2.1 hη₀ ε

end MatedCRT.FirstPass.Derived
