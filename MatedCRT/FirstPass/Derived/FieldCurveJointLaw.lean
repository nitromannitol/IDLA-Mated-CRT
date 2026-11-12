import MatedCRT.FirstPass.Derived.FieldCurveIndep
import MatedCRT.FirstPass.Derived.ValidEnvironmentLaw

/-! # The joint law of the field and the curve of a valid environment

For valid environments of models with the same normalized space-filling SLE law and the same `0 < γ < 2`, on
arbitrary carriers, the pair (field, curve) has the same law: `(H, η')` and `(H', ζ')` are identically distributed in
`𝒟'(ℂ) × C(ℝ, ℂ)` for measurable versions `H, H'` of the fields (random distributions whose pairings are a.s. those of
the environments) and measurable continuous versions `η', ζ'` of the curves.

The proof follows `identDistrib_circleProcess_lqgMeasure_curve_of_valid`: the triple (distribution, circle averages,
LQG measure) is independent of the Lebesgue-parametrized curve `ηL` on both sides
(`indepFun_circleProcess_lqgMeasure_distribution_igCurve_of_coupling`), the curves `ηL` have the same law, and the
area-parametrized curve is a Borel function `areaParam μ ηL` of the LQG measure and `ηL`. This file takes the equality
of the laws of the triples as a hypothesis (`identDistrib_distribution_curveVersion_of_identDistrib_triple`). -/

open MeasureTheory ProbabilityTheory HarmonicBalls
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- **The pair (field, curve) has the same law for two valid environments whose triples (distribution, circle
averages, LQG measure) have the same law.** Here `S, S'` are valid environments of models with the same normalized
space-filling SLE law `ν` and the same `0 < γ < 2`, `H, H'` are measurable random distributions with a.s. the
pairings of `S, S'`, and `η', ζ'` are measurable continuous versions of the curves. -/
theorem identDistrib_distribution_curveVersion_of_identDistrib_triple {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC} (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂S'.P, ∀ φ : LQGMetric.TestC, S'.hC ω φ = H' ω φ)
    (htrip : IdentDistrib (fun ω => (H ω, circleProcess (S.hcirc ω), S.μ ω))
      (fun ω => (H' ω, circleProcess (S'.hcirc ω), S'.μ ω)) S.P S'.P)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ζ' : Ω' → C(ℝ, ℂ)} (hζ'm : Measurable ζ') (hζ' : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω) :
    IdentDistrib (fun ω => (H ω, η' ω)) (fun ω => (H' ω, ζ' ω)) S.P S'.P := by
  have := hS.isProbabilityMeasure
  have := hS'.isProbabilityMeasure
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, ηc, η₀, h, hae⟩ := hS.matingOfTrees
  obtain ⟨Y, Y₀, kIG₀, C, C', C₀, C₀', V, ζL, ζc, ζ₀, k, kae⟩ := hS'.matingOfTrees
  have hη : ∀ᵐ ω ∂S.P, ⇑(ηc ω) = S.η ω := hae.mono fun _ hω => hω.1
  have kη : ∀ᵐ ω ∂S'.P, ⇑(ζc ω) = S'.η ω := kae.mono fun _ hω => hω.1
  have hLm := h.measurable_curves.1
  have kLm := k.measurable_curves.1
  -- the Lebesgue-parametrized curves have the same law
  have hLL : IdentDistrib ηL ζL S.P S'.P := by
    refine ⟨hLm.aemeasurable, kLm.aemeasurable, measurableEmbedding_slePathCode.map_injective ?_⟩
    rw [Measure.map_map measurableEmbedding_slePathCode.measurable hLm,
      Measure.map_map measurableEmbedding_slePathCode.measurable kLm]
    exact (map_slePathCode_igCurve_of_valid hν hγ0 hγ2 hS h hη).trans
      (map_slePathCode_igCurve_of_valid hν' hγ0 hγ2 hS' k kη).symm
  -- the triples are independent of the curves
  have hperm : Measurable fun q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ × LQGMetric.DistC =>
      (q.2.2, q.1, q.2.1) :=
    (measurable_snd.comp measurable_snd).prodMk (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hind : IndepFun (fun ω => (H ω, circleProcess (S.hcirc ω), S.μ ω)) ηL S.P :=
    (indepFun_circleProcess_lqgMeasure_distribution_igCurve_of_coupling hS hγ0 hγ2 h
      (hae.mono fun _ hω => hω.2) hrep).comp hperm measurable_id
  have kind : IndepFun (fun ω => (H' ω, circleProcess (S'.hcirc ω), S'.μ ω)) ζL S'.P :=
    (indepFun_circleProcess_lqgMeasure_distribution_igCurve_of_coupling hS' hγ0 hγ2 k
      (kae.mono fun _ hω => hω.2) hrep').comp hperm measurable_id
  have hpair := htrip.prodMk hLL hind kind
  -- apply the area parametrization and restrict to rational times
  have hm : Measurable fun p : (LQGMetric.DistC × (Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ) × C(ℝ, ℂ) =>
      (p.1.1, fun q : ℚ => areaParam p.1.2.2 p.2 (q : ℝ)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_pi_iff.2 fun q => (measurable_pi_apply (q : ℝ)).comp
        (measurable_areaParam_curve.comp
          ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
  have h3 := hpair.comp hm
  have hcurve : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] {S₁ : MatedCRTEnv Ω₁} {𝒮₁ : SpaceFillingSLEModel}
      {c : Ω₁ → C(ℝ, ℂ)}, S₁.IsValid 𝒮₁ γ → (∀ᵐ ω ∂S₁.P, IsLebesgueRepresentative (S₁.η ω) (c ω)) →
      ∀ᵐ ω ∂S₁.P, areaParam (S₁.μ ω) (c ω) = S₁.η ω := by
    intro Ω₁ _ S₁ 𝒮₁ c hS₁ hrep
    have hlqg : ∀ᵐ ω ∂S₁.P, IsLQGLimit γ (S₁.hcirc ω) (S₁.μ ω) := hS₁.isLQGMeasure
    filter_upwards [hlqg, hS₁.isAreaParametrized, hrep] with ω hl ha hr
    have : IsLocallyFiniteMeasure (S₁.μ ω) := hl.isLocallyFiniteMeasure
    exact areaParam_eq_of_isLebesgueRepresentative ha hr
  have e1 := hcurve hS (ae_isLebesgueRepresentative_of_coupling h hη)
  have e2 := hcurve hS' (ae_isLebesgueRepresentative_of_coupling k kη)
  have hcode : IdentDistrib (fun ω => (H ω, slePathCode (η' ω))) (fun ω => (H' ω, slePathCode (ζ' ω)))
      S.P S'.P := by
    refine (IdentDistrib.of_ae_eq
      (hH.prodMk (measurableEmbedding_slePathCode.measurable.comp hη'm)).aemeasurable ?_).trans
      (h3.trans (IdentDistrib.of_ae_eq h3.aemeasurable_snd ?_))
    · filter_upwards [hη', e1] with ω h1 h2
      simp only [Function.comp_apply]
      rw [slePathCode_eq_restrict h1, h2]
    · filter_upwards [hζ', e2] with ω h1 h2
      simp only [Function.comp_apply]
      rw [slePathCode_eq_restrict h1, h2]
  have hemb : MeasurableEmbedding (Prod.map (id : LQGMetric.DistC → LQGMetric.DistC) slePathCode) :=
    MeasurableEmbedding.id.prodMap measurableEmbedding_slePathCode
  refine ⟨(hH.prodMk hη'm).aemeasurable, (hH'.prodMk hζ'm).aemeasurable, hemb.map_injective ?_⟩
  rw [Measure.map_map hemb.measurable (hH.prodMk hη'm), Measure.map_map hemb.measurable (hH'.prodMk hζ'm)]
  exact hcode.map_eq

end MatedCRT.FirstPass.Derived
