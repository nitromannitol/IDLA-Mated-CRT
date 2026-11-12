import LatticeProb.Prob.IdentDistribProdRestrict
import MatedCRT.FirstPass.Derived.CircleProcessLawValid
import MatedCRT.FirstPass.Derived.FieldCurveIndep
import MatedCRT.FirstPass.Derived.JointMeasureLawTwoSpaces
import MatedCRT.FirstPass.Derived.ValidEnvironmentLaw
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field

/-! # The joint law of the field and the curve of a valid environment

For valid environments of models with the same normalized space-filling SLE law and the same `0 < γ < 2`, on
arbitrary carriers, the pair (field, curve) has the same law: `(H, η')` and `(H', ζ')` are identically distributed in
`𝒟'(ℂ) × C(ℝ, ℂ)` for measurable versions `H, H'` of the fields (random distributions whose pairings are a.s. those of
the environments) and measurable continuous versions `η', ζ'` of the curves.

The proof follows `identDistrib_circleProcess_lqgMeasure_curve_of_valid`: the triple (distribution, circle averages,
LQG measure) is independent of the Lebesgue-parametrized curve `ηL` on both sides
(`indepFun_circleProcess_lqgMeasure_distribution_igCurve_of_coupling`), the curves `ηL` have the same law, and the
area-parametrized curve is a Borel function `areaParam μ ηL` of the LQG measure and `ηL`. The equality of the laws of
the triples (`identDistrib_distribution_circleProcess_lqgMeasure_of_valid`) follows from the joint law of
(distribution, circle averages) and the fact that the LQG measure is a.s. the limit of the circle-average
approximations on each event `{H ∈ A}`; this gives `identDistrib_distribution_curveVersion_of_valid`. -/

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

/-- **The triple (distribution, circle averages, LQG measure) has the same law for two valid environments** with the
same `0 < γ < 2`, for measurable random distributions `H, H'` with a.s. the pairings of `S, S'`. On each event
`{H ∈ A}` the pairs (circle averages, LQG measure) have the same law, since the circle-average processes do (by the
joint law of the distribution and the circle averages) and the LQG measure is a.s. the limit of the circle-average
approximations. -/
theorem identDistrib_distribution_circleProcess_lqgMeasure_of_valid {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'} {𝒮 𝒮' : SpaceFillingSLEModel} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC} (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂S'.P, ∀ φ : LQGMetric.TestC, S'.hC ω φ = H' ω φ) :
    IdentDistrib (fun ω => (H ω, circleProcess (S.hcirc ω), S.μ ω))
      (fun ω => (H' ω, circleProcess (S'.hcirc ω), S'.μ ω)) S.P S'.P := by
  have := hS.isProbabilityMeasure
  have := hS'.isProbabilityMeasure
  have hcp := identDistrib_circleProcess_of_valid hS hS'
  have hpair : IdentDistrib (fun ω => (H ω, circleProcess (S.hcirc ω)))
      (fun ω => (H' ω, circleProcess (S'.hcirc ω))) S.P S'.P :=
    ⟨hH.aemeasurable.prodMk hcp.aemeasurable_fst, hH'.aemeasurable.prodMk hcp.aemeasurable_snd,
      MatedCRT.Sec1.map_distribution_circles_eq_of_cones hS hS' hH hH' hrep hrep'⟩
  refine LatticeProb.identDistrib_prodMk_of_forall_restrict hH hH' fun A hA => ?_
  have hμ : ∀ᵐ ω ∂S.P, IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hS.isLQGMeasure
  have hν : ∀ᵐ ω ∂S'.P, IsLQGLimit γ (S'.hcirc ω) (S'.μ ω) := hS'.isLQGMeasure
  exact identDistrib_circleProcess_lqgMeasure_of_identDistrib
    (ae_restrict_of_ae hS.isQuantumCone.ae_continuousOn_circle)
    (ae_restrict_of_ae hS'.isQuantumCone.ae_continuousOn_circle) (ae_restrict_of_ae hμ) (ae_restrict_of_ae hν)
    (aemeasurable_mu_of_valid hγ0 hγ2 hS).restrict (aemeasurable_mu_of_valid hγ0 hγ2 hS').restrict
    (LatticeProb.identDistrib_restrict_preimage_of_prodMk hH hH' hpair hA)

/-- **The pair (field, curve) has the same law for two valid environments** of models with the same normalized
space-filling SLE law `ν` and the same `0 < γ < 2`: `(H, η')` and `(H', ζ')` are identically distributed in
`𝒟'(ℂ) × C(ℝ, ℂ)` for measurable versions `H, H'` of the fields and measurable continuous versions `η', ζ'` of the
curves. -/
theorem identDistrib_distribution_curveVersion_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ)
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC} (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂S'.P, ∀ φ : LQGMetric.TestC, S'.hC ω φ = H' ω φ)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ζ' : Ω' → C(ℝ, ℂ)} (hζ'm : Measurable ζ') (hζ' : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω) :
    IdentDistrib (fun ω => (H ω, η' ω)) (fun ω => (H' ω, ζ' ω)) S.P S'.P :=
  identDistrib_distribution_curveVersion_of_identDistrib_triple hν hν' hγ0 hγ2 hS hS' hH hH' hrep hrep'
    (identDistrib_distribution_circleProcess_lqgMeasure_of_valid hγ0 hγ2 hS hS' hH hH' hrep hrep')
    hη'm hη' hζ'm hζ'

end MatedCRT.FirstPass.Derived
