import MatedCRT.FirstPass.Derived.ConeCurveIndep
import MatedCRT.FirstPass.Derived.SimilarityAssembly
import MatedCRT.FirstPass.Derived.SimilarityLawInvariance
import Mathlib.Probability.IdentDistribIndep

/-!
# The joint law of a valid environment

For a valid environment `S` with cone parameter `0 < γ < 2` whose space-filling SLE model has the normalized law `ν`,
the triple `(circle-average process, LQG measure, space-filling curve)` has a law that depends only on `γ` and `ν`:

* under the mating-of-trees coupling, the Lebesgue-parametrized curve `ηL` is almost surely a Lebesgue-area
  representative of the curve `S.η` (`ae_isLebesgueRepresentative_of_coupling`), so the law of `ηL` is the normalized
  space-filling SLE law (`map_slePathCode_igCurve_of_valid`);
* the pair `(circle averages, LQG measure)` has the same law for all valid environments with the same `γ`, and it is
  independent of `ηL`; hence the law of `((circle averages, LQG measure), ηL)` is a product law determined by `γ, ν`;
* the curve is the area parametrization of `ηL` by the LQG measure, a measurable function of the pair.
-/

open MeasureTheory ProbabilityTheory HarmonicBalls
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- Under the mating-of-trees coupling, the Lebesgue-parametrized whole-plane space-filling SLE `ηL` is almost surely a
Lebesgue-area representative of every curve that agrees almost surely with its LQG-area reparametrization `η'`. -/
theorem ae_isLebesgueRepresentative_of_coupling {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2} {η : Ω → ℝ → ℂ}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀ bm)
    (hη : ∀ᵐ ω ∂P, ⇑(η' ω) = η ω) :
    ∀ᵐ ω ∂P, IsLebesgueRepresentative (η ω) (ηL ω) := by
  filter_upwards [h.spaceFilling, h.areaParam, hη] with ω hsf hap hηω
  obtain ⟨hsurj, htend, h0, hvol⟩ := hsf
  obtain ⟨⟨φ, hφ0, hφ⟩, -⟩ := hap
  exact ⟨h0, hsurj, htend, hvol, φ, hφ0, fun t => (congrFun hηω t).symm.trans (hφ t)⟩

/-- For a valid environment of a model with the normalized law `ν`, the law of the rational-time code of the
Lebesgue-parametrized curve of the mating-of-trees coupling is `ν (16 / γ²)`. -/
theorem map_slePathCode_igCurve_of_valid {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀ bm)
    (hη : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) :
    S.P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2) := by
  have hκ : 4 < 16 / γ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  exact hν Ω _ S.P S.fieldSigma (16 / γ ^ 2) S.η ηL hS.isProbabilityMeasure hκ hS.isSLE
    h.measurable_curves.1 (ae_isLebesgueRepresentative_of_coupling h hη)

/-- **The joint law of (circle averages, LQG measure, curve) of a valid environment depends only on `γ` and on the
normalized space-filling SLE law `ν`**: for valid environments `S, S'` of models with the same normalized law `ν` and the
same `0 < γ < 2`, on arbitrary carriers, the triples are identically distributed. -/
theorem identDistrib_circleProcess_lqgMeasure_curve_of_valid {𝒮 𝒮' : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν' : HasNormalizedSLELaw 𝒮' ν)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ) :
    IdentDistrib (fun ω => (circleProcess (S.hcirc ω), S.μ ω, S.η ω))
      (fun ω => (circleProcess (S'.hcirc ω), S'.μ ω, S'.η ω)) S.P S'.P := by
  have := hS.isProbabilityMeasure
  have := hS'.isProbabilityMeasure
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, h, hae⟩ := hS.matingOfTrees
  obtain ⟨Y, Y₀, kIG₀, C, C', C₀, C₀', V, ζL, ζ', ζ₀, k, kae⟩ := hS'.matingOfTrees
  have hη : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω := hae.mono fun _ hω => hω.1
  have kη : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω := kae.mono fun _ hω => hω.1
  have hLm := h.measurable_curves.1
  have kLm := k.measurable_curves.1
  -- the Lebesgue-parametrized curves have the same law
  have hLL : IdentDistrib ηL ζL S.P S'.P := by
    refine ⟨hLm.aemeasurable, kLm.aemeasurable, measurableEmbedding_slePathCode.map_injective ?_⟩
    rw [Measure.map_map measurableEmbedding_slePathCode.measurable hLm,
      Measure.map_map measurableEmbedding_slePathCode.measurable kLm]
    exact (map_slePathCode_igCurve_of_valid hν hγ0 hγ2 hS h hη).trans
      (map_slePathCode_igCurve_of_valid hν' hγ0 hγ2 hS' k kη).symm
  -- the pair (cone data, curve) has the same law, by independence on both sides
  have hpair := (identDistrib_circleProcess_lqgMeasure_of_valid hγ0 hγ2 hS hS').prodMk hLL
    (indepFun_circleProcess_lqgMeasure_igCurve_of_coupling hS hγ0 hγ2 h (hae.mono fun _ hω => hω.2))
    (indepFun_circleProcess_lqgMeasure_igCurve_of_coupling hS' hγ0 hγ2 k (kae.mono fun _ hω => hω.2))
  -- apply the area parametrization
  have hm : Measurable fun p : ((Set.Ioi (0 : ℝ) × ℂ → ℝ) × Measure ℂ) × C(ℝ, ℂ) =>
      (p.1.1, p.1.2, areaParam p.1.2 p.2) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_areaParam_curve.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
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
  refine (IdentDistrib.of_ae_eq h3.aemeasurable_fst ?_).symm.trans
    (h3.trans (IdentDistrib.of_ae_eq h3.aemeasurable_snd ?_))
  · filter_upwards [e1] with ω hω
    exact Prod.ext rfl (Prod.ext rfl hω)
  · filter_upwards [e2] with ω hω
    exact Prod.ext rfl (Prod.ext rfl hω)

end MatedCRT.FirstPass.Derived
