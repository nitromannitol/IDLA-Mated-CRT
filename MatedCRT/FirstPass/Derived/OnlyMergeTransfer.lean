import MatedCRT.FirstPass.Derived.MultOfFieldCurve
import MatedCRT.FirstPass.Derived.MatingRelBorel

/-!
# The reference decoder generates the fibre relation on every valid environment

Let `BL₀` be the boundary-length decoder of a reference valid environment `S₀`. On another valid environment `S`
with the same normalized space-filling SLE law and the same `γ`, the pair `Y = BL₀ (H, η')` has the merge property
for `η'` (`ae_merge_boundaryLength_of_valid`, DMS14 Lemma 8.8). This module adds the converse inclusion (DMS14
Lemma 8.14): two times in the same fibre of `η'` are identified by the mating relation of `Y`. Since the mating
relation `{(b, s, t) | matingRel b s t}` is Borel (`measurableSet_matingRel`), the failure of this inclusion is the
projection of a Borel set, hence analytic, hence a property of the law.

* `analyticSet_setOf_not_onlyMerge`, `ae_onlyMerge_of_map_eq`: the analytic set and the transfer between random pairs
  with the same law;
* `ae_onlyMerge_boundaryLength_of_valid`: the converse inclusion for `BL₀ (H, η')` on `S`;
* `ae_matingRel_boundaryLength_eq_fibre_of_valid`: with the merge property, the mating relation of `BL₀ (H, η')` is
  almost surely the fibre relation of the curve of `S`;
* `ae_mult_eq_boundaryLength_of_reference_of_matingRigidOn`, `exists_decoder_mult_eq_of_matingRigidOn`: the edge
  multiplicities as one measurable function of field and curve, under two-sided mating rigidity `MatingRigidOn G`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The failure of the converse merge property is analytic.** The pairs `(η, b)` having two times `s, t` in the
same fibre of `η` that are not identified by the mating relation of `b` form an analytic subset of
`C(ℝ, ℂ) × Path2`: the projection of a Borel set of `(η, b, s, t)`, by `measurableSet_matingRel`. -/
theorem analyticSet_setOf_not_onlyMerge :
    AnalyticSet {p : C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2 | ∃ s t : ℝ,
      p.1 s = p.1 t ∧ ¬ matingRel p.2 s t} := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  have : PolishSpace MatedCRTHarmonic.MatedCRT.Path2 := LQGMetric.polishSpace_continuousMap ℝ (ℝ × ℝ)
  have hR : MeasurableSet {r : (C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2) × ℝ × ℝ |
      matingRel r.1.2 r.2.1 r.2.2} :=
    measurableSet_matingRel.preimage ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have h1 : Continuous fun r : (C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2) × ℝ × ℝ => r.1.1 r.2.1 :=
    ContinuousEval.continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  have h2 : Continuous fun r : (C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2) × ℝ × ℝ => r.1.1 r.2.2 :=
    ContinuousEval.continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))
  have heq : MeasurableSet {r : (C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2) × ℝ × ℝ |
      r.1.1 r.2.1 = r.1.1 r.2.2} :=
    (isClosed_eq h1 h2).measurableSet
  have hT : AnalyticSet {r : (C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2) × ℝ × ℝ |
      r.1.1 r.2.1 = r.1.1 r.2.2 ∧ ¬ matingRel r.1.2 r.2.1 r.2.2} :=
    (heq.inter hR.compl).analyticSet
  have hset : {p : C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2 | ∃ s t : ℝ,
      p.1 s = p.1 t ∧ ¬ matingRel p.2 s t} =
      Prod.fst '' {r : (C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2) × ℝ × ℝ |
        r.1.1 r.2.1 = r.1.1 r.2.2 ∧ ¬ matingRel r.1.2 r.2.1 r.2.2} := by
    ext p
    constructor
    · rintro ⟨s, t, hst, hne⟩
      exact ⟨(p, s, t), ⟨hst, hne⟩, rfl⟩
    · rintro ⟨⟨q, s, t⟩, ⟨hst, hne⟩, rfl⟩
      exact ⟨s, t, hst, hne⟩
  rw [hset]
  exact hT.image_of_continuous continuous_fst

/-- **The converse merge property passes between random pairs with the same law.** Let `V` and `V'` be measurable
random elements of `C(ℝ, ℂ) × Path2`, on possibly different probability spaces, with the same law. If almost surely
any two times in the same fibre of the curve `(V ω).1` are identified by the mating relation of the pair `(V ω).2`,
then the same holds almost surely for `V'`. -/
theorem ae_onlyMerge_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    [IsFiniteMeasure P] {P' : Measure Ω'} {V : Ω → C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2}
    {V' : Ω' → C(ℝ, ℂ) × MatedCRTHarmonic.MatedCRT.Path2}
    (hV : Measurable V) (hV' : Measurable V') (hlaw : P'.map V' = P.map V)
    (h : ∀ᵐ ω ∂P, ∀ s t : ℝ, (V ω).1 s = (V ω).1 t → matingRel (V ω).2 s t) :
    ∀ᵐ ω ∂P', ∀ s t : ℝ, (V' ω).1 s = (V' ω).1 t → matingRel (V' ω).2 s t := by
  have : PolishSpace C(ℝ, ℂ) := LQGMetric.polishSpace_continuousMap ℝ ℂ
  have : PolishSpace MatedCRTHarmonic.MatedCRT.Path2 := LQGMetric.polishSpace_continuousMap ℝ (ℝ × ℝ)
  have hS := (LatticeProb.AnalyticSet.nullMeasurableSet (P.map V) analyticSet_setOf_not_onlyMerge).compl
  have h' := ae_comp_of_map_eq_of_nullMeasurableSet hV hV' hlaw hS (by
    filter_upwards [h] with ω hω
    show ¬ ∃ s t : ℝ, _
    rintro ⟨s, t, hst, hne⟩
    exact hne (hω s t hst))
  filter_upwards [h'] with ω hω s t hst
  by_contra hne
  exact hω (show ∃ s t : ℝ, _ from ⟨s, t, hst, hne⟩)

/-- **The reference decoder identifies every fibre of the curve.** With `S₀`, `BL₀` as in
`ae_merge_boundaryLength_of_valid`, almost surely on `S` any two times in the same fibre of `η'` are identified by
the mating relation of the pair `BL₀ (H, η')`. -/
theorem ae_onlyMerge_boundaryLength_of_valid {𝒮 𝒮₀ : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hν₀ : HasNormalizedSLELaw 𝒮₀ ν)
    {Ω Ω₀ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {S : MatedCRTEnv Ω} {S₀ : MatedCRTEnv Ω₀}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS₀ : S₀.IsValid 𝒮₀ γ)
    {H : Ω → LQGMetric.DistC} {H₀ : Ω₀ → LQGMetric.DistC} (hH : Measurable H) (hH₀ : Measurable H₀)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep₀ : ∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {η₀' : Ω₀ → C(ℝ, ℂ)} (hη₀'m : Measurable η₀') (hη₀' : ∀ᵐ ω ∂S₀.P, ⇑(η₀' ω) = S₀.η ω)
    {BL₀ : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) → MatedCRTHarmonic.MatedCRT.Path2}
    (hBL₀m : Measurable BL₀) (hBL₀ : ∀ᵐ ω ∂S₀.P, S₀.bm ω = BL₀ (H₀ ω, η₀' ω)) :
    ∀ᵐ ω ∂S.P, ∀ s t : ℝ, η' ω s = η' ω t → matingRel (BL₀ (H ω, η' ω)) s t := by
  have hlaw := (identDistrib_distribution_curveVersion_of_valid hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀ hrep hrep₀
    hη'm hη' hη₀'m hη₀').map_eq
  have := hS₀.isProbabilityMeasure
  have hf : Measurable fun p : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) => (p.2, BL₀ p) :=
    measurable_snd.prodMk hBL₀m
  have e : S.P.map (fun ω => (η' ω, BL₀ (H ω, η' ω))) =
      (S.P.map fun ω => (H ω, η' ω)).map
        (fun p : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) => (p.2, BL₀ p)) := by
    rw [Measure.map_map hf (hH.prodMk hη'm)]
    rfl
  have e₀ : S₀.P.map (fun ω => (η₀' ω, BL₀ (H₀ ω, η₀' ω))) =
      (S₀.P.map fun ω => (H₀ ω, η₀' ω)).map
        (fun p : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) => (p.2, BL₀ p)) := by
    rw [Measure.map_map hf (hH₀.prodMk hη₀'m)]
    rfl
  have hlaw' : S.P.map (fun ω => (η' ω, BL₀ (H ω, η' ω))) =
      S₀.P.map (fun ω => (η₀' ω, BL₀ (H₀ ω, η₀' ω))) := by
    rw [e, e₀, hlaw]
  have h₀ : ∀ᵐ ω ∂S₀.P, ∀ s t : ℝ, η₀' ω s = η₀' ω t → matingRel (BL₀ (H₀ ω, η₀' ω)) s t := by
    filter_upwards [hS₀.ae_matingRel_eq_fibre, hη₀', hBL₀] with ω h1 h2 h3 s t hst
    rw [← h3, h1, ← h2]
    exact hst
  exact ae_onlyMerge_of_map_eq
    (V := fun ω => (η₀' ω, BL₀ (H₀ ω, η₀' ω))) (V' := fun ω => (η' ω, BL₀ (H ω, η' ω)))
    (hη₀'m.prodMk (hBL₀m.comp (hH₀.prodMk hη₀'m)))
    (hη'm.prodMk (hBL₀m.comp (hH.prodMk hη'm))) hlaw' h₀

/-- **The reference decoder generates the fibre relation.** With `S₀`, `BL₀` as in
`ae_merge_boundaryLength_of_valid`, almost surely on `S` the mating relation of the pair `BL₀ (H, η')` is the fibre
relation `S.η s = S.η t` of the space-filling curve of `S`. -/
theorem ae_matingRel_boundaryLength_eq_fibre_of_valid {𝒮 𝒮₀ : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν₀ : HasNormalizedSLELaw 𝒮₀ ν)
    {Ω Ω₀ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {S : MatedCRTEnv Ω} {S₀ : MatedCRTEnv Ω₀}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS₀ : S₀.IsValid 𝒮₀ γ)
    {H : Ω → LQGMetric.DistC} {H₀ : Ω₀ → LQGMetric.DistC} (hH : Measurable H) (hH₀ : Measurable H₀)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep₀ : ∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {η₀' : Ω₀ → C(ℝ, ℂ)} (hη₀'m : Measurable η₀') (hη₀' : ∀ᵐ ω ∂S₀.P, ⇑(η₀' ω) = S₀.η ω)
    {BL₀ : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) → MatedCRTHarmonic.MatedCRT.Path2}
    (hBL₀m : Measurable BL₀) (hBL₀ : ∀ᵐ ω ∂S₀.P, S₀.bm ω = BL₀ (H₀ ω, η₀' ω)) :
    ∀ᵐ ω ∂S.P, matingRel (BL₀ (H ω, η' ω)) = fun s t => S.η ω s = S.η ω t := by
  filter_upwards [ae_merge_boundaryLength_of_valid hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀ hrep hrep₀
      hη'm hη' hη₀'m hη₀' hBL₀m hBL₀,
    ae_onlyMerge_boundaryLength_of_valid hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀ hrep hrep₀
      hη'm hη' hη₀'m hη₀' hBL₀m hBL₀, hη'] with ω h1 h2 h3
  rw [← h3]
  exact matingRel_eq_fibre_of_merge (η := ⇑(η' ω)) h1 h2

/-- **Edge multiplicities from field and curve, two-sided rigidity.** With `S₀`, `BL₀` as in
`ae_merge_boundaryLength_of_valid`, and a mating-rigid set `G` that is full for every `γ`-correlated two-sided
Brownian law, the edge multiplicity of `S` is almost surely the mated-CRT edge count of `BL₀ (H, η')`. -/
theorem ae_mult_eq_boundaryLength_of_reference_of_matingRigidOn {𝒮 𝒮₀ : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν₀ : HasNormalizedSLELaw 𝒮₀ ν)
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
    (hG : MatingRigidOn G) (ε : ℝ) :
    ∀ᵐ ω ∂S.P, S.mult ε ω =
      bmEdgeCount ε (fun t => (BL₀ (H ω, η' ω) t).1) (fun t => (BL₀ (H ω, η' ω) t).2) :=
  hS.ae_mult_eq_of_matingRigidOn hGnull hG (Y := fun ω => BL₀ (H ω, η' ω))
    (ae_boundaryLength_mem_of_valid hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀ hrep hrep₀
      hη'm hη' hη₀'m hη₀' hBL₀m hBL₀ hGnull)
    (ae_matingRel_boundaryLength_eq_fibre_of_valid hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀ hrep hrep₀
      hη'm hη' hη₀'m hη₀' hBL₀m hBL₀) ε

/-- **One decoder for all valid environments, two-sided rigidity.** Fix a normalized space-filling SLE law `ν`,
`0 < γ < 2`, and a mating-rigid set `G` that is full for every `γ`-correlated two-sided Brownian law. There is a
measurable `BL : Field × C(ℝ, ℂ) → Path2` such that, for every valid environment `S` whose model has law `ν`, every
measurable version `H` of its field and every measurable continuous version `η'` of its curve, almost surely
`S.mult ε = bmEdgeCount ε (BL (H, η'))` for every `ε`. (If no valid environment with measurable versions exists, any
measurable `BL` serves.) -/
theorem exists_decoder_mult_eq_of_matingRigidOn {ν : ℝ → Measure SLEPathCode} {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
      μ Gᶜ = 0)
    (hG : MatingRigidOn G) :
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
    exact ae_mult_eq_boundaryLength_of_reference_of_matingRigidOn hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀
      hrep hrep₀ hη'm hη' hη₀'m hη₀' hBL₀m hBL₀ hGnull hG ε
  · refine ⟨fun _ => 0, measurable_const, fun 𝒮 hν Ω _ S hS H hH hrep η' hη'm hη' ε => ?_⟩
    exact (hex ⟨𝒮, Ω, inferInstance, S, H, η', hν, hS, hH, hrep, hη'm, hη'⟩).elim

end MatedCRT.FirstPass.Derived
