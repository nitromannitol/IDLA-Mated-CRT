import MatedCRT.FirstPass.Derived.BoundaryPairDecoder
import LatticeProb.LQG.MatingOfTreesCouplingMerge

/-!
# The boundary-length decoder of a reference valid environment, read on another valid environment

Fix the decoder `BL₀` of a reference valid environment `S₀` (`exists_bm_eq_boundaryLength`) with the same
normalized space-filling SLE law and the same `γ` as `S`. The pair `(H, η')` has the same law in both environments
(`identDistrib_distribution_curveVersion_of_valid`), so the pair `Y = BL₀ (H, η')` read on `S`
* lies almost surely in every set of pairs whose complement is null for every `γ`-correlated two-sided Brownian
  law (`ae_boundaryLength_mem_of_valid`);
* has almost surely the merge property for `η'` (`ae_merge_boundaryLength_of_valid`): the failure of the merge
  property is an analytic event, so it is a property of the law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The reference decoder lands in every Brownian-full set.** Let `S₀` be a valid environment with the same
normalized space-filling SLE law and the same `0 < γ < 2` as `S`, and `BL₀` a measurable decoder of its
boundary-length pair from (field, curve). Then for every set `G` of pairs whose complement is null (in outer
measure) for every `γ`-correlated two-sided Brownian law, `BL₀ (H, η')` lies in `G` almost surely on `S`. -/
theorem ae_boundaryLength_mem_of_valid {𝒮 𝒮₀ : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
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
      μ Gᶜ = 0) :
    ∀ᵐ ω ∂S.P, BL₀ (H ω, η' ω) ∈ G := by
  have hlaw := (identDistrib_distribution_curveVersion_of_valid hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀ hrep hrep₀
    hη'm hη' hη₀'m hη₀').map_eq
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, ηw, η₀, hC, -⟩ := hS₀.matingOfTrees
  exact MeasureTheory.ae_mem_of_map_eq_of_map_compl_eq_zero (hH₀.prodMk hη₀'m) (hH.prodMk hη'm) hlaw
    hBL₀m hBL₀ (hGnull _ hC.boundaryLawBM)

/-- **The reference decoder has the merge property on every valid environment.** With `S₀`, `BL₀` as in
`ae_boundaryLength_mem_of_valid`, almost surely on `S` every direct `L`- or `R`-identification of the pair
`BL₀ (H, η')` gives the same point of `η'`. -/
theorem ae_merge_boundaryLength_of_valid {𝒮 𝒮₀ : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
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
    ∀ᵐ ω ∂S.P, ∀ s t : ℝ,
      (MatedCRTHarmonic.MatedCRT.DirectRel
          (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 0 u (BL₀ (H ω, η' ω))) s t ∨
        MatedCRTHarmonic.MatedCRT.DirectRel
          (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 1 u (BL₀ (H ω, η' ω))) s t) →
        η' ω s = η' ω t := by
  have hlaw := (identDistrib_distribution_curveVersion_of_valid hν hν₀ hγ0 hγ2 hS hS₀ hH hH₀ hrep hrep₀
    hη'm hη' hη₀'m hη₀').map_eq
  have := hS₀.isProbabilityMeasure
  have hf : Measurable fun p : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) => (p.2, BL₀ p) :=
    measurable_snd.prodMk hBL₀m
  have e : S.P.map (fun ω => (η' ω, BL₀ (H ω, η' ω))) =
      (S.P.map fun ω => (H ω, η' ω)).map (fun p : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) => (p.2, BL₀ p)) := by
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
  have h₀ : ∀ᵐ ω ∂S₀.P, ∀ s t : ℝ,
      (MatedCRTHarmonic.MatedCRT.DirectRel
          (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 0 u (BL₀ (H₀ ω, η₀' ω))) s t ∨
        MatedCRTHarmonic.MatedCRT.DirectRel
          (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 1 u (BL₀ (H₀ ω, η₀' ω))) s t) →
        η₀' ω s = η₀' ω t := by
    filter_upwards [ae_merge_curveVersion_of_valid hS₀ hη₀', hBL₀] with ω h1 h2
    rw [← h2]
    exact h1
  exact MatedCRTHarmonic.MatedCRT.ae_merge_of_map_eq
    (V := fun ω => (η₀' ω, BL₀ (H₀ ω, η₀' ω))) (V' := fun ω => (η' ω, BL₀ (H ω, η' ω)))
    (hη₀'m.prodMk (hBL₀m.comp (hH₀.prodMk hη₀'m))) (hη'm.prodMk (hBL₀m.comp (hH.prodMk hη'm))) hlaw' h₀

end MatedCRT.FirstPass.Derived
