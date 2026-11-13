import MatedCRT.FirstPass.Derived.FieldCurveJointLaw
import MatedCRT.FirstPass.Derived.MatingRelation

/-!
# The boundary-length pair of a valid environment as a function of (field, curve)

For a valid environment `S` with measurable versions `H` of its field and `η'` of its curve:
* `exists_bm_eq_boundaryLength`: the boundary-length pair is almost surely `BL (H, η')` for a measurable `BL`
  (the `boundaryLength` clause of its mating-of-trees coupling, whose field argument is a.s. `H` by the pairing
  clause of `IsValid.matingOfTrees`);
* `ae_merge_curveVersion_of_valid`: almost surely every direct `L`- or `R`-identification of the boundary-length
  pair gives the same point of `η'` (the `merge` clause, DMS14 Lemma 8.8).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The boundary-length pair as a function of the field and the curve.** In a valid environment, for measurable
versions `H` of the field and `η'` of the curve, the boundary-length pair is almost surely `BL (H, η')` for a
measurable `BL` (the `boundaryLength` clause of the mating-of-trees coupling). -/
theorem exists_bm_eq_boundaryLength {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) {H : Ω → LQGMetric.DistC}
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) {η' : Ω → C(ℝ, ℂ)}
    (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) :
    ∃ BL : MatedCRTHarmonic.MatedCRT.Field × C(ℝ, ℂ) → MatedCRTHarmonic.MatedCRT.Path2, Measurable BL ∧
      ∀ᵐ ω ∂S.P, S.bm ω = BL (H ω, η' ω) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, ηw, η₀, hC, hae⟩ := hS.matingOfTrees
  obtain ⟨BL, hBLm, hBL, -⟩ := hC.boundaryLength
  refine ⟨BL, hBLm, ?_⟩
  filter_upwards [hBL, hae, hrep, hη'] with ω h1 h2 h3 h4
  have hX : MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) = H ω :=
    DFunLike.ext _ _ fun φ => (h2.2 φ).symm.trans (h3 φ)
  have hc : ηw ω = η' ω := DFunLike.coe_injective (h2.1.trans h4.symm)
  rw [h1, hX, hc]

/-- **The merge property of a valid environment**, for a continuous version `η'` of its curve: almost surely every
direct `L`- or `R`-identification of the boundary-length pair gives the same point of `η'`. -/
theorem ae_merge_curveVersion_of_valid {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) :
    ∀ᵐ ω ∂S.P, ∀ s t : ℝ,
      (MatedCRTHarmonic.MatedCRT.DirectRel (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 0 u (S.bm ω)) s t ∨
        MatedCRTHarmonic.MatedCRT.DirectRel (fun u => MatedCRTHarmonic.MatedCRT.lrCoord 1 u (S.bm ω)) s t) →
        η' ω s = η' ω t := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, ηw, η₀, hC, hae⟩ := hS.matingOfTrees
  filter_upwards [hC.merge, hae, hη'] with ω h1 h2 h3 s t hst
  calc η' ω s = S.η ω s := congrFun h3 s
    _ = ηw ω s := (congrFun h2.1 s).symm
    _ = ηw ω t := h1 s t hst
    _ = S.η ω t := congrFun h2.1 t
    _ = η' ω t := (congrFun h3 t).symm

end MatedCRT.FirstPass.Derived
