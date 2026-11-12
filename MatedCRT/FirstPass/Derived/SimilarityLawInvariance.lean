import MatedCRT.External.SLE
import MatedCRT.FirstPass.Derived.SimilarityScaling

/-!
# Scale invariance of the law of the Lebesgue-area representative

For a space-filling SLE model with a normalized law (`HasNormalizedSLELaw`) and scale invariance
(`SLEScaleInvarianceInput`), the law of a measurable Lebesgue-area representative `ηL` of `η` is invariant under
the deterministic rescaling `scaleRep a`, for every `a > 0`.

The rational-time code `slePathCode : C(ℝ, ℂ) → (ℚ → ℂ)` is a continuous injection of a Polish space into a
Hausdorff space with the Borel product σ-algebra, hence a measurable embedding; so the law of the code
determines the law of the path.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Filter Topology
open MatedCRT

theorem continuous_slePathCode : Continuous slePathCode :=
  continuous_pi fun q => continuous_eval_const (q : ℝ)

theorem injective_slePathCode : Function.Injective slePathCode := by
  intro c d h
  have hcd : (c : ℝ → ℂ) = d := by
    refine DenseRange.equalizer Rat.denseRange_cast c.continuous d.continuous ?_
    funext q
    exact congrFun h q
  exact DFunLike.ext' hcd

theorem measurableEmbedding_slePathCode : MeasurableEmbedding slePathCode :=
  continuous_slePathCode.measurableEmbedding injective_slePathCode

/-- **The law of the Lebesgue-area representative is invariant under the rescalings `scaleRep a`.** -/
theorem map_scaleRep_eq_of_law {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hsc : SLEScaleInvarianceInput 𝒮)
    {Ω : Type} {𝓕 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 4 < κ) {η : Ω → ℝ → ℂ} {ηL : Ω → C(ℝ, ℂ)}
    (hη : @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 κ η) (hηm : Measurable[mΩ] ηL)
    (hrep : ∀ᵐ ω ∂P, IsLebesgueRepresentative (η ω) (ηL ω)) {a : ℝ} (ha : 0 < a) :
    (P.map ηL).map (scaleRep a) = P.map ηL := by
  have hsa : Measurable (scaleRep a) := by
    have h := measurable_scaleRep.comp ((measurable_const (a := a)).prodMk
      (measurable_id (α := C(ℝ, ℂ))))
    simpa [ha, Function.comp_def] using h
  have hη' := hsc Ω mΩ P 𝓕 κ η hκ hη (fun _ => a⁻¹) measurable_const (fun _ => inv_pos.2 ha)
  have hrep' : ∀ᵐ ω ∂P, IsLebesgueRepresentative
      (fun s => (((fun _ : Ω => a⁻¹) ω : ℝ) : ℂ) * η ω s) (scaleRep a (ηL ω)) := by
    filter_upwards [hrep] with ω hω
    have h := isLebesgueRepresentative_scaleRep ha one_pos hω
    have heq : (fun s => (((fun _ : Ω => a⁻¹) ω : ℝ) : ℂ) * η ω s) =
        fun s => (a : ℂ)⁻¹ * η ω (1 * s) := by
      funext s
      simp
    rw [heq]
    exact h
  have h1 := hν Ω mΩ P 𝓕 κ η ηL ‹_› hκ hη hηm hrep
  have h2 := hν Ω mΩ P 𝓕 κ _ (fun ω => scaleRep a (ηL ω)) ‹_› hκ hη' (hsa.comp hηm) hrep'
  refine measurableEmbedding_slePathCode.map_injective ?_
  rw [Measure.map_map measurableEmbedding_slePathCode.measurable hsa,
    Measure.map_map (measurableEmbedding_slePathCode.measurable.comp hsa) hηm,
    Measure.map_map measurableEmbedding_slePathCode.measurable hηm]
  exact h2.trans h1.symm

end MatedCRT.FirstPass.Derived
