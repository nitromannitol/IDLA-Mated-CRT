import MatedCRT.FirstPass.Derived.AreaParametrization
import MatedCRT.FirstPass.Derived.CellDiamUniform
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cM.PushArea

/-! # Proper area-parametrized versions of the curve -/

open MeasureTheory Set Filter Topology

namespace MatedCRT.FirstPass.Derived

/-- Every continuous version of the curve in a valid environment is almost surely
proper, surjective and parametrized by the environment's area measure, which is
the pushforward of Lebesgue measure under the curve. -/
theorem MatedCRTEnv.IsValid.ae_proper_area_curveVersion
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η : Ω → C(ℝ, ℂ)}
    (hae : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω) :
    ∀ᵐ ω ∂S.P, IsProperMap (η ω) ∧ Function.Surjective (η ω) ∧
      (∀ a b : ℝ, a ≤ b →
        S.μ ω (η ω '' Icc a b) = ENNReal.ofReal (b - a)) ∧
      S.μ ω = Measure.map (η ω) volume := by
  filter_upwards [ae_mem_properCurveSet hS hae, hS.isAreaParametrized, hae] with ω hp ha heq
  have harea : IsAreaParametrized (S.μ ω) (η ω) := by
    rw [heq]
    exact ha
  have hmass : ∀ a b : ℝ, a ≤ b →
      S.μ ω (η ω '' Icc a b) = ENNReal.ofReal (b - a) := by
    intro a b hab
    rcases hab.eq_or_lt with rfl | hab
    · simpa using measure_image_Icc_self_eq_zero harea a
    · exact harea.2.2.2 a b hab
  exact ⟨isProperMap_iff_tendsto_cocompact.2 ⟨(η ω).continuous, hp.1⟩,
    hp.2, hmass, MatedCRTHarmonic.GMS4cM.eq_map_volume (η ω).continuous hp.2 hmass⟩

/-- A valid environment has a measurable continuous curve version with the
properness, surjectivity and area identities holding on one event of full measure. -/
theorem MatedCRTEnv.IsValid.exists_proper_area_curveVersion
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∃ η : Ω → C(ℝ, ℂ), Measurable η ∧
      (∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω ∧ IsProperMap (η ω) ∧
        Function.Surjective (η ω) ∧
        (∀ a b : ℝ, a ≤ b →
          S.μ ω (η ω '' Icc a b) = ENNReal.ofReal (b - a)) ∧
        S.μ ω = Measure.map (η ω) volume) := by
  obtain ⟨η, hη, hae⟩ := hS.exists_curveVersion
  refine ⟨η, hη, ?_⟩
  filter_upwards [hae, MatedCRTEnv.IsValid.ae_proper_area_curveVersion hS hae] with ω heq hp
  exact ⟨heq, hp⟩

end MatedCRT.FirstPass.Derived
