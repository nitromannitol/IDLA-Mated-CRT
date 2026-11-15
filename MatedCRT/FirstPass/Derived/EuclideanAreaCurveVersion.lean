import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import LatticeProb.Topology.ReparamDistanceIsometry

/-! # Euclidean coordinates for an area-parametrized curve -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace MatedCRT.FirstPass.Derived

/-- A valid environment has a continuous curve version whose image in Euclidean
coordinates is parametrized by the pushforward of its area measure. -/
theorem MatedCRTEnv.IsValid.exists_euclidean_area_curveVersion
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∃ η : Ω → C(ℝ, ℂ), Measurable η ∧
      ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω ∧
        ∀ a b : ℝ, a ≤ b →
          (Measure.map Complex.orthonormalBasisOneI.repr (S.μ ω))
              ((Complex.orthonormalBasisOneI.repr ∘ η ω) '' Icc a b) =
            ENNReal.ofReal (b - a) := by
  obtain ⟨η, hη, hae⟩ := MatedCRTEnv.IsValid.exists_proper_area_curveVersion hS
  refine ⟨η, hη, ?_⟩
  filter_upwards [hae] with ω hω
  refine ⟨hω.1, ?_⟩
  intro a b hab
  have hc : IsCompact (η ω '' Icc a b) := isCompact_Icc.image (η ω).continuous
  have he : Continuous Complex.orthonormalBasisOneI.repr :=
    Complex.orthonormalBasisOneI.repr.continuous
  have hs : MeasurableSet (Complex.orthonormalBasisOneI.repr '' (η ω '' Icc a b)) :=
    (hc.image he).measurableSet
  rw [Set.image_comp, Measure.map_apply he.measurable hs,
    Complex.orthonormalBasisOneI.repr.injective.preimage_image]
  exact hω.2.2.2.1 a b hab

end MatedCRT.FirstPass.Derived
end
