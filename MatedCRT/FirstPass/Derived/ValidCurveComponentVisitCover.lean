import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import LatticeProb.Topology.AreaCurveComponentVisitCover

/-! # Component interval covers of valid curves -/

open MeasureTheory Set

namespace MatedCRT.FirstPass.Derived

/-- In a valid environment, component interval witnesses covering a segment's
interior also cover almost every time in that segment. The exceptional set of
times may depend on the segment and on the witness family. -/
theorem MatedCRTEnv.IsValid.ae_component_intervals_cover_visits
    {Ω ι : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ s t : ℝ, s < t → ∀ (x : ι → ℂ) (a b : ι → ℝ) (A : Set ι),
      (∀ i ∈ A, a i < b i) →
      (∀ i ∈ A, S.η ω '' Icc (a i) (b i) =
        closure (connectedComponentIn (interior (S.η ω '' Icc s t)) (x i))) →
      (∀ z ∈ interior (S.η ω '' Icc s t), ∃ i ∈ A,
        z ∈ connectedComponentIn (interior (S.η ω '' Icc s t)) (x i)) →
      ∀ᵐ u ∂volume, u ∈ Icc s t → ∃ i ∈ A, u ∈ Ioo (a i) (b i) := by
  obtain ⟨η, _, hη⟩ := MatedCRTEnv.IsValid.exists_proper_area_curveVersion hS
  filter_upwards [hη] with ω hω
  rcases hω with ⟨heq, hp, hs, hm, hmap⟩
  intro s t hst x a b A hab himage hcover
  apply LatticeProb.ae_mem_component_intervals_of_proper_area_curve
    (η ω) (S.μ ω) hp hs hmap.symm (fun a b hab => hm a b hab.le) hst x a b A hab
  · simpa only [heq] using himage
  · simpa only [heq] using hcover

end MatedCRT.FirstPass.Derived
