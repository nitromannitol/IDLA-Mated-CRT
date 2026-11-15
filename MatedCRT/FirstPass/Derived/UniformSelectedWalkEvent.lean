import MatedCRT.FirstPass.Derived.ConeShiftedWalkLiftCoordinates
import LatticeProb.Bonanno.LQGMetric.Meas.UM

/-! # Measurability of uniform selected-walk events -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- An existential event over marked starting points is null measurable for a finite
law, provided the continuous curve is almost surely proper and surjective. The
shift may depend on the curve and the boundary pair. -/
theorem nullMeasurableSet_exists_shiftedSelectedWalkLaw
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (η : Ω → C(ℝ, ℂ)) (w : Ω → C(ℝ, ℝ × ℝ)) (τ : Ω → ℝ)
    (hη : Measurable η) (hw : Measurable w) (hτ : Measurable τ)
    (hcurve : ∀ᵐ ω ∂P, Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      Function.Surjective (η ω))
    (K : Set ℂ) (hK : MeasurableSet K)
    (B : Set (ℂ × Measure C(ℝ≥0, ℂ))) (hB : MeasurableSet B) :
    NullMeasurableSet {ω | ∃ x ∈ K,
      (x, shiftedSelectedWalkLaw ε m (τ ω) x (η ω) (w ω)) ∈ B} P := by
  obtain ⟨F, hF, hFe⟩ := exists_jointly_measurable_shifted_selected_walk_law hε m
  let E := (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℝ
  let T : Set (E × ℂ) := {p | p.2 ∈ K ∧ (p.2, F ((p.1.1, p.2), p.1.2)) ∈ B}
  have hT : MeasurableSet T := by
    have hf : Measurable (fun p : E × ℂ => F ((p.1.1, p.2), p.1.2)) :=
      hF.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))
    exact (hK.preimage measurable_snd).inter (hB.preimage (measurable_snd.prodMk hf))
  have hu : LQGMetric.UMeasurableSet {e : E | ∃ x, (e, x) ∈ T} :=
    LQGMetric.UMeasurableSet.setOf_exists hT
  have hm : Measurable (fun ω => ((η ω, w ω), τ ω)) := (hη.prodMk hw).prodMk hτ
  have hp := hu.nullMeasurableSet_preimage hm.aemeasurable (P := P)
  apply hp.congr
  filter_upwards [hcurve] with ω hω
  apply propext
  simp only [mem_preimage, mem_ofPred_eq, T]
  constructor
  · rintro ⟨x, hx, hxb⟩
    refine ⟨x, hx, ?_⟩
    simpa only [shiftedSelectedWalkLaw, hFe (η ω) (w ω) x (τ ω) hω.1 hω.2] using hxb
  · rintro ⟨x, hx, hxb⟩
    refine ⟨x, hx, ?_⟩
    simpa only [shiftedSelectedWalkLaw, hFe (η ω) (w ω) x (τ ω) hω.1 hω.2] using hxb

end MatedCRT
