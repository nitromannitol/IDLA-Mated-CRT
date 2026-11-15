import MatedCRT.FirstPass.Derived.UniformSelectedWalkEvent
import MatedCRT.FirstPass.Derived.JointMeshShiftedSelectedWalk

/-! # Uniform selected-walk events at a random positive mesh -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- An existential selected-walk event is null measurable when the positive
mesh and the shift are measurable functions of the sample. -/
theorem nullMeasurableSet_exists_randomMesh_shiftedSelectedWalkLaw
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ε : Ω → {r : ℝ // 0 < r}) (m : ℝ≥0)
    (η : Ω → C(ℝ, ℂ)) (w : Ω → C(ℝ, ℝ × ℝ)) (τ : Ω → ℝ)
    (hε : Measurable ε) (hη : Measurable η) (hw : Measurable w) (hτ : Measurable τ)
    (hcurve : ∀ᵐ ω ∂P, Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      Function.Surjective (η ω))
    (K : Set ℂ) (hK : MeasurableSet K)
    (B : Set (ℂ × Measure C(ℝ≥0, ℂ))) (hB : MeasurableSet B) :
    NullMeasurableSet {ω | ∃ x ∈ K,
      (x, shiftedSelectedWalkLaw (ε ω).1 m (τ ω) x (η ω) (w ω)) ∈ B} P := by
  let : PolishSpace {r : ℝ // 0 < r} := (isOpen_Ioi : IsOpen (Ioi (0 : ℝ))).polishSpace
  obtain ⟨F, hF, hFe⟩ := exists_measurable_jointMesh_shifted_selected_walk_law m
  let E := ({r : ℝ // 0 < r} × (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ))) × ℝ
  let T : Set (E × ℂ) :=
    {p | p.2 ∈ K ∧ (p.2, F ((p.1.1.1, (p.1.1.2, p.2)), p.1.2)) ∈ B}
  have hT : MeasurableSet T := by
    have hf : Measurable (fun p : E × ℂ => F ((p.1.1.1, (p.1.1.2, p.2)), p.1.2)) :=
      hF.comp (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)).prodMk
        (measurable_snd.comp measurable_fst))
    exact (hK.preimage measurable_snd).inter (hB.preimage (measurable_snd.prodMk hf))
  have hu : LQGMetric.UMeasurableSet {e : E | ∃ x, (e, x) ∈ T} :=
    LQGMetric.UMeasurableSet.setOf_exists hT
  have hm : Measurable (fun ω => ((ε ω, (η ω, w ω)), τ ω)) :=
    (hε.prodMk (hη.prodMk hw)).prodMk hτ
  have hp := hu.nullMeasurableSet_preimage hm.aemeasurable (P := P)
  apply hp.congr
  filter_upwards [hcurve] with ω hω
  apply propext
  simp only [mem_preimage, mem_ofPred_eq, T]
  constructor
  · rintro ⟨x, hx, hxb⟩
    refine ⟨x, hx, ?_⟩
    simpa only [shiftedSelectedWalkLaw, hFe (ε ω) (η ω) (w ω) x (τ ω) hω.1 hω.2] using hxb
  · rintro ⟨x, hx, hxb⟩
    refine ⟨x, hx, ?_⟩
    simpa only [shiftedSelectedWalkLaw, hFe (ε ω) (η ω) (w ω) x (τ ω) hω.1 hω.2] using hxb

end MatedCRT
