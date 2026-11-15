import MatedCRT.FirstPass.Derived.ValidComponentIntervalObservations

/-! # Observable endpoints of a component interval -/

set_option autoImplicit false

open MeasureTheory MeasurableSpace Set
open LatticeProb LatticeProb.CorrelatedBM MatedCRTHarmonic.MatedCRT

namespace MatedCRT

/-- If bounded component interval witnesses exist almost surely, and the visit
code is observable from each half of the contour, segment-observable endpoint
functions themselves witness the component interval almost surely. -/
theorem MatedCRTEnv.IsValid.exists_segment_observable_component_interval
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {a u b : ℝ}
    (hau : a < u) (hub : u < b) (η : Ω → C(ℝ, ℂ))
    (hη : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω)
    (hpast : AELeSigma (MeasurableSpace.comap
      (fun ω (q : {q : ℚ // (q : ℝ) ∈ Icc a b}) =>
        curveComponentVisitCode (Icc a b) (η ω) (η ω u) q.1) inferInstance)
      ((incrementSigma lrCoord (Iic b) b).comap S.bm) S.P)
    (hfuture : AELeSigma (MeasurableSpace.comap
      (fun ω (q : {q : ℚ // (q : ℝ) ∈ Icc a b}) =>
        curveComponentVisitCode (Icc a b) (η ω) (η ω u) q.1) inferInstance)
      ((incrementSigma lrCoord (Ici a) a).comap S.bm) S.P)
    (hcomponent : ∀ᵐ ω ∂S.P, ∃ A B : ℝ,
      a ≤ A ∧ B ≤ b ∧ (η ω) '' Icc A B =
        closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u))) :
    ∃ A B : Path2 → ℝ,
      Measurable[incrementSigma lrCoord (Icc a b) a] A ∧
      Measurable[incrementSigma lrCoord (Icc a b) a] B ∧
      ∀ᵐ ω ∂S.P, a ≤ A (S.bm ω) ∧ B (S.bm ω) ≤ b ∧
        (η ω) '' Icc (A (S.bm ω)) (B (S.bm ω)) =
          closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u)) := by
  classical
  let P : Ω → ℝ → ℝ → Prop := fun ω A B =>
    a ≤ A ∧ B ≤ b ∧ (η ω) '' Icc A B =
      closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u))
  let w : Ω → ℝ × ℝ := fun ω =>
    if h : ∃ A B, P ω A B then ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩
    else (0, 0)
  have hw : ∀ᵐ ω ∂S.P, P ω (w ω).1 (w ω).2 := by
    filter_upwards [hcomponent] with ω hω
    have hex : ∃ A B, P ω A B := hω
    simp only [w, dite_eq_left hex]
    exact Classical.choose_spec (Classical.choose_spec hex)
  obtain ⟨A, B, hA, hB, heq⟩ :=
    hS.exists_segment_observable_component_endpoints_of_closure hau hub η hη
      (fun ω => (w ω).1) (fun ω => (w ω).2) hpast hfuture hw
  refine ⟨A, B, hA, hB, ?_⟩
  filter_upwards [hw, heq] with ω hω he
  simpa only [P, he.1, he.2] using hω

end MatedCRT
