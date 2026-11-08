import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Tonelli reduction for a fixed-time regularization defect. -/

namespace MatedCRT

open Set MeasureTheory Filter

/-- If each sample has countably many bad shift parameters, and the joint
bad event is measurable, then almost every shift has a null bad event. If a
null bad event for any shift transfers to shift zero, the unshifted event is
null. -/
theorem ae_no_defect_of_countable_shifts
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (E : ℝ → Ω → Prop)
    (hmeas : MeasurableSet {p : Ω × ℝ | E p.2 p.1})
    (hcount : ∀ᵐ ω ∂P, {c : ℝ | E c ω}.Countable)
    (htransfer : ∀ c : ℝ, (∀ᵐ ω ∂P, ¬ E c ω) → ∀ᵐ ω ∂P, ¬ E 0 ω) :
    ∀ᵐ ω ∂P, ¬ E 0 ω := by
  have hsample : ∀ᵐ ω ∂P, ∀ᵐ c ∂(volume : Measure ℝ), ¬ E c ω := by
    filter_upwards [hcount] with ω hω
    exact hω.ae_notMem volume
  have hshifts : ∀ᵐ c ∂(volume : Measure ℝ), ∀ᵐ ω ∂P, ¬ E c ω :=
    (Measure.ae_ae_comm hmeas.compl).mp hsample
  obtain ⟨c, hc⟩ := hshifts.exists
  exact htransfer c hc

/-- A measurable bad event is null at the unshifted field when the law of
the unshifted field is absolutely continuous with respect to each shifted
law and each sample has at most countably many bad shifts. -/
theorem ae_no_defect_of_shifted_law
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [SFinite P] (Y : ℝ → Ω → X) (B : Set X)
    (hB : MeasurableSet B) (hY : ∀ c, AEMeasurable (Y c) P)
    (hmeas : MeasurableSet {p : Ω × ℝ | Y p.2 p.1 ∈ B})
    (hcount : ∀ᵐ ω ∂P, {c : ℝ | Y c ω ∈ B}.Countable)
    (hlaw : ∀ c, Measure.map (Y 0) P ≪ Measure.map (Y c) P) :
    ∀ᵐ ω ∂P, Y 0 ω ∉ B := by
  apply ae_no_defect_of_countable_shifts P (fun c ω => Y c ω ∈ B) hmeas hcount
  intro c hc
  have hc' : ∀ᵐ x ∂Measure.map (Y c) P, x ∉ B :=
    (ae_map_iff (hY c) hB.compl).mpr hc
  have hzero : ∀ᵐ x ∂Measure.map (Y 0) P, x ∉ B := (hlaw c).ae_le hc'
  exact (ae_map_iff (hY 0) hB.compl).mp hzero

end MatedCRT
