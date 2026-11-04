import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuousFieldMeasurable
import Mathlib.Topology.Sequences

/-! # Measurability from dense evaluations -/

namespace MatedCRT

open Set Filter MeasureTheory Topology

/-- Almost sure continuity extends almost-everywhere measurability from a
dense set to every point in the spatial domain. -/
theorem aemeasurable_of_ae_continuousOn_of_dense
    {Ω X : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [TopologicalSpace X] [FrechetUrysohnSpace X]
    (U D : Set X) (hDU : D ⊆ U) (hdense : U ⊆ closure D)
    (f : Ω → X → ℝ)
    (hf : ∀ x ∈ D, AEMeasurable (fun ω => f ω x) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (f ω) U) :
    ∀ x ∈ U, AEMeasurable (fun ω => f ω x) P := by
  intro x hx
  obtain ⟨a, haD, ha⟩ := mem_closure_iff_seq_limit.mp (hdense hx)
  apply aemeasurable_of_tendsto_metrizable_ae atTop (f := fun n ω => f ω (a n))
  · exact fun n => hf (a n) (haD n)
  · filter_upwards [hc] with ω hω
    exact (hω x hx).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨ha, Filter.Eventually.of_forall (fun n => hDU (haD n))⟩)

open Classical in
/-- The dense-evaluation reduction also applies after restricting a random
field to an event on which its sample paths are continuous. -/
theorem aemeasurable_on_event_of_ae_continuousOn_of_dense
    {Ω X : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [TopologicalSpace X] [FrechetUrysohnSpace X]
    (U D : Set X) (hDU : D ⊆ U) (hdense : U ⊆ closure D)
    (E : Set Ω) (f : Ω → X → ℝ)
    (hf : ∀ x ∈ D, AEMeasurable (fun ω => if ω ∈ E then f ω x else 0) P)
    (hc : ∀ᵐ ω ∂P, ω ∈ E → ContinuousOn (f ω) U) :
    ∀ x ∈ U, AEMeasurable (fun ω => if ω ∈ E then f ω x else 0) P := by
  classical
  apply aemeasurable_of_ae_continuousOn_of_dense P U D hDU hdense
    (fun ω x => if ω ∈ E then f ω x else 0) hf
  filter_upwards [hc] with ω hω
  by_cases hE : ω ∈ E
  · simpa [hE] using hω hE
  · simpa [hE] using (continuousOn_const : ContinuousOn (fun _ : X => (0 : ℝ)) U)

end MatedCRT
