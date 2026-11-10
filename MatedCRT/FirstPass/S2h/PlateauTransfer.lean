import MatedCRT.FirstPass.S2h.PlateauNull
import MatedCRT.FirstPass.S2h.CertCode
import MatedCRT.FirstPass.S2h.MeasurableIntegral
import MatedCRT.Proofs.Sec4.Prop42Closure.WholePlaneLQGMeasurable

/-!
# Transfer of the plateau event through equality in law (fp-S2h, z1, round 17)

Route of the scaling step `hscale` of `plateauRadii_zero_of_HB` (`FirstPass/S2h/PlateauNull.lean`), following
CHATGPT-z1-logcert-null.md Sections 3.1-3.2 and 5 and CHATGPT-cone-good-set.md Section 5.1: the plateau event of a random
measure is the event that its moment code lies in a fixed Borel set `E` of codes, almost surely. Equality in law of the
measure and of its dilation then transfers the event. This file proves the abstract transfer and the local finiteness
of the LQG measure; the code-space relation `E` is the open NEW step (not here).
-/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

/-- Equality in law transfers an event described by a Borel set of a common code: if `f` and `g` have the same law and
`ω ∈ A ↔ f ω ∈ E` and `ω ∈ B ↔ g ω ∈ E` almost surely for a measurable `E`, then `P B = P A`. -/
theorem measure_eq_of_ae_iff_mem_of_map_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {f g : Ω → X} (hf : AEMeasurable f P) (hg : AEMeasurable g P) (hlaw : P.map g = P.map f) {E : Set X}
    (hE : MeasurableSet E) {A B : Set Ω} (hA : ∀ᵐ ω ∂P, ω ∈ A ↔ f ω ∈ E) (hB : ∀ᵐ ω ∂P, ω ∈ B ↔ g ω ∈ E) :
    P B = P A := by
  calc P B = P (g ⁻¹' E) := measure_congr (Filter.eventuallyEqSet_iff.2 hB)
    _ = P.map g E := (Measure.map_apply_of_aemeasurable hg hE).symm
    _ = P.map f E := by rw [hlaw]
    _ = P (f ⁻¹' E) := Measure.map_apply_of_aemeasurable hf hE
    _ = P A := (measure_congr (Filter.eventuallyEqSet_iff.2 hA)).symm

/-- The plateau probability is invariant under equality in law of the random measure and of its dilation, once both
plateau events are almost surely given by one measurable set `E` of moment codes (fp-S2h, z1, round 17). This is the
abstract form of the scaling step `hscale` (the code relation is the open NEW input). -/
theorem plateau_prob_eq_of_code_relation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (μ S : Ω → Measure ℂ) (hμ : AEMeasurable μ P) (hS : AEMeasurable S P) (hlaw : P.map S = P.map μ)
    (φs : ℕ → ℂ → ℝ) (hcont : ∀ k, Continuous (φs k)) (E : Set (ℕ → ℝ)) (hE : MeasurableSet E) (r : ℝ)
    (hA : ∀ᵐ ω ∂P, r ∈ plateauRadii (μ ω) ↔ localCode φs (μ ω) ∈ E)
    (hB : ∀ᵐ ω ∂P, r ∈ plateauRadii (S ω) ↔ localCode φs (S ω) ∈ E) :
    P {ω | r ∈ plateauRadii (S ω)} = P {ω | r ∈ plateauRadii (μ ω)} := by
  have hcodeM : Measurable (localCode φs) :=
    Measurable.of_eval fun k => measurable_integral_measure_real (hcont k).measurable
  have hlawC : P.map (fun ω => localCode φs (S ω)) = P.map (fun ω => localCode φs (μ ω)) := by
    calc P.map (fun ω => localCode φs (S ω)) = (P.map S).map (localCode φs) :=
          (AEMeasurable.map_map_of_aemeasurable hcodeM.aemeasurable hS).symm
      _ = (P.map μ).map (localCode φs) := by rw [hlaw]
      _ = P.map (fun ω => localCode φs (μ ω)) :=
          AEMeasurable.map_map_of_aemeasurable hcodeM.aemeasurable hμ
  exact measure_eq_of_ae_iff_mem_of_map_eq (hcodeM.comp_aemeasurable hμ) (hcodeM.comp_aemeasurable hS) hlawC hE hA hB

/-- The LQG measure is almost surely finite on every closed ball about the pole (fp-S2h, z1, round 17): the vague limit
`IsLQGLimit` is a Radon measure (HB `IsLQGLimit.isLocallyFiniteMeasure`, Defs/LQG.lean:55), and closed balls are compact. -/
theorem ae_measure_closedBall_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hlgm : IsLQGMeasureOfField P γ γ hcirc μ) (N : ℕ) :
    ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) (N : ℝ)) < ⊤ := by
  have h : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage γ (hcirc ω)) (μ ω) := hlgm
  filter_upwards [h] with ω hω
  have := hω.isLocallyFiniteMeasure
  exact (isCompact_closedBall _ _).measure_lt_top

/-- The whole-plane LQG measure is a random measure: `AEMeasurable μ P` (fp-S2h, z1, round 18). This is the proved
statement `MatedCRT.aemeasurable_wholePlaneLQGMeasure` (Proofs/Sec4/Prop42Closure/WholePlaneLQGMeasurable.lean:98), so no
external freeze is needed for the measurability of the random measure. -/
theorem aemeasurable_lqgMeasure_of_wholePlane {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hL : IsLQGMeasureOfField P γ γ hcirc μ) : AEMeasurable μ P :=
  aemeasurable_wholePlaneLQGMeasure hGFF hL

end MatedCRT
