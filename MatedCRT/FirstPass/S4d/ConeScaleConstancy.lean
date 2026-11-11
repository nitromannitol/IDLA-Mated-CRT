import MatedCRT.FirstPass.S4d.RescaleGap

/-!
# Constancy of the strict-gap probability under cone scaling (FIRST PASS, S4d)

Probabilistic part of the fixed-time union `Λ_t = ⋃_{0<s<t} Λ_s` a.s. (`StrictGapFixedTimeUnionStep`). For a cone family `Λ` and `t > 0`, `E_t = {Λ_t ≠ ⋃_{0<s<t} Λ_s}`.

Two explicit named steps (see docs/campaign/COUNTED.md):
* `ConeGlobalFamilyPairAEMeasurableStep` (B2): the pair (circle averages, global family process) is
  a.e. measurable.
* `ConeRescaledPairAEMeasurableStep` (B2R): the rescaled pair of Lemma 2.6 is a.e. measurable.
  It is NOT a consequence of the law equality: in this Mathlib `Measure.map f μ` for a non-a.e.-measurable `f` is a
  Dirac mass (`Measure.map_of_not_aemeasurable_of_ne_zero`), not `0`, so the law equality in `ConeScaleInvarianceStmt`
  does not by itself give measurability of the rescaled pair. Frozen `FrozenConeScalingLaw` gives only the
  measurability of `R_b` and of the measures, not of the pair.

With these, the law invariance of Lemma 2.6 (`ConeScaleInvarianceStmt`, at the level of the pair) makes `P(E_t)`
invariant under `t ↦ b t`, `b > 0`. The random radius `R_b = coneScaleRadius γ (hcirc ω) b` is positive almost surely
(hypothesis `hpos`; from `FrozenConeScalingLaw`, see `FixedTimeUnion.lean`).
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT

/-- **B2, explicit named step (see docs/campaign/COUNTED.md).** For every cone field and every family `Λ` that is a.s. a cone harmonic
ball family, the pair `(circle averages, global family process)` is a.e. measurable. Quantified as the
`ConeScaleInvarianceStmt` (Lemma 2.6) hypotheses. -/
def ConeGlobalFamilyPairAEMeasurableStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) →
    AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P

/-- **B2R, explicit named step (see docs/campaign/COUNTED.md).** The rescaled pair of Lemma 2.6 (random radius `R_b`, `b > 0`) is a.e.
measurable; the law equality of `ConeScaleInvarianceStmt` presupposes this (`P.map` of a random element). -/
def ConeRescaledPairAEMeasurableStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) →
  ∀ b : ℝ, 0 < b →
    AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
      globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b))) P

/-- Scaling invariance of the strict-gap probability: `P(E_t) = P(E_{b t})` for `t, b > 0`, given the a.e.
measurability of the pair and of its rescaling, the law equality of Lemma 2.6 for each `b`, and `R_b > 0` a.s. -/
theorem strictGapEvent_scale {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {Λ : Ω → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hG : AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P)
    (hG' : ∀ b : ℝ, 0 < b → AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b), globalFamilyProcess (rescaledFamily (Λ ω)
      (coneScaleRadius γ (hcirc ω) b) b))) P)
    (hlaw : ∀ b : ℝ, 0 < b →
      P.map (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) =
        P.map (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
          globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b))))
    (hpos : ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b)
    {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    P {ω | Λ ω t ≠ ⋃ u ∈ Ioo (0 : ℝ) t, Λ ω u} =
      P {ω | Λ ω (b * t) ≠ ⋃ u ∈ Ioo (0 : ℝ) (b * t), Λ ω u} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hSm : MeasurableSet {q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop) | ProxyJumpPred D t q.2} :=
    measurable_snd (measurableSet_proxyJumpPred hDc t)
  have e1 : P {ω | Λ ω t ≠ ⋃ u ∈ Ioo (0 : ℝ) t, Λ ω u} =
      P ((fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) ⁻¹'
        {q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop) | ProxyJumpPred D t q.2}) := by
    apply measure_congr
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hΛ] with ω hω
    exact strictGap_iff_proxyJump (goodFamily_of_isConeHarmonicBallFamily hω) hDd ht
  have e2 := (Measure.map_apply_of_aemeasurable hG hSm).symm
  have e4 : (P.map (fun ω => (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b), globalFamilyProcess (rescaledFamily (Λ ω)
      (coneScaleRadius γ (hcirc ω) b) b)))) {q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop) |
        ProxyJumpPred D t q.2} = P ((fun ω => (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b), globalFamilyProcess (rescaledFamily (Λ ω)
      (coneScaleRadius γ (hcirc ω) b) b))) ⁻¹' {q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop) |
        ProxyJumpPred D t q.2}) :=
    Measure.map_apply_of_aemeasurable (hG' b hb) hSm
  have e5 : P ((fun ω => (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b), globalFamilyProcess (rescaledFamily (Λ ω)
      (coneScaleRadius γ (hcirc ω) b) b))) ⁻¹' {q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop) |
        ProxyJumpPred D t q.2}) = P {ω | Λ ω (b * t) ≠ ⋃ u ∈ Ioo (0 : ℝ) (b * t), Λ ω u} := by
    apply measure_congr
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hΛ, hpos b hb] with ω hω hR
    show ProxyJumpPred D t (globalFamilyProcess (rescaledFamily (Λ ω)
      (coneScaleRadius γ (hcirc ω) b) b)) ↔ Λ ω (b * t) ≠ ⋃ u ∈ Ioo (0 : ℝ) (b * t), Λ ω u
    rw [← strictGap_iff_proxyJump (goodFamily_rescaledFamily (goodFamily_of_isConeHarmonicBallFamily hω)
      hR.ne' hb) hDd ht, rescaled_strictGap_iff hR.ne' hb]
  rw [e1, e2, hlaw b hb, e4, e5]

/-- Constancy in the time variable: `t ↦ P(E_t)` is constant on `(0, ∞)`. -/
theorem strictGapEvent_const {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {Λ : Ω → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hG : AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P)
    (hG' : ∀ b : ℝ, 0 < b → AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b), globalFamilyProcess (rescaledFamily (Λ ω)
      (coneScaleRadius γ (hcirc ω) b) b))) P)
    (hlaw : ∀ b : ℝ, 0 < b →
      P.map (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) =
        P.map (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
          globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b))))
    (hpos : ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    P {ω | Λ ω s ≠ ⋃ u ∈ Ioo (0 : ℝ) s, Λ ω u} =
      P {ω | Λ ω t ≠ ⋃ u ∈ Ioo (0 : ℝ) t, Λ ω u} := by
  have h := strictGapEvent_scale hΛ hG hG' hlaw hpos (b := t / s) (t := s) (div_pos ht hs) hs
  rwa [div_mul_cancel₀ t hs.ne'] at h

end MatedCRT
