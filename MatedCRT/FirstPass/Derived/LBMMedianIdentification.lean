import MatedCRT.FirstPass.Derived.LQGApproxPathKernel
import MatedCRT.FirstPass.Derived.ExitTimeScaling
import MatedCRT.FirstPass.Derived.FieldCoordinateCircleAverages
import MatedCRT.FirstPass.Derived.AnnealedLawConvergence

/-!
# The median of the annealed Liouville Brownian exit time through a field of path laws

Let `q` be a law on the coordinate space `LQGMetric.CoordJ → ℝ` of whole-plane distributions and let
`Λ : (LQGMetric.CoordJ → ℝ) → C(ℂ, 𝒫(C(ℝ≥0, ℂ)))` be a field of path laws. Under the annealed law
`q(dx) Λ(x)(0)(dp)` of the origin path, let `T` be the exit time of `p` from `B_{1/2}`. The lower median of `T`,

  `lawFieldExitMedian q Λ = medianOf (s ↦ ∫ Λ(x)(0){p : T(p) ≤ s} q(dx))`,

is defined for every such pair.

* `MatedCRTEnv.IsValid.m₀_eq_lawFieldExitMedian`: in a valid mated-CRT environment `S` with a measurable version
  `H` of its field, if almost surely `Λ(H)(0)` is the law of the Liouville Brownian motion path
  `t ↦ B_{F⁻¹(t)}` from `0` (`planarBrownianPathLaw 0 (lbmContinuousPath F)`, `F` the LQG clock of `S`), then
  `S.m₀ = lawFieldExitMedian q Λ` for the field law `q = (pairJ ⊤ ∘ H)_* S.P`. Indeed the exit time of `B_{1/2}` by
  the time-changed path is the Liouville Brownian exit time whenever `F(B)` is a time-change clock, which holds
  for almost every Brownian path `B`.
* `MatedCRTEnv.IsValid.map_pairJ_eq`: the field law `(pairJ ⊤ ∘ H)_* S.P` is the same for all valid environments
  at the same `γ` (the law of the `γ`-quantum cone, `Sec1.IsQuantumCone.distribution_law_eq`).
* `MatedCRTEnv.IsValid.m₀_eq_lawFieldExitMedian_of_isValid`: hence `S.m₀` is `lawFieldExitMedian q_γ Λ` for the
  field law `q_γ` of any other valid environment at the same `γ`.

The time-changed path law enters through an existential over the almost everywhere measurability of
`lbmContinuousPath F` (a proposition, so the value of `planarBrownianPathLaw` does not depend on the proof).

Terminology: positive continuous additive functional (the LQG clock `F`), its right-continuous inverse, and the
time change `B_{F⁻¹(t)}` of planar Brownian motion (Garban–Rhodes–Vargas, *Liouville Brownian motion*,
Definition 2.17; Berestycki, *Diffusion in planar Liouville quantum gravity*, Section 2); the `γ`-quantum cone
(Duplantier–Miller–Sheffield (2014), Definition 4.10).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The lower median of the exit time from `B_{1/2}` of the origin path under the annealed law
`q(dx) Λ(x)(0)(dp)` of a field of path laws `Λ` with field law `q`. -/
noncomputable def lawFieldExitMedian (q : Measure (LQGMetric.CoordJ → ℝ))
    (Λ : (LQGMetric.CoordJ → ℝ) → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) : ℝ :=
  medianOf fun s =>
    ∫⁻ x, MatedCRT.exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (Λ x 0 : Measure (ContinuousPath ℂ)) s ∂q

/-- The exit-time distribution function of the origin value of a measurable field of path laws is a measurable
function of the field coordinates. -/
theorem measurable_exitCdf_lawField
    {Λ : (LQGMetric.CoordJ → ℝ) → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛm : Measurable Λ) (s : ℝ) :
    Measurable fun x =>
      MatedCRT.exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (Λ x 0 : Measure (ContinuousPath ℂ)) s := by
  have hK : Measurable fun x : LQGMetric.CoordJ → ℝ => (Λ x 0 : Measure (ContinuousPath ℂ)) :=
    (FirstPass.Derived.measurable_originPathLawKernel (Data := LQGMetric.CoordJ → ℝ)).comp
      (measurable_id.prodMk hΛm)
  exact (measurable_exitCdf (Metric.ball (0 : ℂ) (1 / 2)) Metric.isOpen_ball s).comp hK

/-- **The median `m₀` through a field of Liouville Brownian path laws.** Let `S` be a valid mated-CRT environment
and `H` a measurable version of its field. If `Λ` is a measurable field of path laws whose value at `0`, at the
coordinates `pairJ ⊤ (H ω)` of the field, is almost surely the law of the Liouville Brownian motion path
`t ↦ B_{F⁻¹(t)}` from `0` for the LQG clock `F = S.clock ω`, then `m₀` is the lower median of the exit time from
`B_{1/2}` under the annealed law `q(dx) Λ(x)(0)(dp)`, `q` the law of the field coordinates. -/
theorem MatedCRTEnv.IsValid.m₀_eq_lawFieldExitMedian {Ω : Type} [MeasurableSpace Ω]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    {Λ : (LQGMetric.CoordJ → ℝ) → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ ω ∂S.P, ∃ hg : AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion 0),
      Λ (LQGMetric.pairJ ⊤ (H ω)) 0 = planarBrownianPathLaw 0 (lbmContinuousPath (S.clock ω)) hg) :
    S.m₀ = lawFieldExitMedian (S.P.map fun ω => LQGMetric.pairJ ⊤ (H ω)) Λ := by
  have hq : Measurable fun ω => LQGMetric.pairJ ⊤ (H ω) := measurable_pairJ_top.comp hH
  unfold MatedCRTEnv.m₀ lawFieldExitMedian
  congr 1
  funext s
  rw [lintegral_map (measurable_exitCdf_lawField hΛm s) hq]
  refine lintegral_congr_ae ?_
  filter_upwards [hΛ, hS.isLQGClock] with ω hω hclk
  obtain ⟨hg, hΛω⟩ := hω
  have hE : MeasurableSet {g : ContinuousPath ℂ |
      ContinuousPath.exitTime (Metric.ball (0 : ℂ) (1 / 2)) g ≤ ENNReal.ofReal s} :=
    measurableSet_le (ContinuousPath.measurable_exitTime _ Metric.isOpen_ball) measurable_const
  show _ = MatedCRT.exitCdf (Metric.ball (0 : ℂ) (1 / 2))
    (Λ (LQGMetric.pairJ ⊤ (H ω)) 0 : Measure (ContinuousPath ℂ)) s
  rw [hΛω]
  show _ = Measure.map (lbmContinuousPath (S.clock ω)) (planarBrownianMotion 0)
    {g : ContinuousPath ℂ | ContinuousPath.exitTime (Metric.ball (0 : ℂ) (1 / 2)) g ≤ ENNReal.ofReal s}
  rw [Measure.map_apply_of_aemeasurable hg hE]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [(hclk 0).2] with b hb
  show lbmExitTime (S.clock ω) (Metric.ball (0 : ℂ) (1 / 2)) b ≤ ENNReal.ofReal s ↔
    ContinuousPath.exitTime (Metric.ball (0 : ℂ) (1 / 2)) (lbmContinuousPath (S.clock ω) b) ≤ ENNReal.ofReal s
  rw [lbmContinuousPath_of_isTimeChangeClock hb]
  exact Iff.rfl

/-- **The field law does not depend on the environment.** For two valid mated-CRT environments at the same `γ`
(on any probability spaces) with measurable versions `H₁`, `H₂` of their fields, the laws of the field coordinates
`pairJ ⊤ ∘ Hᵢ` coincide: both are the coordinate law of the `γ`-quantum cone. -/
theorem MatedCRTEnv.IsValid.map_pairJ_eq {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {𝒮₁ 𝒮₂ : SpaceFillingSLEModel} {γ : ℝ} {S₁ : MatedCRTEnv Ω₁} {S₂ : MatedCRTEnv Ω₂}
    (hS₁ : S₁.IsValid 𝒮₁ γ) (hS₂ : S₂.IsValid 𝒮₂ γ)
    {H₁ : Ω₁ → LQGMetric.DistC} {H₂ : Ω₂ → LQGMetric.DistC} (hH₁ : Measurable H₁) (hH₂ : Measurable H₂)
    (hrep₁ : ∀ᵐ ω ∂S₁.P, ∀ φ : LQGMetric.TestC, S₁.hC ω φ = H₁ ω φ)
    (hrep₂ : ∀ᵐ ω ∂S₂.P, ∀ φ : LQGMetric.TestC, S₂.hC ω φ = H₂ ω φ) :
    S₁.P.map (fun ω => LQGMetric.pairJ ⊤ (H₁ ω)) = S₂.P.map (fun ω => LQGMetric.pairJ ⊤ (H₂ ω)) := by
  let : IsProbabilityMeasure S₁.P := hS₁.isProbabilityMeasure
  let : IsProbabilityMeasure S₂.P := hS₂.isProbabilityMeasure
  have h : S₁.P.map H₁ = S₂.P.map H₂ :=
    Sec1.IsQuantumCone.distribution_law_eq hS₁.isQuantumCone hS₂.isQuantumCone hrep₁ hrep₂
  calc S₁.P.map (fun ω => LQGMetric.pairJ ⊤ (H₁ ω))
      = (S₁.P.map H₁).map (LQGMetric.pairJ ⊤) := (Measure.map_map measurable_pairJ_top hH₁).symm
    _ = (S₂.P.map H₂).map (LQGMetric.pairJ ⊤) := by rw [h]
    _ = S₂.P.map (fun ω => LQGMetric.pairJ ⊤ (H₂ ω)) := Measure.map_map measurable_pairJ_top hH₂

/-- **`m₀` is the median of a law that does not depend on the environment.** If `Λ` identifies the Liouville
Brownian path law from `0` in the valid environment `S₁` (as in `MatedCRTEnv.IsValid.m₀_eq_lawFieldExitMedian`),
then `S₁.m₀ = lawFieldExitMedian q Λ` for the field law `q` of any valid environment `S₂` at the same `γ`. -/
theorem MatedCRTEnv.IsValid.m₀_eq_lawFieldExitMedian_of_isValid {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {𝒮₁ 𝒮₂ : SpaceFillingSLEModel} {γ : ℝ} {S₁ : MatedCRTEnv Ω₁} {S₂ : MatedCRTEnv Ω₂}
    (hS₁ : S₁.IsValid 𝒮₁ γ) (hS₂ : S₂.IsValid 𝒮₂ γ)
    {H₁ : Ω₁ → LQGMetric.DistC} {H₂ : Ω₂ → LQGMetric.DistC} (hH₁ : Measurable H₁) (hH₂ : Measurable H₂)
    (hrep₁ : ∀ᵐ ω ∂S₁.P, ∀ φ : LQGMetric.TestC, S₁.hC ω φ = H₁ ω φ)
    (hrep₂ : ∀ᵐ ω ∂S₂.P, ∀ φ : LQGMetric.TestC, S₂.hC ω φ = H₂ ω φ)
    {Λ : (LQGMetric.CoordJ → ℝ) → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ ω ∂S₁.P, ∃ hg : AEMeasurable (lbmContinuousPath (S₁.clock ω)) (planarBrownianMotion 0),
      Λ (LQGMetric.pairJ ⊤ (H₁ ω)) 0 = planarBrownianPathLaw 0 (lbmContinuousPath (S₁.clock ω)) hg) :
    S₁.m₀ = lawFieldExitMedian (S₂.P.map fun ω => LQGMetric.pairJ ⊤ (H₂ ω)) Λ := by
  rw [hS₁.m₀_eq_lawFieldExitMedian hH₁ hΛm hΛ, hS₁.map_pairJ_eq hS₂ hH₁ hH₂ hrep₁ hrep₂]

end MatedCRT
