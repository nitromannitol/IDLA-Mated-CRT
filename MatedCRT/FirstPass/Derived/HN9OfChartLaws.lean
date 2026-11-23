import MatedCRT.FirstPass.Derived.HN9OfLocalSpeedRecovery
import MatedCRT.FirstPass.Derived.MedianOfCdf
import MarkovProcess.Killed.Kernel
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Lemma 7.18 from the chart forms of Lemmas 7.20 and 7.21

Berestycki–Gwynne (2020) prove Lemma 7.18 (the time-change constant `c` of the joint limit is deterministic)
from Lemmas 7.20, 7.21 and 7.22. For times `a < u < b` let `U` be the component of the interior of `η([a, b])`
containing `η(u)` and `φ : 𝔻 → U` the conformal map with `φ(0) = η(u)` (normalized at a boundary point), which
extends to a homeomorphism of the closures (Pommerenke (1992), Theorem 2.6). The chart triple is
`(h^D, η^D, P^D_0)`, where `h^D = h ∘ φ + Q log |φ'|` and `P^D_0` is the law of `φ⁻¹ ∘ X̂`, `X̂` sampled from
the limiting law at `η(u)` and stopped at its exit from `U` (their (7.34)).

* Lemma 7.20: almost surely `P^D_0` is the law of Liouville Brownian motion with respect to `h^D` started from `0`
  and stopped upon hitting `∂𝔻`, pre-composed with `t ↦ c t`.
* Lemma 7.21: the chart triples of two disjoint time windows are independent.
* Lemma 7.22 and the proof of Lemma 7.18: `c` is a measurable function of each triple, hence independent of itself.

This file proves the parts of this argument which do not involve the geometry of the windows.

* **The time-change part of Lemma 7.20** (`chartLaw_eq_map_timeScalePath`): stopping a path at its exit from `U`
  and then applying a continuous map `ψ` (here a continuous extension of `φ⁻¹` to `ℂ`) commutes with the time
  change `t ↦ c t` (`chartStopPath_timeScalePath`). Hence if the limiting law at `z` is the time change by `c` of
  the Liouville Brownian law from `z`, then its chart image is the time change by `c` of the chart image of the
  Liouville Brownian law. What remains of Lemma 7.20 is `c`-free: the chart image of the Liouville Brownian law of
  `h` from `η(u)` is the Liouville Brownian law of `h^D` from `0` stopped on `∂𝔻` (Berestycki (2015), Theorem 1.3,
  the coordinate change of Liouville Brownian motion).
* **Lemma 7.22 in the form used by the proof of Lemma 7.18**: `c` is the ratio of the medians of the exit time
  from `𝔻` under the chart Liouville Brownian law and under `P^D_0` (`exitMedianRatio`,
  `coe_eq_medianOf_div_of_map_timeScalePath`), a measurable function of `(h^D, P^D_0)`. The printed proof of
  Lemma 7.22 (mutual singularity of the laws of `(h, X_{c₁ ·})` and `(h, X_{c₂ ·})` for each pair `c₁ ≠ c₂`) does
  not by itself express `c` as a measurable function; the median ratio does.

The remaining literature content is the input `BG20ChartLawInput` (Lemma 7.20 without the time change, that is the
coordinate change of Liouville Brownian motion, and Lemma 7.21). It implies `BG20LocalSpeedRecoveryInput`
(`bg20LocalSpeedRecoveryInput_of_chartLaws`) and hence the premise `hN9` exactly as typed.

## Main statements

* `stopAtExitTime`, `chartStopPath`, `chartLaw`: the path stopped at its exit from `U`, its image under `ψ`, and
  the image law.
* `chartStopPath_timeScalePath`, `measurable_chartStopPath`, `chartLaw_eq_map_timeScalePath`.
* `BG20ChartLawInput`, `bg20LocalSpeedRecoveryInput_of_chartLaws`, `hN9_of_bg20ChartLaws`.
* `randomWalkToLBMStmt_of_markovLimit_bg20ChartLaws`,
  `closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20ChartLaws`,
  `closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20ChartLaws`: Theorem 2.11 and Theorems 1.4 and 1.6 in
  the counted forms with the premises `h1 h2 hN4 h10` and `BG20ChartLawInput`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

section ChartStop

/-- The time change `t ↦ min t τ` which freezes a path at the time `τ` (the identity if `τ = ∞`). -/
noncomputable def exitClamp (τ : ℝ≥0∞) : C(ℝ≥0, ℝ≥0) :=
  if τ = ⊤ then ContinuousMap.id ℝ≥0 else ⟨fun t => min t τ.toNNReal, continuous_id.min continuous_const⟩

theorem exitClamp_apply (τ : ℝ≥0∞) (t : ℝ≥0) :
    exitClamp τ t = if τ = ⊤ then t else min t τ.toNNReal := by
  unfold exitClamp
  split_ifs <;> rfl

/-- The path `f` stopped at its first exit time from `U` (the path `f` itself if it never leaves `U`). -/
noncomputable def stopAtExitTime (U : Set ℂ) (f : ContinuousPath ℂ) : ContinuousPath ℂ :=
  f.comp (exitClamp (ContinuousPath.exitTime U f))

/-- **Stopping at the exit time commutes with a linear time change.** -/
theorem stopAtExitTime_timeScalePath (U : Set ℂ) {c : ℝ≥0} (hc : c ≠ 0) (f : ContinuousPath ℂ) :
    stopAtExitTime U (timeScalePath c f) = timeScalePath c (stopAtExitTime U f) := by
  ext t
  simp only [stopAtExitTime, ContinuousMap.comp_apply, timeScalePath_apply, exitClamp_apply,
    exitTime_timeScalePath U hc f]
  by_cases hτ : ContinuousPath.exitTime U f = ⊤
  · have htop : (⊤ : ℝ≥0∞) / c = ⊤ := ENNReal.top_div_of_ne_top ENNReal.coe_ne_top
    simp only [hτ, htop, ↓reduceIte]
  · have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
    have hτc : ContinuousPath.exitTime U f / c ≠ ⊤ := ENNReal.div_ne_top hτ hc'
    simp only [hτc, hτ, ↓reduceIte]
    rw [ENNReal.toNNReal_div, ENNReal.toNNReal_coe]
    congr 1
    set x := (ContinuousPath.exitTime U f).toNNReal
    have hcx : c * (x / c) = x := by
      rw [mul_comm]
      exact div_mul_cancel₀ x hc
    rcases le_total t (x / c) with h | h
    · rw [min_eq_left h, min_eq_left]
      calc c * t ≤ c * (x / c) := mul_le_mul_of_nonneg_left h zero_le
        _ = x := hcx
    · rw [min_eq_right h, min_eq_right, hcx]
      calc x = c * (x / c) := hcx.symm
        _ ≤ c * t := mul_le_mul_of_nonneg_left h zero_le

/-- Stopping at the exit time from an open set is a Borel map of path space. -/
theorem measurable_stopAtExitTime (U : Set ℂ) (hU : IsOpen U) : Measurable (stopAtExitTime U) := by
  have hτ : Measurable (ContinuousPath.exitTime U : ContinuousPath ℂ → ℝ≥0∞) :=
    ContinuousPath.measurable_exitTime U hU
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hT : Measurable fun f : ContinuousPath ℂ => exitClamp (ContinuousPath.exitTime U f) t := by
    simp only [exitClamp_apply]
    exact Measurable.ite (hτ (measurableSet_singleton ⊤)) measurable_const
      (measurable_const.min (ENNReal.measurable_toNNReal.comp hτ))
  exact (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
    (measurable_id.prodMk hT)

/-- The chart image `ψ ∘ (f stopped at its exit from U)` of a path `f`. -/
noncomputable def chartStopPath (U : Set ℂ) (ψ : C(ℂ, ℂ)) (f : ContinuousPath ℂ) : ContinuousPath ℂ :=
  ψ.comp (stopAtExitTime U f)

/-- The chart image of a path commutes with a linear time change. -/
theorem chartStopPath_timeScalePath (U : Set ℂ) (ψ : C(ℂ, ℂ)) {c : ℝ≥0} (hc : c ≠ 0)
    (f : ContinuousPath ℂ) :
    chartStopPath U ψ (timeScalePath c f) = timeScalePath c (chartStopPath U ψ f) := by
  unfold chartStopPath
  rw [stopAtExitTime_timeScalePath U hc f]
  ext s
  rfl

theorem measurable_chartStopPath (U : Set ℂ) (hU : IsOpen U) (ψ : C(ℂ, ℂ)) :
    Measurable (chartStopPath U ψ) := by
  have hψ : Continuous fun g : ContinuousPath ℂ => ψ.comp g := ContinuousMap.continuous_postcomp ψ
  exact hψ.measurable.comp (measurable_stopAtExitTime U hU)

/-- The chart image of a time-changed law is the time change of the chart image. -/
theorem map_chartStopPath_map_timeScalePath (U : Set ℂ) (hU : IsOpen U) (ψ : C(ℂ, ℂ)) {c : ℝ≥0}
    (hc : c ≠ 0) (μ : Measure (ContinuousPath ℂ)) :
    (μ.map (timeScalePath c)).map (chartStopPath U ψ) =
      (μ.map (chartStopPath U ψ)).map (timeScalePath c) := by
  rw [Measure.map_map (measurable_chartStopPath U hU ψ) (measurable_timeScalePath c),
    Measure.map_map (measurable_timeScalePath c) (measurable_chartStopPath U hU ψ)]
  congr 1
  funext f
  exact chartStopPath_timeScalePath U ψ hc f

/-- The image under `chartStopPath U ψ` of the law at `z` of a family of path laws (for the limiting family and
`ψ` a continuous extension of the inverse chart map, the law `P^D_0` of Berestycki–Gwynne (2020), (7.34)). -/
noncomputable def chartLaw (K : PathLawFamily) (z : ℂ) (U : Set ℂ) (ψ : C(ℂ, ℂ)) :
    Measure (ContinuousPath ℂ) :=
  (K z : Measure (ContinuousPath ℂ)).map (chartStopPath U ψ)

/-- **The time-change part of Berestycki–Gwynne (2020), Lemma 7.20.** If the law at `z` of `K` is the time
change by `c ≠ 0` of the law at `z` of `L`, then the chart image of `K` at `z` is the time change by `c` of the
chart image of `L` at `z`. -/
theorem chartLaw_eq_map_timeScalePath {K L : PathLawFamily} {c : ℝ≥0} (hc : c ≠ 0) {z : ℂ}
    (hKL : K z = LatticeProb.timeScalePathKernel c L z) (U : Set ℂ) (hU : IsOpen U) (ψ : C(ℂ, ℂ)) :
    chartLaw K z U ψ = (chartLaw L z U ψ).map (timeScalePath c) := by
  have h : (K z : Measure (ContinuousPath ℂ)) = (L z : Measure (ContinuousPath ℂ)).map (timeScalePath c) := by
    rw [hKL]
    rfl
  rw [chartLaw, h]
  exact map_chartStopPath_map_timeScalePath U hU ψ hc _

end ChartStop

/-- **Literature input (Berestycki–Gwynne (2020), Lemma 7.20 without the time change, and Lemma 7.21).** In the
setting of the premise `hN9` of `randomWalkToLBMStmt_of_markovLimit_derived` (a valid environment `S`,
measurable versions `η'` and `H` of its curve and field, a measurable `E`, cell sizes `ε n → 0`, and a weak limit
`ν'` of the joint laws of the field coordinates and the interpolated walk laws, which is almost surely a linear
time change of the Liouville Brownian law field), there are a probability space `(Ω₂, P₂)` with a measurable map
`pr` such that `pr_* P₂ = ν'`, and for two windows `i = 0, 1`: points `z i`, open sets `U i`, continuous maps
`ψ i`, chart fields `hD i` with values in a measurable space `F`, and a measurable kernel `K` on `F`, such that

* the chart laws `chartLaw (pr ω₂).2 (z i ω₂) (U i ω₂) (ψ i ω₂)` depend measurably on `ω₂`;
* (Lemma 7.20 without the time change) almost surely the chart image of the Liouville Brownian law of the field
  from `z i` is `K (hD i)`, under which almost every path starts at `0` and leaves the unit disc;
* (Lemma 7.21) the pairs (chart field, chart law) of the two windows are independent.

In Berestycki–Gwynne, `Ω₂` carries the joint subsequential limit `(h, η, P)` and `pr` forgets the curve; for
times `a < u < b < ã < ũ < b̃`, `z 0 = η(u)`, `U 0` is the component of the interior of `η([a, b])` containing
`η(u)`, `ψ 0` is a continuous extension to `ℂ` of the inverse of the conformal map `φ : 𝔻 → U 0` with
`φ(0) = η(u)` (a homeomorphism of the closures by Pommerenke (1992), Theorem 2.6, as `∂U` is a Jordan curve),
`hD 0 = h ∘ φ + Q log |φ'|`, and `K (hD 0)` is the law of the Liouville Brownian motion of `hD 0` from `0` stopped
upon hitting `∂𝔻` (time-changed by the deterministic normalization of `lbmPathLawField`); likewise for the second
window. The identity of the chart image is the coordinate change of Liouville Brownian motion (Berestycki (2015),
Theorem 1.3); the independence is Lemma 7.21, from Duplantier–Miller–Sheffield, Theorem 1.9. Their walk runs at
the raw speed `ε⁻¹`, while `interpWalkLaw` is normalized by the median `m_ε`; along a further subsequence `ε m_ε`
tends to a deterministic positive limit (end of the proof of their Theorem 1.2), and the chart laws for the two
normalizations differ by the corresponding deterministic time change, which preserves the independence. -/
def BG20ChartLawInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
    (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
        (𝓝 (∫ p, f p ∂ν'))) →
    (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
    ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂) (_ : IsProbabilityMeasure P₂)
      (pr : Ω₂ → ((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily)
      (F : Type) (_ : MeasurableSpace F) (K : F → Measure (ContinuousPath ℂ))
      (z : Fin 2 → Ω₂ → ℂ) (U : Fin 2 → Ω₂ → Set ℂ) (ψ : Fin 2 → Ω₂ → C(ℂ, ℂ)) (hD : Fin 2 → Ω₂ → F),
      Measurable pr ∧ P₂.map pr = ν' ∧ Measurable K ∧ (∀ i, Measurable (hD i)) ∧
      (∀ i ω₂, IsOpen (U i ω₂)) ∧
      (∀ i, Measurable fun ω₂ => chartLaw (pr ω₂).2 (z i ω₂) (U i ω₂) (ψ i ω₂)) ∧
      (∀ i, ∀ᵐ ω₂ ∂P₂,
        chartLaw (lbmPathLawField γ (pr ω₂).1.1) (z i ω₂) (U i ω₂) (ψ i ω₂) = K (hD i ω₂)) ∧
      (∀ i, ∀ᵐ ω₂ ∂P₂, ∀ᵐ f ∂K (hD i ω₂),
        f 0 = 0 ∧ ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f ≠ ⊤) ∧
      IndepFun (fun ω₂ => (hD 0 ω₂, chartLaw (pr ω₂).2 (z 0 ω₂) (U 0 ω₂) (ψ 0 ω₂)))
        (fun ω₂ => (hD 1 ω₂, chartLaw (pr ω₂).2 (z 1 ω₂) (U 1 ω₂) (ψ 1 ω₂))) P₂

/-- **Lemma 7.20 and the median form of Lemma 7.22.** Under the chart image of a time change by `c ≠ 0`, with
the identity of the chart image of the Liouville Brownian law and the starting and exit properties of `K`, the
constant `c` is the ratio of the medians of the exit time from the unit disc under `K (hD)` and under the chart
law. -/
theorem coe_eq_exitMedianRatio_chartLaw {F : Type} {K : F → Measure (ContinuousPath ℂ)}
    {γ : ℝ} {p : ((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily} {z : ℂ} {U : Set ℂ} (hU : IsOpen U)
    {ψ : C(ℂ, ℂ)} {g : F} (hb : chartLaw (lbmPathLawField γ p.1.1) z U ψ = K g)
    (hk : ∀ᵐ f ∂K g, f 0 = 0 ∧ ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f ≠ ⊤)
    {c : ℝ≥0} (hc : c ≠ 0) (hcz : p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) :
    (c : ℝ) = exitMedianRatio (Metric.ball (0 : ℂ) 1) K (g, chartLaw p.2 z U ψ) := by
  have hlaw : chartLaw p.2 z U ψ = (K g).map (timeScalePath c) := by
    rw [chartLaw_eq_map_timeScalePath hc hcz U hU ψ, hb]
  have hprob : IsProbabilityMeasure (K g) := by
    rw [← hb]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_chartStopPath U hU ψ).aemeasurable).mpr
      inferInstance
  have h0 : K g {f | ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f = 0} = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hk)
    intro f hf hfp
    have hpos := (ContinuousPath.exitTime_pos_iff _ Metric.isOpen_ball f).2
      (by rw [hfp.1]; exact Metric.mem_ball_self one_pos)
    rw [show ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f = 0 from hf] at hpos
    exact lt_irrefl _ hpos
  have hT : K g {f | ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f = ⊤} = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hk)
    intro f hf hfp
    exact hfp.2 hf
  exact coe_eq_medianOf_div_of_map_timeScalePath (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball hc _ _ hlaw
    (medianOf_exitCdf_pos _ Metric.isOpen_ball _ h0 hT).ne'

/-- The chart input implies `BG20LocalSpeedRecoveryInput`: the two independent random elements are the pairs
(chart field, chart law) of the two windows, and both recoveries are the ratio of exit-time medians
`exitMedianRatio (ball 0 1) K` (`coe_eq_exitMedianRatio_chartLaw`). -/
theorem bg20LocalSpeedRecoveryInput_of_chartLaws {𝒮 : SpaceFillingSLEModel}
    (hChart : BG20ChartLawInput 𝒮) : BG20LocalSpeedRecoveryInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν' hν' hconv hspeed
  obtain ⟨Ω₂, _, P₂, _, pr, F, _, K, z, U, ψ, hD, hpr, hmap, hK, hhD, hU, hlawm, hBer, hKexit, hind⟩ :=
    hChart γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν' hν' hconv hspeed
  let X : Fin 2 → Ω₂ → F × Measure (ContinuousPath ℂ) := fun i ω₂ =>
    (hD i ω₂, chartLaw (pr ω₂).2 (z i ω₂) (U i ω₂) (ψ i ω₂))
  have hX : ∀ i, Measurable (X i) := fun i => (hhD i).prodMk (hlawm i)
  have hrec : ∀ i, ∀ᵐ ω₂ ∂P₂, ∀ c : ℝ≥0, c ≠ 0 →
      (∀ w, (pr ω₂).2 w = LatticeProb.timeScalePathKernel c (lbmPathLawField γ (pr ω₂).1.1) w) →
      (c : ℝ) = exitMedianRatio (Metric.ball (0 : ℂ) 1) K (X i ω₂) := by
    intro i
    filter_upwards [hBer i, hKexit i] with ω₂ hb hk c hc hcz
    exact coe_eq_exitMedianRatio_chartLaw (hU i ω₂) hb hk hc (hcz (z i ω₂))
  refine ⟨Ω₂, inferInstance, P₂, inferInstance, pr, F × Measure (ContinuousPath ℂ),
    F × Measure (ContinuousPath ℂ), inferInstance, inferInstance, X 0, X 1,
    exitMedianRatio (Metric.ball (0 : ℂ) 1) K, exitMedianRatio (Metric.ball (0 : ℂ) 1) K,
    hpr, hmap, hX 0, hX 1, hind, measurable_exitMedianRatio _ Metric.isOpen_ball hK,
    measurable_exitMedianRatio _ Metric.isOpen_ball hK, ?_⟩
  filter_upwards [hrec 0, hrec 1] with ω₂ h0 h1 c hc hcz
  exact ⟨h0 c hc hcz, h1 c hc hcz⟩

/-- **Berestycki–Gwynne (2020), Lemma 7.18, from the chart forms of Lemmas 7.20 and 7.21.** The premise `hN9` of
`randomWalkToLBMStmt_of_markovLimit_derived`, exactly as typed, from `BG20ChartLawInput`
(`bg20LocalSpeedRecoveryInput_of_chartLaws` and `hN9_of_bg20LocalSpeedRecovery`). -/
theorem hN9_of_bg20ChartLaws {𝒮 : SpaceFillingSLEModel} (hChart : BG20ChartLawInput 𝒮) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z :=
  hN9_of_bg20LocalSpeedRecovery (bg20LocalSpeedRecoveryInput_of_chartLaws hChart)

/-- **Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2) with Lemma 7.18 reduced to the chart forms of Lemmas
7.20 and 7.21.** The remaining premises are `h1 h2 hN4 h10` and `BG20ChartLawInput`. -/
theorem randomWalkToLBMStmt_of_markovLimit_bg20ChartLaws {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hChart : BG20ChartLawInput 𝒮) :
    RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_markovLimit_bg20LocalSpeedRecovery h1 h2 hN4 h10
    (bg20LocalSpeedRecoveryInput_of_chartLaws hChart)

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension`, with the premise `hN9`
(Berestycki–Gwynne (2020), Lemma 7.18) of `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`
replaced by `BG20ChartLawInput` (Lemma 7.20 without the time change, and Lemma 7.21); the remaining premises are
`h1 h2 hN4 h10 hChart`. Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20ChartLaws
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hChart : BG20ChartLawInput 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20LocalSpeedRecovery ν h1 h2 hN4 h10
    (bg20LocalSpeedRecoveryInput_of_chartLaws hChart)

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension`, with the premise `hN9`
(Berestycki–Gwynne (2020), Lemma 7.18) of `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`
replaced by `BG20ChartLawInput` (Lemma 7.20 without the time change, and Lemma 7.21); the remaining premises are
`h1 h2 hN4 h10 hChart`. Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20ChartLaws
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hChart : BG20ChartLawInput 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20LocalSpeedRecovery ν h1 h2 hN4 h10
    (bg20LocalSpeedRecoveryInput_of_chartLaws hChart)

end MatedCRT
