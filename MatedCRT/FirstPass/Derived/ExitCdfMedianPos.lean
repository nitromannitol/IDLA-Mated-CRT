import MatedCRT.FirstPass.Derived.ExitTimeScaling
import MatedCRT.Defs.Notation

/-!
# Positivity of the median of an exit-time distribution function

Let `μ` be a probability measure on continuous paths and `U` an open set.  If the exit time from `U` is
almost surely positive and almost surely finite, then the distribution function
`x ↦ μ {exit time ≤ x}` decreases to `0` as `x ↓ 0` and increases to `1` as `x → ∞`, so its median
`medianOf (exitCdf U μ) = inf {m ≥ 0 : μ {exit time ≤ m} ≥ 1/2}` is strictly positive (BG20, proof of
Lemma 7.18: the median of the exit time recovers the constant of a time change).

* `MatedCRT.tendsto_exitCdf_atTop_one`: `exitCdf U μ x → 1` as `x → ∞` when the exit time is a.s. finite.
* `MatedCRT.exists_exitCdf_lt`: when the exit time is a.s. positive, `exitCdf U μ δ < ε` for some `δ > 0`.
* `MatedCRT.medianOf_exitCdf_pos`: the median of the exit-time distribution function is positive.
-/

open MeasureTheory MarkovProcess Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]

/-- If the exit time from the open set `U` is almost surely finite, the exit-time distribution function
tends to `1` at `∞`. -/
theorem tendsto_exitCdf_atTop_one (U : Set α) (hU : IsOpen U) (μ : Measure (ContinuousPath α))
    [IsProbabilityMeasure μ] (hT : μ {f | ContinuousPath.exitTime U f = ⊤} = 0) :
    Tendsto (exitCdf U μ) atTop (𝓝 1) := by
  have hmono : Monotone fun x : ℝ =>
      {f : ContinuousPath α | ContinuousPath.exitTime U f ≤ ENNReal.ofReal x} :=
    fun x y hxy f hf => hf.trans (ENNReal.ofReal_le_ofReal hxy)
  have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
  have hUnion : (⋃ x : ℝ, {f : ContinuousPath α | ContinuousPath.exitTime U f ≤ ENNReal.ofReal x}) =
      {f : ContinuousPath α | ContinuousPath.exitTime U f = ⊤}ᶜ := by
    ext f
    constructor
    · intro hf hfT
      obtain ⟨x, hx⟩ := mem_iUnion.1 hf
      have hx' : ContinuousPath.exitTime U f ≤ ENNReal.ofReal x := hx
      have hfT' : ContinuousPath.exitTime U f = ⊤ := hfT
      rw [hfT'] at hx'
      exact ENNReal.ofReal_ne_top (top_le_iff.1 hx')
    · intro hf
      have hf' : ContinuousPath.exitTime U f ≠ ⊤ := hf
      refine mem_iUnion.2 ⟨(ContinuousPath.exitTime U f).toReal, ?_⟩
      show ContinuousPath.exitTime U f ≤ ENNReal.ofReal (ContinuousPath.exitTime U f).toReal
      rw [ENNReal.ofReal_toReal hf']
  have hmeas : MeasurableSet {f : ContinuousPath α | ContinuousPath.exitTime U f = ⊤} :=
    (ContinuousPath.measurable_exitTime U hU) (measurableSet_singleton ⊤)
  rw [hUnion, prob_compl_eq_one_sub hmeas, hT, tsub_zero] at h
  exact h

/-- If the exit time from the open set `U` is almost surely positive, the exit-time distribution
function is smaller than any `ε > 0` on some interval `[0, δ]`, `δ > 0`. -/
theorem exists_exitCdf_lt (U : Set α) (hU : IsOpen U) (μ : Measure (ContinuousPath α))
    [IsFiniteMeasure μ] (h0 : μ {f | ContinuousPath.exitTime U f = 0} = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ exitCdf U μ δ < ε := by
  have hanti : Antitone fun n : ℕ =>
      {f : ContinuousPath α | ContinuousPath.exitTime U f ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))} := by
    intro m n hmn f hf
    refine hf.trans (ENNReal.ofReal_le_ofReal ?_)
    exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hnull : ∀ n : ℕ, NullMeasurableSet
      {f : ContinuousPath α | ContinuousPath.exitTime U f ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))} μ :=
    fun n => (measurableSet_le (ContinuousPath.measurable_exitTime U hU) measurable_const).nullMeasurableSet
  have h := tendsto_measure_iInter_atTop hnull hanti ⟨0, measure_ne_top μ _⟩
  have hInter : μ (⋂ n : ℕ, {f : ContinuousPath α |
      ContinuousPath.exitTime U f ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))}) = 0 := by
    refine measure_mono_null (fun f hf => ?_) h0
    have hf' : ∀ n : ℕ, ContinuousPath.exitTime U f ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      fun n => mem_iInter.1 hf n
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    exact le_antisymm (ge_of_tendsto' hlim hf') bot_le
  rw [hInter] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds hε)).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩

/-- **Positivity of the median of the exit time.**  If the exit time from the open set `U` is almost
surely positive and almost surely finite under the probability measure `μ`, then the median of its
distribution function is positive. -/
theorem medianOf_exitCdf_pos (U : Set α) (hU : IsOpen U) (μ : Measure (ContinuousPath α))
    [IsProbabilityMeasure μ] (h0 : μ {f | ContinuousPath.exitTime U f = 0} = 0)
    (hT : μ {f | ContinuousPath.exitTime U f = ⊤} = 0) :
    0 < medianOf (exitCdf U μ) := by
  obtain ⟨δ, hδ, hlt⟩ := exists_exitCdf_lt U hU μ h0 (ε := 1 / 2) (by norm_num)
  have hne : {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ exitCdf U μ m}.Nonempty := by
    have hhalf : (1 / 2 : ℝ≥0∞) < 1 := ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top
    obtain ⟨m, hm1, hm2⟩ := (((tendsto_exitCdf_atTop_one U hU μ hT).eventually
      (lt_mem_nhds hhalf)).and (eventually_ge_atTop 0)).exists
    exact ⟨m, hm2, hm1.le⟩
  have hle : δ ≤ medianOf (exitCdf U μ) := by
    refine le_csInf hne fun m hm => ?_
    by_contra hlt'
    exact absurd (hm.2.trans (exitCdf_mono U μ (not_le.1 hlt').le)) (not_le.2 hlt)
  exact lt_of_lt_of_le hδ hle

end MatedCRT
