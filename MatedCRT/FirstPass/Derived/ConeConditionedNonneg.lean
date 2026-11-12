import MatedCRT.FirstPass.Derived.ConeRadialDivergencePortmanteau

/-!
# Brownian motion conditioned to stay above a line: the weak limit stays nonnegative

`ν` is the weak limit, as `δ → 0+`, of the laws `P_δ` of standard Brownian motion conditioned on
`{w t + c t > -δ for all t ≥ 0}` (`IsBMConditionedPositive`). For `ε > 0` the set of paths with
`w s + c s < -ε` for some `s ≥ 0` is open for the compact-open topology and is disjoint from the
conditioning event as soon as `δ ≤ ε`; by the portmanteau theorem it is `ν`-null. Taking
`ε = 1/(n+1)` gives `ν`-almost surely `w t + c t ≥ 0` for all `t`.

* `measure_isOpen_le_of_eventually`: portmanteau for an arbitrary open set.
* `ae_forall_nonneg_of_isBMConditionedPositive`: `∀ᵐ w ∂ν, ∀ t, 0 ≤ w t + c t`.
-/

namespace MatedCRT.ConeConditionedNonneg

open MeasureTheory ProbabilityTheory Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal ENNReal BoundedContinuousFunction

/-- Portmanteau for the weak limit `ν` of the conditioned laws `P_δ`: a bound `P_δ U ≤ ε` for all small
`δ > 0` on an open set `U` passes to `ν U`. -/
theorem measure_isOpen_le_of_eventually {c : ℝ} {ν : Measure (ContinuousPath ℝ)}
    (hν : IsBMConditionedPositive c ν) {U : Set (ContinuousPath ℝ)} (hU : IsOpen U) {ε : ℝ≥0∞}
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((brownianMotion 0)[|stayAboveEvent c δ]) U ≤ ε) :
    ν U ≤ ε := by
  classical
  have : IsProbabilityMeasure ν := hν.1
  set P : Measure (ContinuousPath ℝ) := brownianMotion 0 with hP
  have hmass : Tendsto (fun δ => ((P[|stayAboveEvent c δ]) Set.univ).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h1 := hν.2 (BoundedContinuousFunction.const (ContinuousPath ℝ) (1 : ℝ))
    simpa [integral_const, Measure.real] using h1
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), IsProbabilityMeasure (P[|stayAboveEvent c δ]) := by
    have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (1 / 2 : ℝ) < ((P[|stayAboveEvent c δ]) Set.univ).toReal :=
      hmass.eventually (lt_mem_nhds (by norm_num))
    filter_upwards [h1] with δ hδ
    have hne : P (stayAboveEvent c δ) ≠ 0 := by
      intro h0
      rw [cond_eq_zero_of_meas_eq_zero h0] at hδ
      simp at hδ
      linarith
    exact cond_isProbabilityMeasure hne
  let ρ : ℝ → ProbabilityMeasure (ContinuousPath ℝ) := fun δ =>
    if hδ : IsProbabilityMeasure (P[|stayAboveEvent c δ]) then ⟨P[|stayAboveEvent c δ], hδ⟩
    else ⟨Measure.dirac (0 : ContinuousPath ℝ), inferInstance⟩
  have hρ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ρ δ : Measure (ContinuousPath ℝ)) = P[|stayAboveEvent c δ] := by
    filter_upwards [hev] with δ hδ
    simp [ρ, hδ]
  let ν' : ProbabilityMeasure (ContinuousPath ℝ) := ⟨ν, inferInstance⟩
  have hlim : Tendsto ρ (𝓝[>] (0 : ℝ)) (𝓝 ν') := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    refine (hν.2 f).congr' ?_
    filter_upwards [hρ] with δ hδ
    rw [hδ]
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hU
  have hle : (𝓝[>] (0 : ℝ)).liminf
      (fun δ => (ρ δ : Measure (ContinuousPath ℝ)) U) ≤ ε := by
    apply Filter.liminf_le_of_frequently_le'
    refine Filter.Eventually.frequently ?_
    filter_upwards [h, hρ] with δ h1 h2
    rw [h2]
    exact h1
  exact hport.trans hle

/-- The paths `w` with `w s + c s < -ε` for some time `s ≥ 0`. -/
def belowEvent (c ε : ℝ) : Set (ContinuousPath ℝ) :=
  {w | ∃ s : ℝ≥0, w s + c * (s : ℝ) < -ε}

/-- `belowEvent c ε` is open for the compact-open topology. -/
lemma isOpen_belowEvent (c ε : ℝ) : IsOpen (belowEvent c ε) := by
  have h : belowEvent c ε =
      ⋃ s : ℝ≥0, {w : ContinuousPath ℝ | w s + c * ((s : ℝ≥0) : ℝ) < -ε} := by
    ext w
    simp [belowEvent]
  rw [h]
  refine isOpen_iUnion fun s => ?_
  have h1 : Continuous fun w : ContinuousPath ℝ => w (s : ℝ≥0) + c * ((s : ℝ≥0) : ℝ) :=
    (continuous_eval_const (s : ℝ≥0)).add continuous_const
  exact isOpen_lt h1 continuous_const

/-- For `0 < δ ≤ ε` the conditioning event `{w t + c t > -δ ∀ t}` is disjoint from `belowEvent c ε`. -/
lemma disjoint_stayAbove_belowEvent (c : ℝ) {δ ε : ℝ} (h : δ ≤ ε) :
    Disjoint (stayAboveEvent c δ) (belowEvent c ε) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨s, hs⟩
  have := hw s
  linarith

/-- The weak limit `ν` of Brownian motion conditioned on `{w t + c t > -δ ∀ t}` gives mass `0` to
`belowEvent c ε`. -/
lemma measure_belowEvent_eq_zero {c : ℝ} {ν : Measure (ContinuousPath ℝ)}
    (hν : IsBMConditionedPositive c ν) {ε : ℝ} (hε : 0 < ε) : ν (belowEvent c ε) = 0 := by
  refine le_antisymm ?_ bot_le
  refine measure_isOpen_le_of_eventually hν (isOpen_belowEvent c ε) (ε := 0) ?_
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ ε := by
    filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ using hδ.2.le
  filter_upwards [hev] with δ hδ
  have h0 := (disjoint_stayAbove_belowEvent c hδ).inter_eq
  rw [cond_apply' ((isOpen_belowEvent c ε).measurableSet)]
  simp [h0]

/-- The weak limit `ν` of Brownian motion conditioned on `{w t + c t > -δ ∀ t}` is carried by the paths
with `w t + c t ≥ 0` for all `t ≥ 0`. -/
theorem ae_forall_nonneg_of_isBMConditionedPositive {c : ℝ} {ν : Measure (ContinuousPath ℝ)}
    (hν : IsBMConditionedPositive c ν) : ∀ᵐ w ∂ν, ∀ t : ℝ≥0, 0 ≤ w t + c * (t : ℝ) := by
  have hae : ∀ᵐ w ∂ν, ∀ n : ℕ, w ∉ belowEvent c (1 / ((n : ℝ) + 1)) :=
    ae_all_iff.2 fun n => measure_eq_zero_iff_ae_notMem.1
      (measure_belowEvent_eq_zero hν (by positivity))
  filter_upwards [hae] with w hw t
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 hneg)
  exact hw n ⟨t, by linarith⟩

end MatedCRT.ConeConditionedNonneg
