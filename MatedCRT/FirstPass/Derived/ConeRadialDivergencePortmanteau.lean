import MatedCRT.FirstPass.Frozen.S1cDivergence

/-!
# Radial divergence of the conditioned Brownian motion: the portmanteau step

Part of the proof of `FrozenConeRadialDivergenceCorrected` (`FirstPass/Frozen/S1cDivergence.lean:17`).

`ν` is the weak limit, as `δ → 0+`, of the laws `P_δ` of standard Brownian motion conditioned on
`{w t + c t > -δ for all t}` (`IsBMConditionedPositive`). The set `lateVisit c K T` of paths with
`w s + c s < K` for some `s > T` is open for the compact-open topology, so by the portmanteau theorem
`ν (lateVisit c K T) ≤ liminf_{δ → 0+} P_δ (lateVisit c K T)`.

* `isOpen_lateVisit`
* `measure_lateVisit_le`: a bound `P_δ (lateVisit c K T) ≤ ε` for all small `δ > 0` passes to `ν`.
* `ae_tendsto_atTop_of_tail`: if for every level `K` and `ε > 0` there is a time `T` with
  `P_δ (lateVisit c K T) ≤ ε` for all small `δ > 0`, then `ν`-almost surely `w s + c s → +∞`.
-/

namespace MatedCRT.ConeRadialDivergence

open MeasureTheory ProbabilityTheory Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal ENNReal BoundedContinuousFunction

/-- The paths `w` with `w s + c s < K` for some time `s > T`. -/
def lateVisit (c K : ℝ) (T : ℝ≥0) : Set (ContinuousPath ℝ) :=
  {w | ∃ s : ℝ≥0, T < s ∧ w s + c * (s : ℝ) < K}

/-- `lateVisit c K T` is open for the compact-open topology: it is a union of sets given by a strict
inequality on one coordinate. -/
lemma isOpen_lateVisit (c K : ℝ) (T : ℝ≥0) : IsOpen (lateVisit c K T) := by
  have h : lateVisit c K T =
      ⋃ s : {s : ℝ≥0 // T < s}, {w : ContinuousPath ℝ | w s + c * ((s : ℝ≥0) : ℝ) < K} := by
    ext w
    simp [lateVisit]
  rw [h]
  refine isOpen_iUnion fun s => ?_
  have h1 : Continuous fun w : ContinuousPath ℝ => w (s : ℝ≥0) + c * (((s : ℝ≥0)) : ℝ) :=
    (continuous_eval_const (s : ℝ≥0)).add continuous_const
  exact isOpen_lt h1 continuous_const

/-- Portmanteau: a bound for the conditioned laws `P_δ` on the open set `lateVisit c K T`, valid for
all small `δ > 0`, holds for the weak limit `ν`. -/
theorem measure_lateVisit_le {c : ℝ} {ν : Measure (ContinuousPath ℝ)}
    (hν : IsBMConditionedPositive c ν) (K : ℝ) (T : ℝ≥0) {ε : ℝ≥0∞}
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ((brownianMotion 0)[|stayAboveEvent c δ]) (lateVisit c K T) ≤ ε) :
    ν (lateVisit c K T) ≤ ε := by
  classical
  have : IsProbabilityMeasure ν := hν.1
  set P : Measure (ContinuousPath ℝ) := brownianMotion 0 with hP
  -- the total mass of `P_δ` tends to `1`, so `P_δ` is a probability measure for small `δ`
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
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (isOpen_lateVisit c K T)
  have hle : (𝓝[>] (0 : ℝ)).liminf
      (fun δ => (ρ δ : Measure (ContinuousPath ℝ)) (lateVisit c K T)) ≤ ε := by
    apply Filter.liminf_le_of_frequently_le'
    refine Filter.Eventually.frequently ?_
    filter_upwards [h, hρ] with δ h1 h2
    rw [h2]
    exact h1
  exact hport.trans hle

/-- If for every level `K` and every `ε > 0` there is a time `T` such that the conditioned laws `P_δ`
give mass at most `ε` to `lateVisit c K T` for all small `δ > 0`, then the weak limit `ν` of the
conditioned laws is carried by the paths with `w s + c s → +∞`. -/
theorem ae_tendsto_atTop_of_tail {c : ℝ} {ν : Measure (ContinuousPath ℝ)}
    (hν : IsBMConditionedPositive c ν)
    (htail : ∀ (K : ℝ) (ε : ℝ≥0∞), 0 < ε → ∃ T : ℝ≥0, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ((brownianMotion 0)[|stayAboveEvent c δ]) (lateVisit c K T) ≤ ε) :
    ∀ᵐ w ∂ν, Tendsto (fun s : ℝ≥0 => w s + c * (s : ℝ)) atTop atTop := by
  have hnull : ∀ K : ℕ, ν (⋂ T : ℝ≥0, lateVisit c (K : ℝ) T) = 0 := by
    intro K
    refine le_antisymm ?_ bot_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨T, hT⟩ := htail (K : ℝ) (ε : ℝ≥0∞) (by exact_mod_cast hε)
    calc ν (⋂ T : ℝ≥0, lateVisit c (K : ℝ) T) ≤ ν (lateVisit c (K : ℝ) T) :=
          measure_mono (Set.iInter_subset _ T)
      _ ≤ (ε : ℝ≥0∞) := measure_lateVisit_le hν (K : ℝ) T hT
      _ = 0 + ε := by simp
  have hae : ∀ᵐ w ∂ν, ∀ K : ℕ, w ∉ ⋂ T : ℝ≥0, lateVisit c (K : ℝ) T :=
    ae_all_iff.2 fun K => measure_eq_zero_iff_ae_notMem.1 (hnull K)
  filter_upwards [hae] with w hw
  rw [tendsto_atTop_atTop]
  intro b
  have hK := hw ⌈b⌉₊
  simp only [Set.mem_iInter, not_forall] at hK
  obtain ⟨T, hT⟩ := hK
  refine ⟨T + 1, fun a ha => ?_⟩
  have hTa : T < a := lt_of_lt_of_le (lt_add_one T) ha
  have h1 : ¬ (w a + c * (a : ℝ) < (⌈b⌉₊ : ℝ)) := fun hlt => hT ⟨a, hTa, hlt⟩
  exact (Nat.le_ceil b).trans (not_lt.1 h1)

end MatedCRT.ConeRadialDivergence
