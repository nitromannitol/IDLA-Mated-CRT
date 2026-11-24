import MatedCRT.FirstPass.Derived.ChartConformalClock
import MatedCRT.FirstPass.Derived.ExitTimeClockAtExit

/-!
# Transport of a time change of planar Brownian motion under an inverse chart

Pathwise part of step R1 of the Revuz route to Berestycki (2015), Theorem 1.3 (*Diffusion in planar Liouville
quantum gravity*, arXiv:1301.3356): the chart image of a time-changed path, stopped at its exit from the window, is
the conformal image path (the path run with its conformal clock, `ChartConformalClock.lean`) run with the transported
clock and stopped at its exit from the unit disc.

Let `A`, `F`, `G` be time-change clocks, `τ` the exit time of the path `b` from the open set `U`, and assume
`G σ = F (A⁻¹ σ)` for `σ ≤ A τ`. Then `A⁻¹ ∘ G⁻¹` and `F⁻¹` agree up to the time `τ`
(`min_clockInverse_comp_eq`), and therefore (`chartStopPath_lbmContinuousPath_eq`)

`ψ ∘ (b ∘ F⁻¹ stopped at its exit from U) = (W ∘ G⁻¹ stopped at its exit from the unit disc)`,

where `W = ψ ∘ (b ∘ A⁻¹ stopped at its exit from U)`, which leaves the unit disc at the time `A τ`
(`exitTime_chartStopPath_lbmContinuousPath`). Here `f⁻¹` is the clock inverse `HarmonicBalls.clockInverse f`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

section ClockAlgebra

/-- A time-change clock is nonnegative. -/
theorem IsTimeChangeClock.clock_nonneg {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f) (s : ℝ≥0) : 0 ≤ f s := by
  have h := hf.strictMono.monotone (zero_le : (0 : ℝ≥0) ≤ s)
  rwa [hf.map_zero] at h

/-- A time-change clock takes the value `t` at its inverse at `t`. -/
theorem IsTimeChangeClock.apply_clockInverse_eq {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f) (t : ℝ≥0) :
    f (_root_.HarmonicBalls.clockInverse f t) = t := by
  obtain ⟨u, hu⟩ := IsTimeChangeClock.surjective_toNNReal hf t
  have hu' : Real.toNNReal (f u) = t := hu
  rw [← hu', clockInverse_clockValue hf.map_zero hf.strictMono u,
    Real.coe_toNNReal _ (IsTimeChangeClock.clock_nonneg hf u)]

/-- **Composition of time changes up to a time.** Let `A`, `F`, `G` be time-change clocks and `τ` a time such that
`G σ = F (A⁻¹ σ)` for `σ ≤ A τ`. Then `min (A⁻¹ (G⁻¹ t)) τ = min (F⁻¹ t) τ` for every `t`. -/
theorem min_clockInverse_comp_eq {A F G : ℝ≥0 → ℝ} (hA : IsTimeChangeClock A) (hF : IsTimeChangeClock F)
    (hG : IsTimeChangeClock G) {τ : ℝ≥0}
    (hGF : ∀ σ : ℝ≥0, (σ : ℝ) ≤ A τ → G σ = F (_root_.HarmonicBalls.clockInverse A σ)) (t : ℝ≥0) :
    min (_root_.HarmonicBalls.clockInverse A (_root_.HarmonicBalls.clockInverse G t)) τ =
      min (_root_.HarmonicBalls.clockInverse F t) τ := by
  set u := _root_.HarmonicBalls.clockInverse F t
  set v := _root_.HarmonicBalls.clockInverse G t
  by_cases ht : (t : ℝ) ≤ F τ
  · have huτ : u ≤ τ := (clockInverse_le_iff_of_isTimeChangeClock hF t τ).2 ht
    have hFu : F u = t := IsTimeChangeClock.apply_clockInverse_eq hF t
    have hσA : ((Real.toNNReal (A u) : ℝ≥0) : ℝ) = A u :=
      Real.coe_toNNReal _ (IsTimeChangeClock.clock_nonneg hA _)
    have hAσ : _root_.HarmonicBalls.clockInverse A (Real.toNNReal (A u)) = u :=
      clockInverse_clockValue hA.map_zero hA.strictMono _
    have hστ : ((Real.toNNReal (A u) : ℝ≥0) : ℝ) ≤ A τ := by
      rw [hσA]
      exact hA.strictMono.monotone huτ
    have hGσ : G (Real.toNNReal (A u)) = t := by
      rw [hGF _ hστ, hAσ, hFu]
    have hGinv : v = Real.toNNReal (A u) := by
      have h := clockInverse_clockValue hG.map_zero hG.strictMono (Real.toNNReal (A u))
      rwa [hGσ, Real.toNNReal_coe] at h
    rw [hGinv, hAσ, min_eq_left huτ]
  · have ht' : F τ < t := not_le.1 ht
    have hτF : τ ≤ u := by
      refine not_lt.1 fun h => ?_
      exact ht ((clockInverse_le_iff_of_isTimeChangeClock hF t τ).1 h.le)
    have hτAG : τ ≤ _root_.HarmonicBalls.clockInverse A v := by
      refine not_lt.1 fun h => ?_
      have hAσ : A (_root_.HarmonicBalls.clockInverse A v) = v :=
        IsTimeChangeClock.apply_clockInverse_eq hA _
      have hσlt : (v : ℝ) < A τ := by
        rw [← hAσ]
        exact hA.strictMono h
      have hGσ : G v = t := IsTimeChangeClock.apply_clockInverse_eq hG t
      have h1 : F (_root_.HarmonicBalls.clockInverse A v) < F τ := hF.strictMono h
      have h2 := hGF _ hσlt.le
      linarith
    rw [min_eq_right hτF, min_eq_right hτAG]

end ClockAlgebra

section StoppedTimeChange

/-- **The stopped time-changed path.** If the path `g` leaves `O` at the time `τ` and `F g` is a time-change clock,
then the path `g` run with the clock `F g` and stopped at its exit from `O` is `t ↦ g (min (F⁻¹ t) τ)`. -/
theorem stopAtExitTime_lbmContinuousPath_apply {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {g : ContinuousPath ℂ}
    (hF : IsTimeChangeClock (F g)) {O : Set ℂ} {τ : ℝ≥0} (hτ : ContinuousPath.exitTime O g = τ) (t : ℝ≥0) :
    stopAtExitTime O (lbmContinuousPath F g) t = g (min (_root_.HarmonicBalls.clockInverse (F g) t) τ) := by
  have hexit : ContinuousPath.exitTime O (lbmContinuousPath F g) =
      ((Real.toNNReal (F g τ) : ℝ≥0) : ℝ≥0∞) := by
    rw [lbmContinuousPath_of_isTimeChangeClock hF]
    exact pathExitTime_comp_clockInverse_eq_ofReal hF O g hτ
  have happ : ∀ s, lbmContinuousPath F g s = g (_root_.HarmonicBalls.clockInverse (F g) s) := by
    intro s
    rw [lbmContinuousPath_of_isTimeChangeClock hF]
    rfl
  show lbmContinuousPath F g (exitClamp (ContinuousPath.exitTime O (lbmContinuousPath F g)) t) = _
  rw [hexit, exitClamp_apply, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe, happ,
    (IsTimeChangeClock.strictMono_clockInverse hF).monotone.map_min,
    clockInverse_clockValue hF.map_zero hF.strictMono τ]

variable {U : Set ℂ} {ψ : C(ℂ, ℂ)}

/-- The chart image of the path `b` run with the clock `A b` and stopped at its exit from `U`, when `b` leaves `U` at
the time `τ`: at time `σ` it is `ψ (b (min (A⁻¹ σ) τ))`. -/
theorem chartStopPath_lbmContinuousPath_apply {A : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ}
    (hA : IsTimeChangeClock (A b)) {τ : ℝ≥0} (hτ : ContinuousPath.exitTime U b = τ) (σ : ℝ≥0) :
    chartStopPath U ψ (lbmContinuousPath A b) σ =
      ψ (b (min (_root_.HarmonicBalls.clockInverse (A b) σ) τ)) := by
  show ψ (stopAtExitTime U (lbmContinuousPath A b) σ) = _
  rw [stopAtExitTime_lbmContinuousPath_apply hA hτ]

/-- **The conformal image path leaves the unit disc at the clock value of the exit time.** If `ψ` maps the open set
`U` into the unit disc and its frontier outside, the path `b` starts in `U` and leaves it at the time `τ`, and `A b` is
a time-change clock, then the chart image of `b` run with the clock `A b` and stopped at its exit from `U` leaves the
unit disc at the time `A b τ`. -/
theorem exitTime_chartStopPath_lbmContinuousPath (hU : IsOpen U)
    (hψU : MapsTo ψ U (Metric.ball (0 : ℂ) 1)) (hψf : MapsTo ψ (frontier U) (Metric.ball (0 : ℂ) 1)ᶜ)
    {A : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} (hA : IsTimeChangeClock (A b)) (hb0 : b 0 ∈ U)
    {τ : ℝ≥0} (hτ : ContinuousPath.exitTime U b = τ) :
    ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) (chartStopPath U ψ (lbmContinuousPath A b)) =
      ((Real.toNNReal (A b τ) : ℝ≥0) : ℝ≥0∞) := by
  have hfin : ContinuousPath.exitTime U b ≠ ⊤ := by
    rw [hτ]
    exact ENNReal.coe_ne_top
  have hfront : b τ ∈ frontier U := by
    have h := ContinuousPath.coordinate_exitTime_mem_frontier U hU b hb0 hfin
    rwa [hτ, ENNReal.toNNReal_coe] at h
  have hout : chartStopPath U ψ (lbmContinuousPath A b) (Real.toNNReal (A b τ)) ∉
      Metric.ball (0 : ℂ) 1 := by
    rw [chartStopPath_lbmContinuousPath_apply hA hτ, clockInverse_clockValue hA.map_zero hA.strictMono τ,
      min_self]
    exact hψf hfront
  have hin : ∀ σ : ℝ≥0, σ < Real.toNNReal (A b τ) →
      chartStopPath U ψ (lbmContinuousPath A b) σ ∈ Metric.ball (0 : ℂ) 1 := by
    intro σ hσ
    have hlt : _root_.HarmonicBalls.clockInverse (A b) σ < τ := by
      refine not_le.1 fun h => ?_
      have h1 : A b τ ≤ A b (_root_.HarmonicBalls.clockInverse (A b) σ) := hA.strictMono.monotone h
      rw [IsTimeChangeClock.apply_clockInverse_eq hA σ] at h1
      have h2 : Real.toNNReal (A b τ) ≤ σ := by
        have h3 := Real.toNNReal_le_toNNReal h1
        rwa [Real.toNNReal_coe] at h3
      exact absurd hσ (not_lt.2 h2)
    rw [chartStopPath_lbmContinuousPath_apply hA hτ, min_eq_left hlt.le]
    refine hψU (ContinuousPath.mem_of_lt_exitTime U b _ ?_)
    rw [hτ]
    exact ENNReal.coe_lt_coe.2 hlt
  refine le_antisymm (ContinuousPath.exitTime_le_of_notMem _ _ _ hout) ?_
  show ((Real.toNNReal (A b τ) : ℝ≥0) : ℝ≥0∞) ≤
    pathExitTime (Metric.ball (0 : ℂ) 1) (chartStopPath U ψ (lbmContinuousPath A b))
  unfold pathExitTime
  refine le_sInf ?_
  rintro _ ⟨s, rfl, hs⟩
  refine not_lt.1 fun hlt => hs (hin s ?_)
  exact ENNReal.coe_lt_coe.1 hlt

/-- **Transport of a time change under an inverse chart (pathwise).** Let `ψ` map the open set `U` into the unit
disc and its frontier outside, let the path `b` start in `U` and leave it at the time `τ`, and let `A b`, `F b` be
time-change clocks. Let `W` be the chart image of `b` run with the clock `A b` and stopped at its exit from `U`, and
let `G W` be a time-change clock with `G W σ = F b (A⁻¹ σ)` for `σ ≤ A b τ`. Then the chart image of `b` run with
the clock `F b` and stopped at its exit from `U` is `W` run with the clock `G W` and stopped at its exit from the
unit disc. -/
theorem chartStopPath_lbmContinuousPath_eq (hU : IsOpen U)
    (hψU : MapsTo ψ U (Metric.ball (0 : ℂ) 1)) (hψf : MapsTo ψ (frontier U) (Metric.ball (0 : ℂ) 1)ᶜ)
    {A F G : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} (hA : IsTimeChangeClock (A b))
    (hF : IsTimeChangeClock (F b)) (hb0 : b 0 ∈ U) {τ : ℝ≥0} (hτ : ContinuousPath.exitTime U b = τ)
    (hG : IsTimeChangeClock (G (chartStopPath U ψ (lbmContinuousPath A b))))
    (hGF : ∀ σ : ℝ≥0, (σ : ℝ) ≤ A b τ →
      G (chartStopPath U ψ (lbmContinuousPath A b)) σ = F b (_root_.HarmonicBalls.clockInverse (A b) σ)) :
    chartStopPath U ψ (lbmContinuousPath F b) =
      stopAtExitTime (Metric.ball (0 : ℂ) 1)
        (lbmContinuousPath G (chartStopPath U ψ (lbmContinuousPath A b))) := by
  have hexit := exitTime_chartStopPath_lbmContinuousPath hU hψU hψf hA hb0 hτ
  ext t
  rw [stopAtExitTime_lbmContinuousPath_apply hG hexit, chartStopPath_lbmContinuousPath_apply hA hτ,
    (IsTimeChangeClock.strictMono_clockInverse hA).monotone.map_min,
    clockInverse_clockValue hA.map_zero hA.strictMono τ, min_assoc, min_self,
    min_clockInverse_comp_eq hA hF hG hGF t, chartStopPath_lbmContinuousPath_apply hF hτ]

end StoppedTimeChange

end MatedCRT
