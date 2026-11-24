import MatedCRT.FirstPass.Derived.GMS21AnnulusStoppedCurve
import MatedCRT.FirstPass.Derived.ExitTimeCdfConvergence
import HarmonicBalls.Proofs.Potential.LQGClockAnnularReturnMoment

/-!
# From the annulus to the ball: hitting the hole

In the proof of Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1, the walk and Brownian motion are
compared until their exits from the annulus `U \ closedBall 0 α`, and `α` is chosen so small that Brownian motion
started from a point of `D \ B_δ(0)` hits `B_α(0)` before it leaves `D` with small probability. This file proves the
quantitative form of that step: by the logarithmic hitting estimate for planar Brownian motion, Brownian motion from
`z ∉ B_b(0)` hits `closedBall 0 r` before it leaves `U ⊆ B_R(0)` with probability at most
`log (R / b) / log (R / r)`; a Lévy–Prokhorov bound `< c` for the curves stopped at the exit from the annulus transfers
this bound, with `r = α + c`, to the walk; and the Lévy–Prokhorov distance of the curves stopped at the exit from `U`
is then at most `c + (log (R / b) / log (R / (α + c)) + c) + log (R / b) / log (R / α)`.

## Main results

* `exists_lt_pathExitTime_of_exitPoint_mem`: a continuous path whose exit point from `V ⊆ U` lies in a set `A ⊆ U`
  visits `A` strictly before it leaves the open set `U`.
* `planarBrownianMotion_exitPoint_mem_le`: the probability that Brownian motion from `z ∉ B_b(0)` leaves `V ⊆ U` at a
  point of `closedBall 0 r ⊆ U` is at most `log (R / b) / log (R / r)` (`U ⊆ B_R(0)`, `0 < r < b < R`).
* `planarBrownianMotion_hitsBeforeExit_le`: the same bound for hitting `closedBall 0 α ⊆ U` before leaving `U`.
* `levyProkhorovEDist_stoppedExitCurve_le_of_annulus`: the Lévy–Prokhorov distance between the laws of a random path
  and of Brownian motion from `z ∉ B_b(0)`, both stopped at their exits from `U`, is at most
  `c + (L (α + c) + c) + L α` when the distance for the exits from `U \ closedBall 0 α` is less than `c`, where
  `L x = log (R / b) / log (R / x)`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov

/-- A path is in `U` at all times up to its exit point from `V ⊆ U`, if that exit point lies in `U`. -/
theorem forall_le_mem_of_exitPoint_mem {U V : Set ℂ} (hVU : V ⊆ U) {f : ℝ≥0 → ℂ}
    (hp : f (pathExitTime V f).toNNReal ∈ U) : ∀ t ≤ (pathExitTime V f).toNNReal, f t ∈ U := by
  intro t ht
  rcases ht.lt_or_eq with ht | ht
  · apply hVU
    by_contra hfV
    have hle : pathExitTime V f ≤ (t : ℝ≥0∞) := sInf_le ⟨t, rfl, hfV⟩
    have hlt : (t : ℝ≥0∞) < ((pathExitTime V f).toNNReal : ℝ≥0∞) := ENNReal.coe_lt_coe.2 ht
    exact absurd (hlt.trans_le ENNReal.coe_toNNReal_le_self) (not_lt.2 hle)
  · rw [ht]
    exact hp

/-- **Visiting `A` before leaving `U`.** If the exit point of a continuous path from `V ⊆ U` lies in a set `A ⊆ U`,
with `U` open, then the path is in `A` at a time strictly before its exit time from `U`. -/
theorem exists_lt_pathExitTime_of_exitPoint_mem {U V A : Set ℂ} (hU : IsOpen U) (hVU : V ⊆ U) (hAU : A ⊆ U)
    {g : ContinuousPath ℂ} (hp : g (pathExitTime V ⇑g).toNNReal ∈ A) :
    ∃ s : ℝ≥0, g s ∈ A ∧ (s : ℝ≥0∞) < pathExitTime U ⇑g :=
  ⟨_, hp, (ExitTimeCdf.lt_pathExitTime_iff hU).2 (forall_le_mem_of_exitPoint_mem hVU (hAU hp))⟩

/-- **Brownian motion leaving `V` near the origin.** For `V ⊆ U ⊆ B_R(0)` with `U` open, `closedBall 0 r ⊆ U`,
`0 < r < b < R` and `z ∉ B_b(0)`, the probability that planar Brownian motion from `z` leaves `V` at a point of
`closedBall 0 r` is at most `log (R / b) / log (R / r)`. -/
theorem planarBrownianMotion_exitPoint_mem_le {U V : Set ℂ} (hU : IsOpen U) (hVU : V ⊆ U) {r b R : ℝ}
    (hr : 0 < r) (hrb : r < b) (hbR : b < R) (hUR : U ⊆ ball (0 : ℂ) R) (hrU : closedBall (0 : ℂ) r ⊆ U)
    {z : ℂ} (hz : z ∉ ball (0 : ℂ) b) :
    planarBrownianMotion z {ω : ContinuousPath ℂ | ω (pathExitTime V ⇑ω).toNNReal ∈ closedBall (0 : ℂ) r} ≤
      ENNReal.ofReal (Real.log R - Real.log b) / ENNReal.ofReal (Real.log R - Real.log r) := by
  refine le_trans (measure_mono fun ω hω => ?_)
    (planarBrownian_hit_closedBall_before_exitTime_le 0 hr hrb hbR hUR hz)
  exact exists_lt_pathExitTime_of_exitPoint_mem hU hVU hrU hω

/-- **Brownian motion hitting the hole.** For `U ⊆ B_R(0)` open, `closedBall 0 α ⊆ U`, `0 < α < b < R` and
`z ∉ B_b(0)`, the probability that planar Brownian motion from `z` hits `closedBall 0 α` before it leaves `U` is at
most `log (R / b) / log (R / α)`. -/
theorem planarBrownianMotion_hitsBeforeExit_le {U : Set ℂ} (hU : IsOpen U) {α b R : ℝ} (hα : 0 < α) (hαb : α < b)
    (hbR : b < R) (hUR : U ⊆ ball (0 : ℂ) R) (hαU : closedBall (0 : ℂ) α ⊆ U) {z : ℂ} (hz : z ∉ ball (0 : ℂ) b) :
    planarBrownianMotion z {ω : ContinuousPath ℂ | HitsBeforeExit U (closedBall (0 : ℂ) α) ⇑ω} ≤
      ENNReal.ofReal (Real.log R - Real.log b) / ENNReal.ofReal (Real.log R - Real.log α) :=
  le_trans (measure_mono fun _ hω => hω.2)
    (planarBrownianMotion_exitPoint_mem_le hU sdiff_subset hα hαb hbR hUR hαU hz)

/-- The `δ`-thickening of `closedBall 0 α` lies in `closedBall 0 (α + δ)`. -/
theorem thickening_closedBall_zero_subset (α δ : ℝ) :
    thickening δ (closedBall (0 : ℂ) α) ⊆ closedBall (0 : ℂ) (α + δ) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
  rw [mem_closedBall] at hy ⊢
  linarith [dist_triangle x y 0]

/-- **A random path hitting the hole, from a Lévy–Prokhorov bound on the annulus.** If the laws of the curve classes
of a random continuous path and of Brownian motion from `z ∉ B_b(0)`, both stopped at their exits from the annulus
`U \ closedBall 0 α`, are at Lévy–Prokhorov distance less than `c`, then the random path hits `closedBall 0 α` before
it leaves `U` with probability at most `log (R / b) / log (R / r) + c`, for `α + c ≤ r` and `closedBall 0 r ⊆ U`. -/
theorem measure_hitsBeforeExit_le_of_annulus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {W : Ω → ContinuousPath ℂ} (hW : AEMeasurable W P) {U : Set ℂ} (hU : IsOpen U) {α r b R : ℝ}
    (hr : 0 < r) (hrb : r < b) (hbR : b < R) (hUR : U ⊆ ball (0 : ℂ) R) (hrU : closedBall (0 : ℂ) r ⊆ U)
    {z : ℂ} (hz : z ∉ ball (0 : ℂ) b) {c : ℝ≥0∞} (hαc : α + c.toReal ≤ r)
    (hc : levyProkhorovEDist (P.map fun ω => stoppedExitCurve (U \ closedBall (0 : ℂ) α) (W ω))
      ((planarBrownianMotion z).map (stoppedExitCurve (U \ closedBall (0 : ℂ) α))) < c) :
    P {ω | HitsBeforeExit U (closedBall (0 : ℂ) α) ⇑(W ω)} ≤
      ENNReal.ofReal (Real.log R - Real.log b) / ENNReal.ofReal (Real.log R - Real.log r) + c := by
  have h := measure_hitsBeforeExit_le_of_levyProkhorovEDist_lt P (planarBrownianMotion z) hW aemeasurable_id hU
    isClosed_closedBall (W₂ := fun ω => ω) hc
  refine h.trans (add_le_add (le_trans (measure_mono fun ω hω => ?_)
    (planarBrownianMotion_exitPoint_mem_le (V := U \ closedBall (0 : ℂ) α) hU sdiff_subset hr hrb hbR hUR hrU
      hz)) le_rfl)
  exact closedBall_subset_closedBall hαc (thickening_closedBall_zero_subset α c.toReal hω)

/-- **From the annulus to the ball.** Let `U ⊆ B_R(0)` be open with `closedBall 0 r ⊆ U`, `0 < α`, `α + c ≤ r`,
`r < b < R` and `z ∉ B_b(0)`. If the laws of the curve classes of a random continuous path and of Brownian motion from
`z`, both stopped at their exits from the annulus `U \ closedBall 0 α`, are at Lévy–Prokhorov distance less than `c`,
then the laws of their curve classes stopped at their exits from `U` are at distance at most
`c + (L r + c) + L α`, where `L x = log (R / b) / log (R / x)`. -/
theorem levyProkhorovEDist_stoppedExitCurve_le_of_annulus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {W : Ω → ContinuousPath ℂ} (hW : AEMeasurable W P) {U : Set ℂ} (hU : IsOpen U) {α r b R : ℝ} (hα : 0 < α)
    (hr : 0 < r) (hrb : r < b) (hbR : b < R) (hUR : U ⊆ ball (0 : ℂ) R) (hrU : closedBall (0 : ℂ) r ⊆ U)
    {z : ℂ} (hz : z ∉ ball (0 : ℂ) b) {c : ℝ≥0∞} (hαc : α + c.toReal ≤ r)
    (hc : levyProkhorovEDist (P.map fun ω => stoppedExitCurve (U \ closedBall (0 : ℂ) α) (W ω))
      ((planarBrownianMotion z).map (stoppedExitCurve (U \ closedBall (0 : ℂ) α))) < c) :
    levyProkhorovEDist (P.map fun ω => stoppedExitCurve U (W ω))
        ((planarBrownianMotion z).map (stoppedExitCurve U)) ≤
      c + (ENNReal.ofReal (Real.log R - Real.log b) / ENNReal.ofReal (Real.log R - Real.log r) + c) +
        ENNReal.ofReal (Real.log R - Real.log b) / ENNReal.ofReal (Real.log R - Real.log α) := by
  have hαr : α ≤ r := by
    have := ENNReal.toReal_nonneg (a := c)
    linarith
  have hαU : closedBall (0 : ℂ) α ⊆ U := (closedBall_subset_closedBall hαr).trans hrU
  have h := levyProkhorovEDist_stoppedExitCurve_le_diff P (planarBrownianMotion z) hW aemeasurable_id hU
    isClosed_closedBall (W₂ := fun ω => ω) (K := closedBall (0 : ℂ) α)
  refine h.trans (add_le_add (add_le_add hc.le ?_) ?_)
  · exact measure_hitsBeforeExit_le_of_annulus P hW hU hr hrb hbR hUR hrU hz hαc hc
  · exact planarBrownianMotion_hitsBeforeExit_le hU hα (hαr.trans_lt hrb) hbR hUR hαU hz

end MatedCRT
