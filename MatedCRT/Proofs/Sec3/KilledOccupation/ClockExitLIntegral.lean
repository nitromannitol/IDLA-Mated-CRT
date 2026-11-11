import MatedCRT.Proofs.Sec3.KilledOccupation.RemovedTail
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockBinders
import LatticeProb.Prob.MeasurableLIntegralIic

/-!
# Measurability of the clock integral over `[0, σ]`

For a family `κ b` of measures on `ℝ≥0`, indexed by continuous paths `b : ℝ≥0 → ℂ`, whose masses
on the intervals `Iic t` are finite and measurable in `b`, the integral `∫_{[0, σ(b)]} q(b u) dκ_b(u)`
over the exit time `σ(b) = exitNN z r b` of the ball `ball z r` is measurable in `b`, for every
measurable `q : ℂ → ℝ≥0∞`. This is the shape of the binder `hMeas` of `closure4`
(`OccupationClosure4.lean`), with the two measurability hypotheses on `κ` written out.

The proof: the integrand `(b, u) ↦ 1_{u ≤ σ(b)} q(b u)` is jointly measurable, since `σ` is
measurable (`measurable_toNNReal_pathExitTime_ball`) and the evaluation `(b, u) ↦ b u` is jointly
measurable (`measurable_eval_path`); then the measurability of kernel integrals from the masses
on `Iic` (`LatticeProb.measurable_lintegral_of_measurable_Iic`) applies.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.KilledOccupation

/-- The exit time `exitNN z r` of the ball `ball z r` is measurable on the path space
(`measurable_pathExitTime_ball`, `BaseClockBinders.lean`). -/
lemma measurable_exitNN (z : ℂ) (r : ℝ) : Measurable fun b : ContinuousPath ℂ => exitNN z r b :=
  ENNReal.measurable_toNNReal.comp (measurable_pathExitTime_ball z r)

/-- Joint measurability of the evaluation `(b, u) ↦ b u` on `ContinuousPath ℂ × ℝ≥0`. This is
`measurable_eval_path` (`RegClockFun.lean`) composed with the swap of the factors. -/
lemma measurable_eval_path_pair : Measurable fun p : ContinuousPath ℂ × ℝ≥0 => p.1 p.2 :=
  (measurable_uncurry_of_continuous_of_measurable (u := fun (t : ℝ≥0) (b : ContinuousPath ℂ) => b t)
    (fun b => map_continuous b) (fun t => (continuous_eval_const t).measurable)).comp measurable_swap

/-- **Measurability of the clock integral over `[0, σ]`.** Let `κ : ContinuousPath ℂ → Measure ℝ≥0`
with each `κ b (Iic t)` finite and measurable in `b`. Then, for the exit time `σ = exitNN z r` of
`ball z r` and every measurable `q : ℂ → ℝ≥0∞`, the map `b ↦ ∫⁻ u in [0, σ(b)], q (b u) dκ b` is
measurable. -/
theorem measurable_setLIntegral_exitNN (κ : ContinuousPath ℂ → Measure ℝ≥0)
    (hfin : ∀ b t, κ b (Set.Iic t) ≠ ∞) (hIic : ∀ t : ℝ≥0, Measurable fun b => κ b (Set.Iic t))
    (z : ℂ) (r : ℝ) (q : ℂ → ℝ≥0∞) (hq : Measurable q) :
    Measurable fun b => ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(κ b) := by
  let M : Set (ContinuousPath ℂ × ℝ≥0) := {p | p.2 ≤ exitNN z r p.1}
  have hM : MeasurableSet M :=
    measurableSet_le measurable_snd ((measurable_exitNN z r).comp measurable_fst)
  have hF : Measurable fun p : ContinuousPath ℂ × ℝ≥0 => M.indicator (fun p => q (p.1 p.2)) p :=
    (hq.comp measurable_eval_path_pair).indicator hM
  have hint : ∀ b : ContinuousPath ℂ, ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(κ b) =
      ∫⁻ u, M.indicator (fun p => q (p.1 p.2)) (b, u) ∂(κ b) := by
    intro b
    rw [← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun u => ?_
    by_cases h : u ≤ exitNN z r b
    · rw [Set.indicator_of_mem (show u ∈ Icc (0 : ℝ≥0) (exitNN z r b) from ⟨zero_le, h⟩),
        Set.indicator_of_mem (show (b, u) ∈ M from h)]
    · rw [Set.indicator_of_notMem (show u ∉ Icc (0 : ℝ≥0) (exitNN z r b) from fun hh => h hh.2),
        Set.indicator_of_notMem (show (b, u) ∉ M from h)]
  have hfun : (fun b => ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(κ b)) =
      fun b => ∫⁻ u, M.indicator (fun p => q (p.1 p.2)) (b, u) ∂(κ b) :=
    funext hint
  rw [hfun]
  exact LatticeProb.measurable_lintegral_of_measurable_Iic κ hfin hIic hF

end MatedCRT.KilledOccupation
