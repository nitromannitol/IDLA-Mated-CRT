import LatticeProb.Prob.BrownianDriftConditionedWeakLimit
import MatedCRT.Defs.QuantumCone
import MatedCRT.FirstPass.LPBridge.ExitRestartCanonical

/-!
# Existence of the Brownian motion conditioned to stay positive

For `c > 0`, the laws of standard Brownian motion conditioned on `{w t + c t > -δ for all t}`
converge weakly as `δ → 0+` (`LatticeProb.exists_weakLimit_stayAbove`).  This is the existence
of a measure `ν` with `IsBMConditionedPositive c ν` (Definition 2.1, line 430), used for the
radial part of the quantum cone.

* `exists_isBMConditionedPositive`: for `c > 0` there is `ν` with `IsBMConditionedPositive c ν`.
-/

namespace MatedCRT.ConeBMConditioned

open MeasureTheory ProbabilityTheory Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal ENNReal BoundedContinuousFunction

/-- **Existence of the Brownian motion conditioned to stay positive.**  For `c > 0` there is a
probability measure `ν` on path space which is the weak limit, as `δ → 0+`, of the laws of
standard Brownian motion conditioned on `{w t + c t > -δ for all t}`. -/
theorem exists_isBMConditionedPositive {c : ℝ} (hc : 0 < c) :
    ∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive c ν := by
  have hpre : ProbabilityTheory.IsPreBrownianReal (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t)
      (brownianMotion 0) := by
    simpa using MatedCRT.ExitRestart.brownianMotion_isPreBrownianReal 0
  have hB : ProbabilityTheory.IsBrownianReal (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t)
      (brownianMotion 0) := ⟨hpre, Filter.Eventually.of_forall fun ω => ω.continuous⟩
  have hm : ∀ t : ℝ≥0, Measurable fun ω : ContinuousPath ℝ => ω t := fun t =>
    MarkovProcess.ContinuousPath.measurable_coordinateProcess t
  have hcont : ∀ ω : ContinuousPath ℝ, Continuous fun s : ℝ≥0 => ω s := fun ω => ω.continuous
  obtain ⟨ν, hν, hlim⟩ := LatticeProb.exists_weakLimit_stayAbove hB hm hcont hc
  have hid : LatticeProb.pathMap (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t) hcont = id :=
    funext fun ω => ContinuousMap.ext fun t => rfl
  refine ⟨ν, hν, fun f => ?_⟩
  have h := hlim f
  simp only [hid, Measure.map_id] at h
  exact h

end MatedCRT.ConeBMConditioned
