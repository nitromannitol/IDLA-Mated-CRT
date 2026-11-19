import MatedCRT.FirstPass.Derived.InterpWalkLawClassClose
import MatedCRT.FirstPass.Derived.UniformStartGoodSandwich
import MatedCRT.FirstPass.Derived.BlockExitSkeletonLevyProkhorov
import MatedCRT.FirstPass.Derived.ExitReparamClass
import MatedCRT.FirstPass.Derived.StoppedWalkScaling
import MatedCRT.FirstPass.Derived.StopAtExitWalkBound

/-!
# The stopped curve class of the quenched walk law, from the uniform-start good event

On the good event of the uniform-start invariance principle (`MatedCRT.UniformStartGood.goodG`, the all-sets
form of `GMS21UniformStartInput`) the Lévy–Prokhorov distance, on the space of curves modulo time
parametrization, between the stopped walk class law from a vertex `x` with `η(εx) ∈ closedBall 0 ρ` and the stopped
Brownian class law from `η(εx)` is at most `κ` (`levyProkhorovEDist_walkPathLaw_stoppedExitCurve_le`).  The walk
path law is the one of the interpolated walk with time scale `mε`; the uniform-start event is stated for the time
scale one.  The two stopped classes agree, as they differ by a linear change of time
(`stoppedExitCurve_comp_mul`, `interpPathCM_eq_comp_mul`).
-/

namespace MatedCRT.WalkClassLevyProkhorov

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open _root_.HarmonicBalls
open scoped NNReal ENNReal
open MatedCRT.StopAtExitLevyProkhorov MatedCRT.ExitReparamClass MatedCRT.FirstPass.Derived

/-- A linear change of time does not change the stopped curve class of a path that exits `U`. -/
theorem stoppedExitCurve_comp_mul {f g : ContinuousPath ℂ} {c : ℝ≥0} (hc : c ≠ 0)
    (hfg : ∀ t, f t = g (c * t)) {U : Set ℂ} (hU : IsOpen U) (hfin : pathExitTime U ⇑g < ⊤) :
    stoppedExitCurve U f = stoppedExitCurve U g := by
  obtain ⟨m, -, hgm⟩ := MatedCRT.M0Cdf.exists_exit_eq hU g hfin
  have hpos : 0 < c := pos_iff_ne_zero.2 hc
  have hcm : c * (m / c) = m := mul_div_cancel₀ m hc
  refine stoppedExitCurve_eq_of_exactReparam (a := m / c) (b := m) (φ := fun t => c * t) ?_ hU ?_
  · refine ⟨fun s _ t _ hst => mul_lt_mul_of_pos_left hst hpos, fun t ht => ?_, fun y hy => ?_,
      fun t _ => hfg t⟩
    · calc c * t ≤ c * (m / c) := mul_le_mul_of_nonneg_left (mem_Iic.1 ht) bot_le
        _ = m := hcm
    · refine ⟨y / c, mem_Iic.2 (div_le_div_of_nonneg_right (mem_Iic.1 hy) bot_le), ?_⟩
      exact mul_div_cancel₀ y hc
  · rw [hfg, hcm]
    exact hgm

/-- The interpolated walk with time scale `m` is the one with time scale one after the linear change of time
`t ↦ m t`. -/
theorem interpPathCM_eq_comp_mul (v : ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) (x : ℕ → ℤ) (t : ℝ≥0) :
    interpPathCM v hm x t = interpPathCM v zero_le_one x (m.toNNReal * t) := by
  simp only [interpPathCM_apply]
  have h := StoppedWalkScaling.interpPathFn_mul_speed v m.toNNReal 1 x t
  rw [mul_one, Real.coe_toNNReal m hm, NNReal.coe_one] at h
  exact h

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Class-level Lévy–Prokhorov bound for the quenched walk law from a vertex.**  On the uniform-start good event
at tolerance `κ`, with the walk exiting `ball 0 R` almost surely from the vertices in `closedBall 0 ρ`, the stopped
curve class law of the quenched walk from such a vertex `x` (time scale `mε > 0`) is within Lévy–Prokhorov
distance `κ` of the stopped class law of planar Brownian motion from `η(εx)`. -/
theorem levyProkhorovEDist_walkPathLaw_stoppedExitCurve_le (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ))
    {ε R ρ κ : ℝ} (hmε : 0 < S.mε ε) {ω : Ω} (hη : ⇑(η' ω) = S.η ω)
    (hfin : ω ∈ UniformStartGood.finExit S ε R ρ) (hG : ω ∈ UniformStartGood.goodG S ε R ρ κ) {x : ℤ}
    (hx : vertexPoint ε (⇑(η' ω)) x ∈ closedBall (0 : ℂ) ρ) :
    levyProkhorovEDist
      (((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
          (stoppedExitCurve (ball (0 : ℂ) R)))
      ((planarBrownianMotion (vertexPoint ε (⇑(η' ω)) x)).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤
        ENNReal.ofReal κ := by
  have hvv : vertexPoint ε (⇑(η' ω)) = vertexPoint ε (S.η ω) := by rw [hη]
  have hx' : vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ := hvv ▸ hx
  have hfinx : ∀ᵐ ξ ∂(srwLaw (S.mult ε ω) x),
      pathExitTime (ball (0 : ℂ) R) ⇑(interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ) ≠ ⊤ :=
    hfin x hx'
  have hmeas : Measurable fun ξ => stoppedExitCurve (ball (0 : ℂ) R)
      (interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ) :=
    (measurable_stoppedExitCurve _ isOpen_ball).comp (measurable_interpPathCM _ _)
  have hC1 := BlockExit.levyProkhorovEDist_stoppedExitCurve_le_of_allSet (srwLaw (S.mult ε ω) x)
    (fun ξ => interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ) (ball (0 : ℂ) R) hmeas.aemeasurable
    hfinx (ball (0 : ℂ) R) isOpen_ball (vertexPoint ε (S.η ω) x)
    (StopAtExitWalkBound.ae_pathExitTime_planarBrownianMotion_ne_top Metric.isBounded_ball _)
    (κ := κ) (E := ENNReal.ofReal κ) (fun A => hG x hx' A)
  have hwalk : (((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
          (stoppedExitCurve (ball (0 : ℂ) R))) =
      (srwLaw (S.mult ε ω) x).map fun ξ => stoppedExitCurve (ball (0 : ℂ) R)
        (interpPathCM (vertexPoint ε (S.η ω)) zero_le_one ξ) := by
    have h1 : ((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) =
        (srwLaw (S.mult ε ω) x).map (interpPathCM (vertexPoint ε (S.η ω)) (S.mε_nonneg ε)) := by
      show Measure.map (interpPathCM (vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε)) _ = _
      rw [hvv]
    rw [h1, Measure.map_map (measurable_stoppedExitCurve _ isOpen_ball)
      (measurable_interpPathCM _ _)]
    refine Measure.map_congr ?_
    filter_upwards [hfinx] with ξ hξ
    refine stoppedExitCurve_comp_mul (c := (S.mε ε).toNNReal) ?_ (fun t => ?_) isOpen_ball
      (lt_top_iff_ne_top.2 hξ)
    · exact (Real.toNNReal_pos.2 hmε).ne'
    · exact interpPathCM_eq_comp_mul _ _ _ _
  rw [hwalk, hvv]
  simpa using hC1

end MatedCRT.WalkClassLevyProkhorov
