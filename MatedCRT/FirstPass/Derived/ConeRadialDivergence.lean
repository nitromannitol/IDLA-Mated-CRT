import LatticeProb.Prob.BrownianDriftLateVisit
import LatticeProb.Prob.BrownianDriftSurvival
import MatedCRT.FirstPass.Derived.ConeRadialDivergencePortmanteau
import MatedCRT.FirstPass.LPBridge.ExitRestartCanonical

/-!
# Radial divergence of the conditioned Brownian motion

Proof of `FrozenConeRadialDivergenceCorrected` (`FirstPass/Frozen/S1cDivergence.lean:17`).

For `c > 0` and a level `K`, the laws `P_δ` of standard Brownian motion conditioned on
`{w t + c t > -δ for all t}` give mass at most `ε` to the paths that visit `{w s + c s < K}` after a
fixed time `T`, for all small `δ > 0` (`LatticeProb.exists_late_visit_tail`). The portmanteau step
`ae_tendsto_atTop_of_tail` then transfers this to the weak limit `ν`, which gives
`w s + c s → +∞` for `ν`-almost every `w`.

* `cond_lateVisit_le`: the uniform tail bound for the conditioned laws `P_δ` on `lateVisit c K T`.
* `frozenConeRadialDivergenceCorrected_holds`: the statement `FrozenConeRadialDivergenceCorrected`.
-/

namespace MatedCRT.ConeRadialDivergence

open MeasureTheory ProbabilityTheory Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal ENNReal BoundedContinuousFunction

/-- Evaluation at a time is measurable on the path space, after centring at the starting point `0`. -/
private lemma measurable_eval_sub_zero (t : ℝ≥0) :
    Measurable fun ω : ContinuousPath ℝ => ω t - 0 :=
  (MarkovProcess.ContinuousPath.measurable_coordinateProcess t).sub measurable_const

/-- Uniform tail bound for the conditioned laws `P_δ = (brownianMotion 0)[|stayAboveEvent c δ]`: for
`c > 0`, a level `K` and `ε > 0` there is a time `T` such that `P_δ (lateVisit c K T) ≤ ε` for all
small `δ > 0`. -/
theorem cond_lateVisit_le {c : ℝ} (hc : 0 < c) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ≥0, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ((brownianMotion 0)[|stayAboveEvent c δ]) (lateVisit c K T) ≤ ENNReal.ofReal ε := by
  have hB := MatedCRT.ExitRestart.brownianMotion_isPreBrownianReal 0
  have hcont : ∀ ω : ContinuousPath ℝ, Continuous fun t : ℝ≥0 => ω t - 0 :=
    fun ω => ω.continuous.sub continuous_const
  obtain ⟨T, δ₀, hδ₀, h⟩ := LatticeProb.exists_late_visit_tail hB measurable_eval_sub_zero hcont hc K hε
  refine ⟨T, ?_⟩
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioo 0 δ₀ := Ioo_mem_nhdsGT hδ₀
  filter_upwards [hev] with δ hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hS : (brownianMotion 0) (stayAboveEvent c δ) =
      ENNReal.ofReal (1 - Real.exp (-(2 * c * δ))) := by
    have := LatticeProb.measure_forall_drift_gt hB measurable_eval_sub_zero hcont hc hδ0
    simpa [stayAboveEvent] using this
  have hpos : 0 < 1 - Real.exp (-(2 * c * δ)) := by
    have h1 : Real.exp (-(2 * c * δ)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (by nlinarith [mul_pos hc hδ0])
    linarith
  have hne0 : (brownianMotion 0) (stayAboveEvent c δ) ≠ 0 := by
    rw [hS]; exact (ENNReal.ofReal_pos.2 hpos).ne'
  have hnetop : (brownianMotion 0) (stayAboveEvent c δ) ≠ ⊤ := by
    rw [hS]; exact ENNReal.ofReal_ne_top
  have hA : MeasurableSet (lateVisit c K T) := (isOpen_lateVisit c K T).measurableSet
  have key := h δ hδ0 hδ1
  have hset : ({ω : ContinuousPath ℝ | ∀ t : ℝ≥0, -δ < ω t - 0 + c * t} ∩
      {ω : ContinuousPath ℝ | ∃ s : ℝ≥0, T < s ∧ ω s - 0 + c * s < K}) =
      lateVisit c K T ∩ stayAboveEvent c δ := by
    ext ω
    simp [lateVisit, stayAboveEvent, and_comm]
  have hset2 : {ω : ContinuousPath ℝ | ∀ t : ℝ≥0, -δ < ω t - 0 + c * t} = stayAboveEvent c δ := by
    ext ω; simp [stayAboveEvent]
  rw [hset, hset2] at key
  unfold ProbabilityTheory.cond
  rw [Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  calc ((brownianMotion 0) (stayAboveEvent c δ))⁻¹ *
        (brownianMotion 0) (lateVisit c K T ∩ stayAboveEvent c δ)
      ≤ ((brownianMotion 0) (stayAboveEvent c δ))⁻¹ *
          (ENNReal.ofReal ε * (brownianMotion 0) (stayAboveEvent c δ)) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [mul_comm (ENNReal.ofReal ε), ← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]

end MatedCRT.ConeRadialDivergence

namespace MatedCRT

open MeasureTheory Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal ENNReal

/-- **Radial divergence of the conditioned Brownian motion** (`FrozenConeRadialDivergenceCorrected`):
the weak limit `ν` of standard Brownian motion conditioned on `{w t + c t > -δ for all t}`, with
drift `c = Q - γ > 0`, satisfies `w s + c s → +∞` almost surely. -/
theorem frozenConeRadialDivergenceCorrected_holds : FrozenConeRadialDivergenceCorrected := by
  intro γ hγ0 hγ2 ν hν
  have hc : 0 < lqgQ γ - γ := by
    unfold lqgQ
    have key : 2 / γ + γ / 2 - γ = (4 - γ ^ 2) / (2 * γ) := by
      field_simp
      ring
    rw [key]
    apply div_pos _ (by positivity)
    nlinarith
  refine ConeRadialDivergence.ae_tendsto_atTop_of_tail hν ?_
  intro K ε hε
  by_cases htop : ε = ⊤
  · exact ⟨0, Filter.Eventually.of_forall fun δ => by simp [htop]⟩
  · obtain ⟨T, hT⟩ := ConeRadialDivergence.cond_lateVisit_le hc K
      (ENNReal.toReal_pos hε.ne' htop)
    refine ⟨T, hT.mono fun δ hδ => hδ.trans ?_⟩
    rw [ENNReal.ofReal_toReal htop]

end MatedCRT
