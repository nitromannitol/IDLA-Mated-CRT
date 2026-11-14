import MatedCRT.FirstPass.Derived.JointBallExitMeasurable
import MatedCRT.FirstPass.Derived.BrownianRegularExitBall
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! # Joint continuity of planar ball exit times -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- At a finite regular exit from a positive-radius ball, the exit time is continuous
jointly in the path and the radius. -/
theorem continuousAt_planarBall_exitTime_joint {b : ContinuousPath ℂ} {r : ℝ}
    (hr : 0 < r) (hfin : pathExitTime (ball (0 : ℂ) r) b ≠ ⊤)
    (hreg : ∃ᶠ t in 𝓝[>] (pathExitTime (ball (0 : ℂ) r) b).toNNReal,
      b t ∉ closure (ball (0 : ℂ) r)) :
    ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
      ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) (b, r) := by
  rw [ContinuousAt, tendsto_order]
  constructor
  · intro a ha
    obtain ⟨s, has, hsτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    have hopen := (MatedCRT.isClosed_planarBall_exitTime_le s).isOpen_compl
    have hmem : (b, r) ∈ {p : ContinuousPath ℂ × ℝ |
        ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1 ≤ (s : ℝ≥0∞)}ᶜ := by
      exact not_le.mpr hsτ
    filter_upwards [hopen.mem_nhds hmem] with p hp
    exact lt_trans has (lt_of_not_ge hp)
  · intro a ha
    have hτa : ((pathExitTime (ball (0 : ℂ) r) b).toNNReal : ℝ≥0∞) < a := by
      rwa [ENNReal.coe_toNNReal hfin]
    obtain ⟨s, hτs, hsa⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hτa
    have hτs' : (pathExitTime (ball (0 : ℂ) r) b).toNNReal < s := ENNReal.coe_lt_coe.1 hτs
    obtain ⟨t, ht, hts⟩ := (hreg.and_eventually (Ioo_mem_nhdsGT hτs')).exists
    have ht' : r < dist (b t) 0 := by
      rw [closure_ball _ hr.ne', mem_closedBall, not_le] at ht
      exact ht
    have heval : Continuous (fun p : ContinuousPath ℂ × ℝ => p.1 t) :=
      (continuous_eval_const t).comp continuous_fst
    have hopen : IsOpen {p : ContinuousPath ℂ × ℝ | p.2 < dist (p.1 t) 0} :=
      isOpen_lt continuous_snd (heval.dist continuous_const)
    filter_upwards [hopen.mem_nhds ht'] with p hp
    have hout : p.1 t ∉ ball (0 : ℂ) p.2 := by
      simp only [mem_ball, not_lt]
      exact le_of_lt hp
    have hexit : ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1 ≤ (t : ℝ≥0∞) :=
      exitTime_le_of_not_mem hout
    exact lt_of_le_of_lt hexit (lt_trans (ENNReal.coe_lt_coe.2 hts.2) hsa)

/-- Joint ball-exit continuity holds almost surely for Brownian motion started inside the ball. -/
theorem ae_continuousAt_planarBall_exitTime_joint {x : ℂ} {r : ℝ}
    (hx : x ∈ ball (0 : ℂ) r) :
    ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
        ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) (b, r) := by
  have hr : 0 < r := lt_of_le_of_lt (dist_nonneg : 0 ≤ dist x (0 : ℂ)) hx
  filter_upwards [ae_regularExit_ball_planarBrownian hx] with b hb
  exact continuousAt_planarBall_exitTime_joint hr hb.1 (hb.2.resolve_left hb.1)

end MatedCRT.StopAtExitCmp
