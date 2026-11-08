import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockVersion
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.CutoffInverseContinuous

/-!
# Lemma 3.4 (item 4): measurability of the approximate Liouville paths

For a continuous circle-average field `hε ε` at a fixed radius `ε > 0`, the approximate Liouville clock
`t ↦ lqgClockApprox γ hε ε b t` of a continuous Brownian path `b` has the continuous positive density
`ε ^ (γ ^ 2 / 2) * exp (γ * hε ε (b s))`; hence it is continuous and strictly increasing in `t`, and it is jointly measurable in
`(b, t)` by the Carathéodory lemma (continuous in `t`, measurable in `b`). Consequently the cutoff approximate inverse
`b ↦ cutInv (clock b) n u` is measurable for each time `u`, the evaluations `b ↦ b (cutInv (clock b) n u)` of the time-changed
approximate path are measurable, and the approximate path `t ↦ b (cutInv (clock b) n (m t))` is continuous. These are the
ingredients of the grid approximation of the bounded Lipschitz functional of the approximate Liouville path (paper argument,
`docs/campaign/GAPS-SEC3.md` item 4).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal

section

variable {γ ε : ℝ} {hε : ℝ → ℂ → ℝ}

/-- The density `s ↦ ε ^ (γ ^ 2 / 2) * exp (γ * hε ε (b s))` of the approximate clock is continuous along a continuous path. -/
theorem continuous_clockDensity (hcont : Continuous (hε ε)) (b : ContinuousPath ℂ) :
    Continuous fun s : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal)) :=
  continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
    (hcont.comp (b.continuous.comp continuous_real_toNNReal))))

/-- The density of the approximate clock is interval integrable for Lebesgue measure. -/
theorem intervalIntegrable_clockDensity (hcont : Continuous (hε ε)) (b : ContinuousPath ℂ) (a c : ℝ) :
    IntervalIntegrable (fun s : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal))) volume a c :=
  (continuous_clockDensity hcont b).intervalIntegrable a c

/-- The approximate clock is continuous in time. -/
theorem continuous_lqgClockApprox_time (hcont : Continuous (hε ε)) (b : ContinuousPath ℂ) :
    Continuous fun t : ℝ≥0 => lqgClockApprox γ hε ε b t :=
  (intervalIntegral.continuous_primitive
    (fun a c => intervalIntegrable_clockDensity hcont b a c) 0).comp NNReal.continuous_coe

/-- The approximate clock of a positive density is strictly increasing in time. -/
theorem strictMono_lqgClockApprox (hε0 : 0 < ε) (hcont : Continuous (hε ε)) (b : ContinuousPath ℂ) :
    StrictMono fun t : ℝ≥0 => lqgClockApprox γ hε ε b t := by
  intro t₁ t₂ h
  have hlt : (t₁ : ℝ) < t₂ := NNReal.coe_lt_coe.2 h
  have hpos : (0 : ℝ) < ∫ s in (t₁ : ℝ)..(t₂ : ℝ), ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (intervalIntegrable_clockDensity hcont b _ _)
      (fun s _ => mul_pos (Real.rpow_pos_of_pos hε0 _) (Real.exp_pos _)) hlt
  have hsub := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_clockDensity (γ := γ) hcont b (0 : ℝ) (t₂ : ℝ))
    (intervalIntegrable_clockDensity (γ := γ) hcont b (0 : ℝ) (t₁ : ℝ))
  unfold lqgClockApprox
  linarith

/-- The approximate clock is jointly measurable in the path and the time (Carathéodory: continuous in time, measurable in the
path). -/
theorem measurable_lqgClockApprox_pair (hcont : Continuous (hε ε)) :
    Measurable fun q : ContinuousPath ℂ × ℝ≥0 => lqgClockApprox γ hε ε q.1 q.2 :=
  (measurable_uncurry_of_continuous_of_measurable (u := fun (t : ℝ≥0) (b : ContinuousPath ℂ) =>
      lqgClockApprox γ hε ε b t)
    (fun b => continuous_lqgClockApprox_time hcont b)
    (fun t => measurable_lqgClockApprox hcont t)).comp measurable_swap

/-- The cutoff approximate inverse of the approximate clock is jointly measurable in the path and the time. -/
theorem measurable_cutInv_lqgClockApprox (hε0 : 0 < ε) (hcont : Continuous (hε ε)) (n : ℝ≥0) :
    Measurable fun q : ContinuousPath ℂ × ℝ≥0 =>
      cutInv (fun s : ℝ≥0 => lqgClockApprox γ hε ε q.1 s) n q.2 :=
  measurable_cutInv (C := fun (b : ContinuousPath ℂ) (s : ℝ≥0) => lqgClockApprox γ hε ε b s)
    (fun b => (strictMono_lqgClockApprox hε0 hcont b).monotone)
    (measurable_lqgClockApprox_pair hcont) n

/-- The evaluations `b ↦ b (cutInv (clock b) n u)` of the time-changed approximate path at a fixed time are measurable in the
path. -/
theorem measurable_approxPath_eval (hε0 : 0 < ε) (hcont : Continuous (hε ε)) (n u : ℝ≥0) :
    Measurable fun b : ContinuousPath ℂ =>
      b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ hε ε b s) n u) := by
  have hτ : Measurable fun b : ContinuousPath ℂ =>
      cutInv (fun s : ℝ≥0 => lqgClockApprox γ hε ε b s) n u :=
    (measurable_cutInv_lqgClockApprox hε0 hcont n).comp (measurable_id.prodMk measurable_const)
  exact measurable_path_eval_pair.comp (measurable_id.prodMk hτ)

/-- The time-changed approximate path `t ↦ b (cutInv (clock b) n (m t))` is continuous in the time variable. -/
theorem continuous_approxPath (hε0 : 0 < ε) (hcont : Continuous (hε ε)) (b : ContinuousPath ℂ) (n m : ℝ≥0) :
    Continuous fun t : ℝ≥0 => b (cutInv (fun s : ℝ≥0 => lqgClockApprox γ hε ε b s) n (m * t)) :=
  b.continuous.comp ((continuous_cutInv (strictMono_lqgClockApprox hε0 hcont b)
    (continuous_lqgClockApprox_time hcont b) n).comp (continuous_const.mul continuous_id))

end

end MatedCRT
