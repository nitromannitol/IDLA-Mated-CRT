import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkExitMeasurable
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkFunctionalConvergence
import MatedCRT.Proofs.LBM.AlmostSureRegularExit
import MatedCRT.Proofs.LBM.BrownianExitBall
import MatedCRT.Proofs.LBM.TimeChangeContinuity

/-!
# Killed per-test convergence of the walk (E-c2-9)

For a continuous test `g : ℂ → ℝ` that is bounded and Hölder on the ball `ball z r`, the killed occupation functional
`truncatedOccupationFunctional (ball z r) g T` of the interpolated walk converges in probability to its value on the
rescaled LBM path. This is `walkFunctional_tendstoInProbability_of_ae_continuousWithin` with the walk-side
measurability of `WalkExitMeasurable.lean`, the a.s. regular exit and finiteness of the LBM exit time (from the existing
Brownian excursion hypothesis `BrownianOutwardExcursionAtExitStep`), and the continuity of the killed functional at
regular exits.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The killed occupation functional of a test bounded by `M` is bounded by `M T` on any path. -/
theorem abs_truncatedOccupationFunctional_le {D : Set ℂ} {g : ℂ → ℝ} {M T : ℝ} (hM0 : 0 ≤ M) (hT : 0 ≤ T)
    (hgM : ∀ x, |g x| ≤ M) (w : ℝ≥0 → ℂ) :
    |truncatedOccupationFunctional D g T w| ≤ M * T := by
  unfold truncatedOccupationFunctional
  have ha0 : 0 ≤ min T (pathExitTime D w).toReal := le_min hT ENNReal.toReal_nonneg
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Ioc (0 : ℝ) (min T (pathExitTime D w).toReal)) (C := M)
    (f := fun t : ℝ => g (w t.toNNReal))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun t _ => hgM _)
  rw [Real.norm_eq_abs, Real.volume_real_Ioc_of_le ha0, sub_zero] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hM0)

/-- A path whose exit time from `U` is finite leaves `U`. -/
theorem exists_not_mem_of_pathExitTime_lt_top {U : Set ℂ} {w : ℝ≥0 → ℂ} (h : pathExitTime U w < ⊤) :
    ∃ t, w t ∉ U := by
  by_contra hcon
  have hempty : {c : ℝ≥0∞ | ∃ t : ℝ≥0, c = (t : ℝ≥0∞) ∧ w t ∉ U} = ∅ := by
    ext c
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨t, -, ht⟩
    exact hcon ⟨t, ht⟩
  have htop : pathExitTime U w = ⊤ := by
    unfold pathExitTime
    rw [hempty, sInf_empty]
  rw [htop] at h
  exact lt_irrefl _ h

/-- **Killed per-test convergence of the walk.** For a continuous test `g`, bounded by `M` and Hölder on the ball,
the killed occupation functional of the interpolated walk converges in probability to its value on the rescaled
LBM path (Theorem 2.11 for a path functional continuous at regular exits). -/
theorem truncatedOccupation_tendstoInProbability_of_holder {𝒮 : SpaceFillingSLEModel}
    (h211 : RandomWalkToLBMStmt 𝒮) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (hm : 0 < S.m₀)
    {z : ℂ} {r : ℝ} (hr : 0 < r) {g : ℂ → ℝ} (hg : Continuous g) {M : ℝ} (hgM : ∀ x, |g x| ≤ M)
    {C χ : ℝ≥0} (hχ : 0 < χ) (hhol : HolderOnWith C χ g (Metric.ball z r)) {T : ℝ} (hT : 0 ≤ T) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, truncatedOccupationFunctional (Metric.ball z r) g T (interpolatedWalk ε (S.η ω) (S.mε ε) x)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z))
      (fun ω => ∫ b, truncatedOccupationFunctional (Metric.ball z r) g T (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion z) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgM 0)
  have hz : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hM : ∀ w : ℝ≥0 → ℂ, Continuous w →
      |truncatedOccupationFunctional (Metric.ball z r) g T w| ≤ M * T :=
    fun w _ => abs_truncatedOccupationFunctional_le hM0 hT hgM w
  have hGW : ∀ (ε : ℝ) (ω : Ω), AEStronglyMeasurable
      (fun x => truncatedOccupationFunctional (Metric.ball z r) g T (interpolatedWalk ε (S.η ω) (S.mε ε) x))
      (srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z)) := fun ε ω =>
    aestronglyMeasurable_truncatedOccupation_interpolatedWalk ε (S.η ω) (S.mε ε) z r T hg
  have hclock := hS.isLQGClock
  have hreg := hS.ae_rescaledLBM_ball_regular_of_brownian_outward_radial_excursion hm hz (hexc z z r hz)
  have hfin := hS.ae_rescaledLBMExitTime_any_ball_lt_top hm z z r
  have hcl : closure (Metric.ball z r) = Metric.closedBall z r := closure_ball z hr.ne'
  have hcont : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion z,
      rescaledLBMPath (S.clock ω) S.m₀ b ∈ {w : ℝ≥0 → ℂ | Continuous w} ∧
        PathFunctionalContinuousWithinAt {w : ℝ≥0 → ℂ | Continuous w}
          (truncatedOccupationFunctional (Metric.ball z r) g T) (rescaledLBMPath (S.clock ω) S.m₀ b) := by
    filter_upwards [hclock, hreg, hfin] with ω hω hreg_ω hfin_ω
    filter_upwards [(hω z).2, hreg_ω, hfin_ω] with b hb hregb hfinb
    have hcb : Continuous (rescaledLBMPath (S.clock ω) S.m₀ b) := continuous_rescaledLBMPath hb
    refine ⟨hcb, ?_⟩
    have hfin' : ContinuousPath.exitTime (Metric.ball z r) (⟨_, hcb⟩ : ContinuousPath ℂ) < ⊤ :=
      (ContinuousPath.exitTime_lt_top_iff _ _).2 (exists_not_mem_of_pathExitTime_lt_top hfinb)
    have hreg' : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (Metric.ball z r) (⟨_, hcb⟩ : ContinuousPath ℂ)).toNNReal,
        (⟨_, hcb⟩ : ContinuousPath ℂ) t ∉ Metric.closedBall z r := by
      refine hregb.mono fun t ht => ?_
      rw [← hcl]
      exact ht
    exact pathFunctionalContinuousWithinAt_truncatedOccupation (⟨_, hcb⟩ : ContinuousPath ℂ) z hfin' hreg'
      (fun x _ => hgM x) hχ hhol hT
  exact walkFunctional_tendstoInProbability_of_ae_continuousWithin 𝒮 h211 hX hγ hγ2 S hS z
    (truncatedOccupationFunctional (Metric.ball z r) g T) (M * T) hM hGW hcont

end MatedCRT
