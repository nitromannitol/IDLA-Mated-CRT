import MatedCRT.FirstPass.Derived.JointBallExitContinuity
import MatedCRT.FirstPass.Derived.BrownianRegularExitSquare

/-! # Joint ball-exit continuity at positive-radius boundary starts -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal InnerProductSpace

namespace MatedCRT.StopAtExitCmp

/-- Brownian exit time from a ball is jointly continuous in path and radius almost surely
when the starting point lies on its positive-radius boundary. -/
theorem ae_continuousAt_planarBall_exitTime_joint_of_boundary {x : ℂ} {r : ℝ}
    (hr : 0 < r) (hx : dist x 0 = r) :
    ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
        ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) (b, r) := by
  have hx0 : x ≠ 0 := by
    intro h
    simp only [h, dist_self] at hx
    linarith
  have hfin : ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousPath.exitTime (ball (0 : ℂ) r) b ≠ ⊤ :=
    (HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top x
      (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) r))).mono fun _ hb => hb.ne
  obtain ⟨hW, _, _⟩ := ExitRestart.exit_restart_planar isOpen_ball x hfin
  have hBlum := fun A hA =>
    LatticeProb.PlanarBrownian.isTrivialSigma_iInf_pathSigmaTo_planar hW
      (LatticeProb.isTrivialSigma_iInf_bmPast hW.re fun t => Complex.measurable_re.comp (hW.measurable t))
      (LatticeProb.isTrivialSigma_iInf_bmPast hW.im fun t => Complex.measurable_im.comp (hW.measurable t)) A hA
  have hfreq := LatticeProb.PlanarBrownian.ae_frequently_pos_of_indepFun hW hBlum
    (N := fun _ => x) aemeasurable_const (indepFun_const_left x _) (Filter.Eventually.of_forall fun _ => hx0)
  filter_upwards [hfreq, ae_planarBrownianMotion_eval_zero x] with b hb hb0
  have hτ : ContinuousPath.exitTime (ball (0 : ℂ) r) b = 0 := by
    apply le_antisymm
    · simpa using ContinuousPath.exitTime_le_of_notMem (ball (0 : ℂ) r) b 0
        (by simp only [mem_ball, not_lt, hb0, hx, le_refl])
    · exact zero_le
  have hsphere : b 0 ∈ sphere (0 : ℂ) r := by simpa only [mem_sphere, hb0] using hx
  have hexc : ∃ᶠ t in 𝓝[>] (0 : ℝ≥0), 0 < ⟪b 0 - 0, b t - b 0⟫_ℝ := by
    simpa only [ExitRestart.exitNN, hτ, ENNReal.toNNReal_zero, zero_add, hb0, sub_zero,
      LatticeProb.PlanarBrownian.inner_eq_pairing] using hb
  have hτ' : pathExitTime (ball (0 : ℂ) r) b = 0 := hτ
  apply continuousAt_planarBall_exitTime_joint hr (by rw [hτ']; exact bot_ne_top)
  simpa only [hτ', ENNReal.toNNReal_zero] using
    (frequently_outside_closedBall_of_outward_radial_excursion hsphere hexc).mono
      (fun _ ht hmem => ht (closure_ball_subset_closedBall hmem))

end MatedCRT.StopAtExitCmp
