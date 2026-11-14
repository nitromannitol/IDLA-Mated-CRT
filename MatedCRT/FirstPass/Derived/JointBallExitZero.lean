import MatedCRT.FirstPass.Derived.JointBallExitBoundary

/-! # Joint ball-exit continuity at the zero-radius boundary -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal InnerProductSpace

namespace MatedCRT.StopAtExitCmp

/-- Arbitrarily early nonzero values give joint exit-time continuity at radius zero. -/
theorem continuousAt_planarBall_exitTime_joint_zero {b : ContinuousPath ℂ}
    (h : ∃ᶠ t in 𝓝[>] (0 : ℝ≥0), b t ≠ 0) :
    ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
      ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) (b, 0) := by
  have hτ : ContinuousPath.exitTime (ball (0 : ℂ) (0 : ℝ)) b = 0 := by
    apply le_antisymm
    · simpa using ContinuousPath.exitTime_le_of_notMem (ball (0 : ℂ) (0 : ℝ)) b 0
        (by simp)
    · exact zero_le
  rw [ContinuousAt, tendsto_order]
  constructor
  · intro a ha
    rw [hτ] at ha
    exact (not_lt_of_ge zero_le ha).elim
  · intro a ha
    rw [hτ] at ha
    obtain ⟨s, hs0, hsa⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    have hs0' : (0 : ℝ≥0) < s := by exact_mod_cast hs0
    obtain ⟨t, ht, hts⟩ := (h.and_eventually (Ioo_mem_nhdsGT hs0')).exists
    have ht' : (0 : ℝ) < dist (b t) 0 := dist_pos.mpr ht
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

/-- Brownian ball-exit time is jointly continuous at the zero-radius boundary almost surely. -/
theorem ae_continuousAt_planarBall_exitTime_joint_zero :
    ∀ᵐ b ∂planarBrownianMotion 0,
      ContinuousAt (fun p : ContinuousPath ℂ × ℝ =>
        ContinuousPath.exitTime (ball (0 : ℂ) p.2) p.1) (b, 0) := by
  have hfin : ∀ᵐ b ∂planarBrownianMotion 0,
      ContinuousPath.exitTime (ball (0 : ℂ) (0 : ℝ)) b ≠ ⊤ :=
    (HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top 0
      (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) (0 : ℝ)))).mono fun _ hb => hb.ne
  obtain ⟨hW, _, _⟩ := ExitRestart.exit_restart_planar isOpen_ball 0 hfin
  have hBlum := fun A hA =>
    LatticeProb.PlanarBrownian.isTrivialSigma_iInf_pathSigmaTo_planar hW
      (LatticeProb.isTrivialSigma_iInf_bmPast hW.re fun t => Complex.measurable_re.comp (hW.measurable t))
      (LatticeProb.isTrivialSigma_iInf_bmPast hW.im fun t => Complex.measurable_im.comp (hW.measurable t)) A hA
  have hfreq := LatticeProb.PlanarBrownian.ae_frequently_pos_of_indepFun hW hBlum
    (N := fun _ => (1 : ℂ)) aemeasurable_const (indepFun_const_left (1 : ℂ) _)
      (Filter.Eventually.of_forall fun _ => one_ne_zero)
  filter_upwards [hfreq, ae_planarBrownianMotion_eval_zero 0] with b hb hb0
  have hτ : ContinuousPath.exitTime (ball (0 : ℂ) (0 : ℝ)) b = 0 := by
    apply le_antisymm
    · simpa using ContinuousPath.exitTime_le_of_notMem (ball (0 : ℂ) (0 : ℝ)) b 0
        (by simp)
    · exact zero_le
  have hexc : ∃ᶠ t in 𝓝[>] (0 : ℝ≥0), 0 < ⟪(1 : ℂ), b t⟫_ℝ := by
    simpa only [ExitRestart.exitNN, hτ, ENNReal.toNNReal_zero, zero_add, hb0, sub_zero,
      LatticeProb.PlanarBrownian.inner_eq_pairing] using hb
  apply continuousAt_planarBall_exitTime_joint_zero
  exact hexc.mono fun t ht hzero => by simp only [hzero, inner_zero_right, lt_self_iff_false] at ht

end MatedCRT.StopAtExitCmp
