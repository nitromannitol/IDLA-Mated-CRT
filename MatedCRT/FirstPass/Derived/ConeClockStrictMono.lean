import MatedCRT.FirstPass.Derived.ConeClockUniformCauchy
import MatedCRT.FirstPass.Derived.ConeReferenceClockLocalChain
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxPathMeasurable
import LatticeProb.Prob.LimitAfterPositiveTimesShift

/-!
# Strict monotonicity of the cone clock from that of the whole-plane clock

The approximating cone clock at scale `ε` is the whole-plane clock density integrated against the
cone weight `exp(γ (-γ log max(|z|, ε) + ⨍_{∂B_ε(z)} coneRefField))` (`lqgClockApprox_coneRefCircle`).
For `γ ≥ 0`, along a path that stays in `closedBall 0 M` up to time `N`, this weight is bounded below
by `exp(γ (-γ log (M + 1) + m))` at every scale `ε ≤ 1`, where `m` is a lower bound of the continuous
function `coneRefField` on `closedBall 0 (M + 1)`; no condition at the origin is needed, since the
logarithmic term only increases the weight there. Hence the increments of the cone clocks dominate a
fixed positive multiple of those of the whole-plane clocks at every dyadic scale.

When the dyadic clocks are uniformly Cauchy on every `[0, N]`, the limit after positive times is
their pointwise limit (`tendsto_limitAfterPositiveTimes_of_uniformCauchySeqOn`), so the comparison
passes to the limit: strict monotonicity of the limiting whole-plane clock implies that of the
limiting cone clock. Together with the local-to-global uniform Cauchy property
(`ae_uniformCauchySeqOn_lqgClockApprox_of_local`) this transfers the almost sure strict monotonicity
from Lebesgue-almost every start.

## Main statements

* `tendsto_limitAfterPositiveTimes_of_uniformCauchySeqOn`;
* `exists_pos_mul_sub_le_coneRefCircle_clock`;
* `strictMono_limitAfterPositiveTimes_coneRefCircle`;
* `ae_strictMono_limitAfterPositiveTimes_coneRefCircle_of_local`.
-/

noncomputable section

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Filter HarmonicBalls MarkovProcess
open scoped NNReal Topology

/-- **The limit after positive times as a pointwise limit.** If continuous functions `a k` vanishing
at `0` are uniformly Cauchy on every `[0, N]`, then `a k t` converges to the limit after positive
times at every time `t`. -/
theorem tendsto_limitAfterPositiveTimes_of_uniformCauchySeqOn {a : ℕ → ℝ≥0 → ℝ}
    (hcont : ∀ k, Continuous (a k)) (h0 : ∀ k, a k 0 = 0)
    (hU : ∀ N : ℕ, UniformCauchySeqOn a atTop (Icc 0 (N : ℝ≥0))) (t : ℝ≥0) :
    Tendsto (fun k => a k t) atTop (𝓝 (LatticeProb.limitAfterPositiveTimes a t)) := by
  have hcs : ∀ t : ℝ≥0, CauchySeq fun k => a k t := fun t =>
    (hU ⌈(t : ℝ≥0)⌉₊).cauchySeq ⟨zero_le, Nat.le_ceil t⟩
  choose G hG using fun t => cauchySeq_tendsto_of_complete (hcs t)
  have hG0 : G 0 = 0 := tendsto_nhds_unique (hG 0) (by simp [h0])
  have hU1 : UniformCauchySeqOn a atTop (Icc 0 1) := by simpa using hU 1
  have hunif : TendstoUniformlyOn a G atTop (Icc 0 1) :=
    hU1.tendstoUniformlyOn_of_tendsto fun x _ => hG x
  have hGc : ContinuousOn G (Icc 0 1) :=
    hunif.continuousOn (Eventually.of_forall fun k => (hcont k).continuousOn).frequently
  have hnhds : Icc (0 : ℝ≥0) 1 ∈ 𝓝 (0 : ℝ≥0) :=
    mem_of_superset (Iio_mem_nhds zero_lt_one) fun x hx => ⟨zero_le, le_of_lt hx⟩
  rw [LatticeProb.limitAfterPositiveTimes_eq_sub_of_tendsto hG
    (hGc.continuousAt hnhds).continuousWithinAt t, hG0, sub_zero]
  exact hG t

/-- **Comparison of the cone and whole-plane clock increments.** For `γ ≥ 0`, circle averages
`hcirc` jointly continuous at positive radii, a path `b` and a horizon `N`, there is `c > 0` such
that at every dyadic scale and for all `s ≤ t ≤ N`, the increment of the cone clock over `[s, t]`
is at least `c` times that of the whole-plane clock. -/
theorem exists_pos_mul_sub_le_coneRefCircle_clock (γ : ℝ) (hγ : 0 ≤ γ) {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (w : ContinuousPath ℝ)
    (b : ContinuousPath ℂ) (N : ℝ≥0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (s t : ℝ≥0), s ≤ t → t ≤ N →
      c * (lqgClockApprox γ hcirc (HarmonicBalls.dyadicScale k) b t -
          lqgClockApprox γ hcirc (HarmonicBalls.dyadicScale k) b s) ≤
        lqgClockApprox γ (coneRefCircle γ hcirc w) (HarmonicBalls.dyadicScale k) b t -
          lqgClockApprox γ (coneRefCircle γ hcirc w) (HarmonicBalls.dyadicScale k) b s := by
  have hc0 : ContinuousOn (fun ρ => hcirc ρ 0) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn fun ρ hρ => ⟨hρ, mem_univ _⟩
  have hF : Continuous (coneRefField hcirc w) := continuous_coneRefField hc0 w
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := N)).bddAbove_image
    (continuous_norm.comp b.continuous).continuousOn
  have hM' : ∀ u ∈ Icc (0 : ℝ≥0) N, ‖b u‖ ≤ M := fun u hu => hM ⟨u, hu, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM' 0 ⟨le_rfl, zero_le⟩)
  obtain ⟨m, hm⟩ := (isCompact_closedBall (0 : ℂ) (M + 1)).bddBelow_image hF.continuousOn
  have hm' : ∀ z ∈ Metric.closedBall (0 : ℂ) (M + 1), m ≤ coneRefField hcirc w z :=
    fun z hz => hm ⟨z, hz, rfl⟩
  refine ⟨Real.exp (γ * (-γ * Real.log (M + 1) + m)), Real.exp_pos _, ?_⟩
  intro k s t hst htN
  have hε : 0 < HarmonicBalls.dyadicScale k := HarmonicBalls.dyadicScale_pos k
  have hε1 : HarmonicBalls.dyadicScale k ≤ 1 := by
    unfold HarmonicBalls.dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  set ε := HarmonicBalls.dyadicScale k with hε_def
  have hf := continuous_lqgClockDensity_path γ hc hε b
  have hw := (continuous_coneClockWeight_path hF γ b hε one_pos).1
  have hfw : Continuous fun u : ℝ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε (b u.toNNReal)) *
        Real.exp (γ * (-γ * Real.log (max ‖b u.toNNReal‖ ε) +
          Real.circleAverage (coneRefField hcirc w) (b u.toNNReal) ε)) := hf.mul hw
  rw [lqgClockApprox_coneRefCircle γ hcirc w hε b t, lqgClockApprox_coneRefCircle γ hcirc w hε b s]
  unfold lqgClockApprox
  rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _),
    intervalIntegral.integral_interval_sub_left (hfw.intervalIntegrable _ _)
      (hfw.intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by exact_mod_cast hst)
    ((hf.const_mul _).intervalIntegrable _ _) (hfw.intervalIntegrable _ _) ?_
  intro u hu
  have hu0 : (0 : ℝ) ≤ u := (NNReal.coe_nonneg s).trans hu.1
  have huN : u.toNNReal ∈ Icc (0 : ℝ≥0) N :=
    ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 (hu.2.trans (by exact_mod_cast htN))⟩
  have hz : ‖b u.toNNReal‖ ≤ M := hM' _ huN
  have hd0 := lqgClockDensity_nonneg γ hcirc hε (b u.toNNReal)
  rw [mul_comm (Real.exp _) _]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hγ)) hd0
  refine add_le_add ?_ ?_
  · have hlog : Real.log (max ‖b u.toNNReal‖ ε) ≤ Real.log (M + 1) :=
      Real.log_le_log (lt_max_of_lt_right hε) (max_le (by linarith) (by linarith))
    have := mul_le_mul_of_nonneg_left hlog hγ
    linarith
  · rw [← Real.circleAverage_const m (b u.toNNReal) ε]
    refine Real.circleAverage_mono (continuousOn_const.circleIntegrable')
      (hF.continuousOn.circleIntegrable') fun x hx => hm' x ?_
    rw [Metric.mem_sphere, abs_of_pos hε] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖x‖ ≤ ‖x - b u.toNNReal‖ + ‖b u.toNNReal‖ := norm_le_norm_sub_add x _
      _ ≤ 1 + M := add_le_add (by rw [← dist_eq_norm, hx]; exact hε1) hz
      _ = M + 1 := add_comm _ _

/-- **Strict monotonicity of the limiting cone clock along a path.** For `γ ≥ 0`, circle averages
`hcirc` jointly continuous at positive radii and a path `b` along which the dyadic whole-plane and
cone clocks are uniformly Cauchy on every `[0, N]`, if the limiting whole-plane clock is strictly
increasing then so is the limiting cone clock. -/
theorem strictMono_limitAfterPositiveTimes_coneRefCircle (γ : ℝ) (hγ : 0 ≤ γ)
    {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (w : ContinuousPath ℝ)
    {b : ContinuousPath ℂ}
    (hA : ∀ N : ℕ, UniformCauchySeqOn
      (fun k t => lqgClockApprox γ hcirc (HarmonicBalls.dyadicScale k) b t) atTop
      (Icc 0 (N : ℝ≥0)))
    (hC : ∀ N : ℕ, UniformCauchySeqOn
      (fun k t => lqgClockApprox γ (coneRefCircle γ hcirc w) (HarmonicBalls.dyadicScale k) b t)
      atTop (Icc 0 (N : ℝ≥0)))
    (hsm : StrictMono (LatticeProb.limitAfterPositiveTimes
      fun k t => lqgClockApprox γ hcirc (HarmonicBalls.dyadicScale k) b t)) :
    StrictMono (LatticeProb.limitAfterPositiveTimes
      fun k t => lqgClockApprox γ (coneRefCircle γ hcirc w) (HarmonicBalls.dyadicScale k) b t) := by
  intro s t hst
  obtain ⟨c, hc0, hcmp⟩ := exists_pos_mul_sub_le_coneRefCircle_clock γ hγ hc w b t
  have hcontA : ∀ k : ℕ, Continuous (hcirc (HarmonicBalls.dyadicScale k)) := fun k =>
    hc.comp_continuous (continuous_const.prodMk continuous_id)
      fun _ => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  have hcontC : ∀ k : ℕ,
      Continuous (coneRefCircle γ hcirc w (HarmonicBalls.dyadicScale k)) := fun k =>
    (continuousOn_coneRefCircle γ hc w).comp_continuous
      (continuous_const.prodMk continuous_id)
      fun _ => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  have hTA := tendsto_limitAfterPositiveTimes_of_uniformCauchySeqOn
    (fun k => MatedCRT.continuous_lqgClockApprox_time (γ := γ) (hcontA k) b)
    (fun k => by simp [lqgClockApprox]) hA
  have hTC := tendsto_limitAfterPositiveTimes_of_uniformCauchySeqOn
    (fun k => MatedCRT.continuous_lqgClockApprox_time (γ := γ) (hcontC k) b)
    (fun k => by simp [lqgClockApprox]) hC
  have hle := le_of_tendsto_of_tendsto' (((hTA t).sub (hTA s)).const_mul c)
    ((hTC t).sub (hTC s)) fun k => hcmp k s t hst.le le_rfl
  have hpos := mul_pos hc0 (sub_pos.2 (hsm hst))
  exact sub_pos.1 (hpos.trans_le hle)

/-- **Almost sure strict monotonicity of the limiting cone clock from almost every start.** For
`γ ≥ 0` and circle averages `hcirc` jointly continuous at positive radii, if the dyadic whole-plane
clocks are locally uniformly Cauchy on discs avoiding the origin from Lebesgue-almost every start,
and the limiting whole-plane clock is almost surely strictly increasing from Lebesgue-almost every
start, then so is the limiting cone clock. -/
theorem ae_strictMono_limitAfterPositiveTimes_coneRefCircle_of_local (γ : ℝ) (hγ : 0 ≤ γ)
    {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (w : ContinuousPath ℝ)
    (hpolar : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), ∀ t, b t ≠ 0)
    (hloc : ∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ →
      ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
        (∀ t ∈ Icc 0 h, b t ∈ Metric.closedBall a r) →
        UniformCauchySeqOn
          (fun k t => lqgClockApprox γ hcirc (HarmonicBalls.dyadicScale k) b t) atTop (Icc 0 h))
    (hsm : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
      StrictMono (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ hcirc (HarmonicBalls.dyadicScale k) b t)) :
    ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
      StrictMono (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ (coneRefCircle γ hcirc w) (HarmonicBalls.dyadicScale k) b t) := by
  have hcontA : ∀ k : ℕ, Continuous (hcirc (HarmonicBalls.dyadicScale k)) := fun k =>
    hc.comp_continuous (continuous_const.prodMk continuous_id)
      fun _ => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  have hcontC : ∀ k : ℕ,
      Continuous (coneRefCircle γ hcirc w (HarmonicBalls.dyadicScale k)) := fun k =>
    (continuousOn_coneRefCircle γ hc w).comp_continuous
      (continuous_const.prodMk continuous_id)
      fun _ => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  have hA : ∀ᵐ y ∂(volume : Measure ℂ), ∀ N : ℕ, ∀ᵐ b ∂(planarBrownianMotion y),
      UniformCauchySeqOn (fun k t => lqgClockApprox γ hcirc (HarmonicBalls.dyadicScale k) b t)
        atTop (Icc 0 (N : ℝ≥0)) :=
    ae_all_iff.2 fun N => ae_uniformCauchySeqOn_lqgClockApprox_of_local hcontA hpolar hloc N
  have hC : ∀ᵐ y ∂(volume : Measure ℂ), ∀ N : ℕ, ∀ᵐ b ∂(planarBrownianMotion y),
      UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (coneRefCircle γ hcirc w) (HarmonicBalls.dyadicScale k) b t)
        atTop (Icc 0 (N : ℝ≥0)) :=
    ae_all_iff.2 fun N => ae_uniformCauchySeqOn_lqgClockApprox_of_local hcontC hpolar
      (coneRefCircle_localUniformCauchy γ hc w hloc) N
  filter_upwards [hA, hC, hsm] with y hAy hCy hsmy
  filter_upwards [ae_all_iff.2 hAy, ae_all_iff.2 hCy, hsmy] with b hAb hCb hsmb
  exact strictMono_limitAfterPositiveTimes_coneRefCircle γ hγ hc w hAb hCb hsmb

end MatedCRT.FirstPass.Derived
