import MatedCRT.FirstPass.Derived.LBMApproxRestart
import MatedCRT.FirstPass.Derived.UniformStartStoppedBM
import LatticeProb.Prob.PathSpaceDUnif

/-!
# The restarted approximate Liouville Brownian path in the metric `dUnif`

Let `A_n = lqgApproxClockPlus γ hε n` be the approximating LQG clock with drift at the dyadic scale
`2^{-n}` and `Φ_n = lbmContinuousPath A_n` the time-changed path map. For `δ ≥ 0` write
`θ_δ b = b (δ + ·)`, `c_n(b) = A_n(b, δ)` and `T_c y = y ((· - c)⁺)`.

* `dUnif_lbmContinuousPath_continuousPathDelay_le`: if `b` oscillates by at most `η` on `[0, δ]`
  (relative to `b δ`), then for every `T₀ ≥ 0`,
  `dUnif (Φ_n b) (T_{c_n(b)} Φ_n (θ_δ b)) ≤ T₀ η + e^{-T₀}`; this holds for every clock additive at `δ`.
* `integral_min_dUnif_lbmContinuousPath_lqgApproxClockPlus_delay_le`: for `L ≥ 0`, `ρ ≥ 0`, `T₀ ≥ 0`
  and every start `z`,
  `E^z min(2, L dUnif(Φ_n b, T_{c_n} Φ_n(θ_δ b))) ≤ L (2 T₀ ρ + e^{-T₀}) + 2 P^0(τ_{B(0,ρ)} ≤ δ)`.
* `eventually_integral_min_dUnif_lbmContinuousPath_lqgApproxClockPlus_delay_le`: for `L ≥ 0` and
  `ε > 0`, for all small `δ > 0` the left side is at most `ε`, uniformly in the level `n` and in the
  start `z`.

This is the term `m_L(δ)` in the comparison of the laws of the approximate Liouville Brownian paths
from two starting points through the restart at the fixed time `δ` (Garban–Rhodes–Vargas,
*Liouville Brownian motion*, Ann. Probab. 44 (2016), proof of Proposition 2.19).
-/

open MeasureTheory ProbabilityTheory Set MarkovProcess Filter Topology Metric
open _root_.HarmonicBalls MatedCRT.StopAtExitCmp
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- The continuous path `y` delayed by the time `c`: `(T_c y)(t) = y ((t - c)⁺)`. By definition
this is the path delay `LatticeProb.pathDelay c y` of the path-space library. -/
noncomputable def continuousPathDelay (c : ℝ≥0) (y : ContinuousPath ℂ) : ContinuousPath ℂ :=
  y.comp ⟨fun t => t - c, continuous_id.sub continuous_const⟩

@[simp] theorem continuousPathDelay_apply (c : ℝ≥0) (y : ContinuousPath ℂ) (t : ℝ≥0) :
    continuousPathDelay c y t = y (t - c) := rfl

section Path

variable {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} {δ : ℝ≥0}

/-- **The delayed restarted path in `dUnif`.** Under clock additivity at `δ`, if `b` oscillates by
at most `η` on `[0, δ]` (relative to `b δ`), then for every `T₀ ≥ 0` the time-changed path of `b`
and the time-changed path of `θ_δ b` delayed by `F b δ` are within `T₀ η + e^{-T₀}` in `dUnif`. -/
theorem dUnif_lbmContinuousPath_continuousPathDelay_le (hF : IsTimeChangeClock (F b))
    (hadd : ∀ s, F (ContinuousPath.shift δ b) s = F b (δ + s) - F b δ) {η : ℝ}
    (hosc : ∀ r ≤ δ, ‖b r - b δ‖ ≤ η) (T0 : ℝ≥0) :
    LatticeProb.dUnif (lbmContinuousPath F b)
        (continuousPathDelay (F b δ).toNNReal (lbmContinuousPath F (ContinuousPath.shift δ b))) ≤
      T0 * η + Real.exp (-(T0 : ℝ)) :=
  LatticeProb.dUnif_le_of_forall_dist_le T0 fun t _ => by
    rw [dist_eq_norm]
    exact norm_lbmContinuousPath_sub_pathDelay_le hF hadd hosc t

end Path

/-- If the translate `b - z` has not left the disc `B(0, ρ)` by time `δ`, then `b` oscillates by at
most `2ρ` on `[0, δ]` relative to `b δ`. -/
theorem norm_sub_le_of_not_exitTime_translatePath_le {z : ℂ} {ρ : ℝ} {δ : ℝ≥0}
    {b : ContinuousPath ℂ}
    (hb : ¬ ContinuousPath.exitTime (ball (0 : ℂ) ρ) (translatePath (-z) b) ≤ δ) :
    ∀ r ≤ δ, ‖b r - b δ‖ ≤ 2 * ρ := by
  have hlt : ∀ s ≤ δ, ‖b s - z‖ < ρ := fun s hs => by
    have hmem := ContinuousPath.mem_of_lt_exitTime (ball (0 : ℂ) ρ) (translatePath (-z) b) s
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (not_le.1 hb))
    simpa [translatePath_apply, mem_ball, dist_zero_right, sub_eq_add_neg] using hmem
  intro r hr
  calc ‖b r - b δ‖ = ‖(b r - z) - (b δ - z)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖b r - z‖ + ‖b δ - z‖ := norm_sub_le _ _
    _ ≤ 2 * ρ := by linarith [hlt r hr, hlt δ le_rfl]

/-- Translation invariance of the exit probability: under `P^z`, the translate `b - z` leaves
`B(0, ρ)` by time `δ` with the probability that planar Brownian motion from `0` does. -/
theorem planarBrownianMotion_exitTime_translatePath_neg_le (z : ℂ) (ρ : ℝ) (δ : ℝ≥0) :
    planarBrownianMotion z
        {b : ContinuousPath ℂ | ContinuousPath.exitTime (ball (0 : ℂ) ρ) (translatePath (-z) b) ≤ δ} =
      planarBrownianMotion (0 : ℂ)
        {b : ContinuousPath ℂ | ContinuousPath.exitTime (ball (0 : ℂ) ρ) b ≤ δ} := by
  rw [planarBrownianMotion_apply_eq_translatePath]
  congr 1
  ext b
  have hb : translatePath (-z) (translatePath z b) = b :=
    ContinuousMap.ext fun s => by simp [translatePath_apply]
  simp only [mem_preimage, mem_ofPred_eq, hb]

/-- The probability `P^0(τ_{B(0,ρ)} ≤ δ)` that planar Brownian motion from `0` leaves the disc of
radius `ρ > 0` by time `δ` tends to `0` as `δ ↓ 0`. -/
theorem tendsto_planarBrownianMotion_exitTime_ball_le {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun δ : ℝ≥0 => planarBrownianMotion (0 : ℂ)
      {b : ContinuousPath ℂ | ContinuousPath.exitTime (ball (0 : ℂ) ρ) b ≤ δ}) (𝓝[>] 0) (𝓝 0) := by
  have hτm := ContinuousPath.measurable_exitTime (ball (0 : ℂ) ρ) isOpen_ball
  have hlim := tendsto_measure_biInter_gt (μ := planarBrownianMotion (0 : ℂ))
    (s := fun δ : ℝ≥0 => {b : ContinuousPath ℂ | ContinuousPath.exitTime (ball (0 : ℂ) ρ) b ≤ δ})
    (a := 0) (fun r _ => (measurableSet_le hτm measurable_const).nullMeasurableSet)
    (fun i j _ hij b hb => by
      simp only [mem_ofPred_eq] at hb ⊢; exact le_trans hb (by exact_mod_cast hij))
    ⟨1, one_pos, measure_ne_top _ _⟩
  have h0 : planarBrownianMotion (0 : ℂ) (⋂ r > (0 : ℝ≥0),
      {b : ContinuousPath ℂ | ContinuousPath.exitTime (ball (0 : ℂ) ρ) b ≤ r}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (ae_planarBrownianMotion_eval_zero (0 : ℂ)))
    intro b hb
    simp only [mem_iInter, mem_ofPred_eq] at hb
    show ¬ b 0 = 0
    intro h0b
    have hpos : 0 < ContinuousPath.exitTime (ball (0 : ℂ) ρ) b :=
      (ContinuousPath.exitTime_pos_iff _ isOpen_ball b).2 (by rw [h0b]; exact mem_ball_self hρ)
    obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
    exact absurd (hb r (by exact_mod_cast hr0)) (not_le.2 hr)
  rw [h0] at hlim
  exact hlim

section ApproxClock

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ} {n : ℕ}

/-- The approximate Liouville Brownian path of `b` and the delayed approximate path of `θ_δ b`
are within `T₀ η + e^{-T₀}` in `dUnif` when `b` oscillates by at most `η` on `[0, δ]`. -/
theorem dUnif_lbmContinuousPath_lqgApproxClockPlus_delay_le
    (hcont : Continuous (hε (dyadicScale n))) (b : ContinuousPath ℂ) (δ : ℝ≥0) {η : ℝ}
    (hosc : ∀ r ≤ δ, ‖b r - b δ‖ ≤ η) (T0 : ℝ≥0) :
    LatticeProb.dUnif (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
        (continuousPathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal
          (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))) ≤
      T0 * η + Real.exp (-(T0 : ℝ)) :=
  dUnif_lbmContinuousPath_continuousPathDelay_le (isTimeChangeClock_lqgApproxClockPlus hcont b)
    (lqgApproxClockPlus_shift_eq_sub hcont b δ) hosc T0

/-- **The term `m_L(δ)` at a fixed level and start.** For `L ≥ 0`, `ρ ≥ 0` and `T₀ ≥ 0`,
`E^z min(2, L dUnif(Φ_n b, T_{c_n(b)} Φ_n(θ_δ b))) ≤ L (2 T₀ ρ + e^{-T₀}) + 2 P^0(τ_{B(0,ρ)} ≤ δ)`. -/
theorem integral_min_dUnif_lbmContinuousPath_lqgApproxClockPlus_delay_le
    (hcont : Continuous (hε (dyadicScale n))) (z : ℂ) (δ : ℝ≥0) {L ρ : ℝ} (hL : 0 ≤ L)
    (hρ : 0 ≤ ρ) (T0 : ℝ≥0) :
    ∫ b, min 2 (L * LatticeProb.dUnif (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
        (continuousPathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal
          (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))))
        ∂(planarBrownianMotion z) ≤
      L * (T0 * (2 * ρ) + Real.exp (-(T0 : ℝ))) +
        2 * (planarBrownianMotion (0 : ℂ)
          {b : ContinuousPath ℂ | ContinuousPath.exitTime (ball (0 : ℂ) ρ) b ≤ δ}).toReal := by
  set S : Set (ContinuousPath ℂ) :=
    {b | ContinuousPath.exitTime (ball (0 : ℂ) ρ) (translatePath (-z) b) ≤ δ} with hS
  have hSm : MeasurableSet S :=
    measurableSet_le ((ContinuousPath.measurable_exitTime _ isOpen_ball).comp
      (translatePath (-z)).continuous.measurable) measurable_const
  set c := L * (T0 * (2 * ρ) + Real.exp (-(T0 : ℝ))) with hc
  have hc0 : 0 ≤ c :=
    mul_nonneg hL (add_nonneg (mul_nonneg T0.2 (by linarith)) (Real.exp_pos _).le)
  have hg : Integrable (fun b => c + S.indicator (fun _ => (2 : ℝ)) b) (planarBrownianMotion z) :=
    (integrable_const c).add ((integrable_const (2 : ℝ)).indicator hSm)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun b => ?_) hg
    (Eventually.of_forall fun b => ?_)).trans (le_of_eq ?_)
  · exact le_min (by norm_num) (mul_nonneg hL (LatticeProb.dUnif_nonneg _ _))
  · by_cases hb : b ∈ S
    · simp only [indicator_of_mem hb]
      linarith [min_le_left (2 : ℝ) (L * LatticeProb.dUnif
        (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
        (continuousPathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal
          (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))))]
    · simp only [indicator_of_notMem hb, add_zero]
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left
        (dUnif_lbmContinuousPath_lqgApproxClockPlus_delay_le hcont b δ
          (norm_sub_le_of_not_exitTime_translatePath_le hb) T0) hL)
  · rw [integral_add (integrable_const c) ((integrable_const (2 : ℝ)).indicator hSm),
      integral_indicator hSm, setIntegral_const, integral_const, hS]
    simp only [measureReal_def]
    rw [planarBrownianMotion_exitTime_translatePath_neg_le]
    simp only [measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    ring

/-- **The term `m_L(δ)` is small uniformly in the level and the start.** For `L ≥ 0` and `ε > 0`,
for all small `δ > 0`, every level `n` with continuous circle averages at the scale `2^{-n}` and
every start `z`, `E^z min(2, L dUnif(Φ_n b, T_{c_n(b)} Φ_n(θ_δ b))) ≤ ε`. -/
theorem eventually_integral_min_dUnif_lbmContinuousPath_lqgApproxClockPlus_delay_le
    {L ε : ℝ} (hL : 0 ≤ L) (hεpos : 0 < ε) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ n, Continuous (hε (dyadicScale n)) → ∀ z : ℂ,
      ∫ b, min 2 (L * LatticeProb.dUnif (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
        (continuousPathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal
          (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))))
        ∂(planarBrownianMotion z) ≤ ε := by
  -- choose `T₀` with `L e^{-T₀} ≤ ε / 3`
  have hexp : Tendsto (fun T : ℝ => L * Real.exp (-T)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul L
  obtain ⟨T1, hT1⟩ := eventually_atTop.1 (hexp.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < ε / 3)))
  set T0 : ℝ≥0 := (max T1 0).toNNReal with hT0
  have hT0e : L * Real.exp (-(T0 : ℝ)) ≤ ε / 3 := by
    refine hT1 _ ?_
    rw [hT0, Real.coe_toNNReal _ (le_max_right _ _)]
    exact le_max_left _ _
  -- choose `ρ` with `2 L T₀ ρ ≤ ε / 3`
  have hK : 0 < L * T0 + 1 := by positivity
  set ρ : ℝ := ε / (6 * (L * T0 + 1)) with hρdef
  have hρ : 0 < ρ := by positivity
  have hρe : L * (T0 * (2 * ρ)) ≤ ε / 3 := by
    have h1 : L * (T0 * (2 * ρ)) = ε / 3 * (L * T0 / (L * T0 + 1)) := by
      rw [hρdef]; field_simp; ring
    rw [h1]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one hK).2 (by linarith))
  -- the exit probability at radius `ρ` is small for small `δ`
  have hπ := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_planarBrownianMotion_exitTime_ball_le hρ)
  filter_upwards [hπ.eventually (ge_mem_nhds (by rw [ENNReal.toReal_zero]; linarith : ((0 : ℝ≥0∞).toReal) < ε / 6))]
    with δ hδ n hcont z
  have hδ' : (planarBrownianMotion (0 : ℂ)
      {b : ContinuousPath ℂ | ContinuousPath.exitTime (ball (0 : ℂ) ρ) b ≤ δ}).toReal ≤ ε / 6 := hδ
  refine (integral_min_dUnif_lbmContinuousPath_lqgApproxClockPlus_delay_le hcont z δ hL hρ.le
    T0).trans ?_
  nlinarith [hT0e, hρe, hδ']

end ApproxClock

end MatedCRT.FirstPass.Derived
