import MatedCRT.FirstPass.Derived.LQGApproxPathKernel
import MatedCRT.FirstPass.Derived.ConeReferenceInitialClockSmall
import MatedCRT.FirstPass.Derived.UniformStartStoppedBM
import MatedCRT.FirstPass.Derived.PlanarBrownianExitDynkin

/-!
# Tail of the approximating LQG clock at a small time

Let `A'_k(b, t) = A_k(b, t) + 2^{-k} t` be the dyadic approximating LQG clock with its vanishing linear drift
(`lqgApproxClockPlus`), and suppose the stopped heat bound
`E^w ∫_0^{δ ∧ τ_{B(0,R+1)}} ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds ≤ C δ^β` holds at a start `w` with `|w| ≤ R`.
Then, for `2δ ≤ a`,

`P^w(A'_k(b, δ) > a) ≤ π(δ) + 2 C δ^β / a`, where `π(δ) = P^0(τ_{B(0,1)} ≤ δ)`,

and `π(δ) → 0` as `δ ↓ 0`. The bound is uniform in the level `k` and in the start `|w| ≤ R`: the exit term is
compared with the exit of the unit disc by Brownian motion from `0`, by translation invariance.
-/

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess
open Filter Topology Metric
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- The probability `π(δ) = P^0(τ_{B(0,1)} ≤ δ)` that planar Brownian motion from `0` leaves the unit disc by time
`δ` tends to `0` as `δ ↓ 0`. -/
theorem tendsto_planarBrownianMotion_exitTime_unitBall_le :
    Tendsto (fun δ : ℝ≥0 => planarBrownianMotion (0 : ℂ)
      {b : ContinuousPath ℂ | ContinuousPath.exitTime (ball (0 : ℂ) 1) b ≤ δ}) (𝓝[>] 0) (𝓝 0) := by
  have hτm := ContinuousPath.measurable_exitTime (ball (0 : ℂ) 1) isOpen_ball
  have hlim := tendsto_measure_biInter_gt (μ := planarBrownianMotion (0 : ℂ))
    (s := fun δ : ℝ≥0 => {b : ContinuousPath ℂ | ContinuousPath.exitTime (ball (0 : ℂ) 1) b ≤ δ})
    (a := 0) (fun r _ => (measurableSet_le hτm measurable_const).nullMeasurableSet)
    (fun i j _ hij b hb => by
      simp only [mem_ofPred_eq] at hb ⊢; exact le_trans hb (by exact_mod_cast hij)) ⟨1, one_pos, measure_ne_top _ _⟩
  have h0 : planarBrownianMotion (0 : ℂ) (⋂ r > (0 : ℝ≥0),
      {b : ContinuousPath ℂ | ContinuousPath.exitTime (ball (0 : ℂ) 1) b ≤ r}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (ae_planarBrownianMotion_eval_zero (0 : ℂ)))
    intro b hb
    simp only [mem_iInter, mem_ofPred_eq] at hb
    show ¬ b 0 = 0
    intro h0b
    have hpos : 0 < ContinuousPath.exitTime (ball (0 : ℂ) 1) b :=
      (ContinuousPath.exitTime_pos_iff _ isOpen_ball b).2 (by rw [h0b]; exact mem_ball_self one_pos)
    obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
    exact absurd (hb r (by exact_mod_cast hr0)) (not_le.2 hr)
  rw [h0] at hlim
  exact hlim

/-- **Tail of the approximating clock at a small time (uniform in the level and the start).** If the stopped
heat bound `E^w ∫_0^{δ ∧ τ_{B(0,R+1)}} ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds ≤ C δ^β` holds at a start `w` with
`|w| ≤ R`, then for `0 < a` and `2δ ≤ a`,
`P^w(A'_k(b, δ) > a) ≤ P^0(τ_{B(0,1)} ≤ δ) + 2 C δ^β / a`, where `A'_k = lqgApproxClockPlus γ hε k`. -/
theorem planarBrownianMotion_lt_lqgApproxClockPlus_le
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {k : ℕ} (hcont : Continuous (hε (dyadicScale k)))
    {R β C : ℝ} {w : ℂ} (hw : ‖w‖ ≤ R) {δ a : ℝ≥0} (ha : 0 < a) (hδa : 2 * δ ≤ a)
    (hbound : ∫⁻ b, (∫⁻ s in Ioc 0 (min (δ : ℝ)
          (ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b).toReal),
          ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
            Real.exp (γ * hε (dyadicScale k) (b s.toNNReal))))
        ∂(planarBrownianMotion w) ≤ ENNReal.ofReal (C * (δ : ℝ) ^ β)) :
    planarBrownianMotion w {b | (a : ℝ) < lqgApproxClockPlus γ hε k b δ} ≤
      planarBrownianMotion (0 : ℂ) {b | ContinuousPath.exitTime (ball (0 : ℂ) 1) b ≤ δ} +
        ENNReal.ofReal (2 * C * (δ : ℝ) ^ β / a) := by
  set Q := planarBrownianMotion w with hQ
  have hτm : Measurable fun b : ContinuousPath ℂ =>
      ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b :=
    ContinuousPath.measurable_exitTime _ isOpen_ball
  set G : Set (ContinuousPath ℂ) := {b | (δ : ℝ≥0∞) < ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b ∧
    ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b < ⊤} with hGdef
  have hG : MeasurableSet G :=
    (measurableSet_lt measurable_const hτm).inter (measurableSet_lt hτm measurable_const)
  set Y : ContinuousPath ℂ → ℝ≥0∞ :=
    G.indicator (fun b => ENNReal.ofReal (lqgClockApprox γ hε (dyadicScale k) b δ)) with hYdef
  have hYm : Measurable Y :=
    ((MatedCRT.measurable_lqgClockApprox hcont δ).ennreal_ofReal).indicator hG
  have hε1 : dyadicScale k ≤ 1 := by
    unfold dyadicScale; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hε0 : 0 ≤ dyadicScale k := by unfold dyadicScale; positivity
  have ha' : (0 : ℝ) < a := ha
  have ha2 : (0 : ℝ) < (a : ℝ) / 2 := by linarith
  -- the event splits into an early exit, a non-exit, and a large clock before the exit
  have hsub : {b | (a : ℝ) < lqgApproxClockPlus γ hε k b δ} ⊆
      ({b | ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b ≤ δ} ∪
        {b | ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b = ⊤}) ∪
        {b | ENNReal.ofReal ((a : ℝ) / 2) ≤ Y b} := by
    intro b hb
    by_cases hbG : b ∈ G
    · right
      change ENNReal.ofReal ((a : ℝ) / 2) ≤ Y b
      rw [hYdef, Set.indicator_of_mem hbG]
      apply ENNReal.ofReal_le_ofReal
      have hb' : (a : ℝ) < lqgClockApprox γ hε (dyadicScale k) b δ + dyadicScale k * δ := hb
      have hδ' : (2 : ℝ) * δ ≤ a := by exact_mod_cast hδa
      have hdr : dyadicScale k * (δ : ℝ) ≤ δ := mul_le_of_le_one_left δ.coe_nonneg hε1
      linarith
    · left
      have hn : ¬ ((δ : ℝ≥0∞) < ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b ∧
          ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b < ⊤) := hbG
      rcases not_and_or.1 hn with h | h
      · exact Or.inl (not_lt.1 h)
      · exact Or.inr (top_le_iff.1 (not_lt.1 h))
  -- before the exit, the clock is dominated by the stopped occupation integral
  have hYX : ∀ b, Y b ≤
      ∫⁻ s in Ioc 0 (min (δ : ℝ) (ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b).toReal),
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
          Real.exp (γ * hε (dyadicScale k) (b s.toNNReal))) := by
    intro b
    by_cases hbG : b ∈ G
    · have hle : (δ : ℝ) ≤ (ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b).toReal := by
        have h1 := ENNReal.toReal_mono hbG.2.ne hbG.1.le
        simpa using h1
      rw [hYdef, Set.indicator_of_mem hbG, min_eq_left hle, lqgClockApprox,
        intervalIntegral.integral_of_le δ.coe_nonneg]
      exact ofReal_integral_le_lintegral_ofReal_of_nonneg
        (Eventually.of_forall fun s => mul_nonneg (Real.rpow_nonneg hε0 _) (Real.exp_pos _).le)
    · have h0 : Y b = 0 := by simp [hYdef, hbG]
      rw [h0]
      exact zero_le
  have hmarkov : Q {b | ENNReal.ofReal ((a : ℝ) / 2) ≤ Y b} ≤
      (∫⁻ b, Y b ∂Q) / ENNReal.ofReal ((a : ℝ) / 2) :=
    meas_ge_le_lintegral_div hYm.aemeasurable (ENNReal.ofReal_pos.2 ha2).ne' ENNReal.ofReal_ne_top
  have hint : ∫⁻ b, Y b ∂Q ≤ ENNReal.ofReal (C * (δ : ℝ) ^ β) := (lintegral_mono hYX).trans hbound
  have hdiv : ENNReal.ofReal (C * (δ : ℝ) ^ β) / ENNReal.ofReal ((a : ℝ) / 2) =
      ENNReal.ofReal (2 * C * (δ : ℝ) ^ β / a) := by
    rw [← ENNReal.ofReal_div_of_pos ha2, div_div_eq_mul_div]
    congr 1
    ring
  -- the exit time is almost surely finite
  have htop : Q {b | ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b = ⊤} = 0 := by
    have hfin : ∀ᵐ b ∂Q, ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b < ⊤ :=
      ae_lt_top (ContinuousPath.measurable_exitTime _ isOpen_ball)
        (MatedCRT.KilledOccupation.lintegral_exitTime_planarBrownianMotion_lt_top isOpen_ball
          isBounded_ball w).ne
    have hnull := ae_iff.1 hfin
    refine measure_mono_null ?_ hnull
    intro b hb
    show ¬ ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b < ⊤
    rw [show ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b = ⊤ from hb]
    exact lt_irrefl _
  -- an early exit of `B(0, R+1)` from `w` forces an early exit of the unit disc around `w`
  have hexit : Q {b | ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b ≤ δ} ≤
      planarBrownianMotion (0 : ℂ) {b | ContinuousPath.exitTime (ball (0 : ℂ) 1) b ≤ δ} := by
    rw [hQ, MatedCRT.StopAtExitCmp.planarBrownianMotion_apply_eq_translatePath w]
    refine measure_mono fun b hb => ?_
    have hb' : ContinuousPath.exitTime (ball (0 : ℂ) (R + 1))
        (MatedCRT.StopAtExitCmp.translatePath w b) ≤ δ := hb
    show ContinuousPath.exitTime (ball (0 : ℂ) 1) b ≤ δ
    refine le_trans ?_ hb'
    rw [ContinuousPath.le_exitTime_iff]
    intro v hv
    refine ContinuousPath.exitTime_le_of_notMem _ b v fun h => hv ?_
    rw [MatedCRT.StopAtExitCmp.translatePath_apply, mem_ball_zero_iff]
    rw [mem_ball_zero_iff] at h
    calc ‖b v + w‖ ≤ ‖b v‖ + ‖w‖ := norm_add_le _ _
      _ < R + 1 := by linarith
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le (μ := Q) _ _) le_rfl).trans ?_
  rw [htop, add_zero]
  exact add_le_add hexit (hmarkov.trans ((ENNReal.div_le_div_right hint _).trans hdiv.le))

end MatedCRT.FirstPass.Derived
