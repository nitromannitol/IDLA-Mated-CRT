import MatedCRT.FirstPass.Derived.ConeReferenceClockLocalChain
import MatedCRT.FirstPass.Derived.LQGLimitClockShiftAdditive
import LatticeProb.Prob.LimitAfterPositiveTimesMeasurable

/-!
# The good set of the limit clock after positive times, from every start

Let `A^k(b)_t = lqgClockApprox γ hε (2^{-k}) b t` be the dyadic approximating LQG clocks and
`F(b) = lim_m lim_k (A^k(b)_· - A^k(b)_{δ_m})`, `δ_m = (m + 1)⁻¹`, their limit after positive times.
The good set of a path `b` consists of the three conditions

* the increment limits `lim_k (A^k(b)_t - A^k(b)_{δ_m})` exist for `t ≥ δ_m`;
* their limits as `m → ∞` exist for `t > 0`;
* `F(b)` is continuous.

On the good set the limit clock is nondecreasing and additive along the shift
(`LQGLimitClockShift.ae_monotone_and_shift_limitAfterPositiveTimes_dyadic`).

* `convergence_of_uniformCauchySeqOn_increments_of_subseq` (deterministic): uniformly Cauchy increments
  after each time `δ_n` on every `[δ_n, T]`, together with pointwise convergence of a subsequence
  `A^{s(n)}` to a function `G` right-continuous at `0`, give the first two conditions.
* `ae_goodSet_of_isLQGClock`: if the limit after positive times is an LQG clock from `z` and is almost
  surely continuous, and the increments are almost surely uniformly Cauchy, then almost every path
  from `z` lies in the good set.
* `ae_coneRef_goodSet_of_local`: for the reference cone, almost surely, once the dyadic clocks are
  locally uniformly Cauchy from Lebesgue-almost every start while the path stays in a closed disc
  avoiding the origin, almost every path from every start lies in the good set.
* `ae_coneRef_monotone_and_shift_of_local`: in the same situation, from every start, the limit clock
  is almost surely nondecreasing and satisfies `F(θ_s b)_t = F(b)_{s+t} - F(b)_s`.
* `strictMono_of_monotone_of_rat_shift` (deterministic), `ae_strictMono_of_ae_start` and
  `ae_coneRef_strictMono_of_local`: strict monotonicity of the clock from Lebesgue-almost every start
  transfers to every start (simple Markov property at the times `δ_n` and shift additivity).
-/

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric MarkovProcess
open Filter Topology Metric
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- **Increment limits and their limits from a convergent subsequence.** Let `a k : ℝ≥0 → ℝ`. If the
increments `a k t - a k δ_n` after each time `δ_n = (n + 1)⁻¹` are uniformly Cauchy on every
`[δ_n, T]`, and along a sequence `s → ∞` the values `a (s n) t` converge to `G t` at every time, with
`G` right-continuous at `0`, then the increment limits `lim_k (a k t - a k δ_m)` exist for `t ≥ δ_m`,
and for `t > 0` they converge to `G t - G 0` as `m → ∞`. -/
theorem convergence_of_uniformCauchySeqOn_increments_of_subseq {a : ℕ → ℝ≥0 → ℝ}
    {G : ℝ≥0 → ℝ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    (hU : ∀ (n : ℕ) (T : ℝ≥0), UniformCauchySeqOn
      (fun k t => a k t - a k (LatticeProb.invSuccTime n)) atTop
      (Icc (LatticeProb.invSuccTime n) T))
    (hsub : ∀ t, Tendsto (fun n => a (s n) t) atTop (𝓝 (G t)))
    (h0 : ContinuousWithinAt G (Ioi 0) 0) :
    (∀ m t, LatticeProb.invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (LatticeProb.invSuccTime m)) atTop (𝓝 L)) ∧
    (∀ t, 0 < t →
      ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter a m t) atTop (𝓝 L)) := by
  have hconv : ∀ m t, LatticeProb.invSuccTime m ≤ t →
      ∃ L, Tendsto (fun k => a k t - a k (LatticeProb.invSuccTime m)) atTop (𝓝 L) :=
    fun m t ht => cauchySeq_tendsto_of_complete ((hU m t).cauchySeq ⟨ht, le_rfl⟩)
  refine ⟨hconv, fun t ht => ⟨G t - G 0, ?_⟩⟩
  have heq : ∀ᶠ m in atTop,
      G t - G (LatticeProb.invSuccTime m) = LatticeProb.incrementLimitAfter a m t := by
    obtain ⟨n, hn⟩ := LatticeProb.exists_invSuccTime_le ht
    filter_upwards [eventually_ge_atTop n] with m hm
    have hmt : LatticeProb.invSuccTime m ≤ t := (LatticeProb.invSuccTime_antitone hm).trans hn
    exact tendsto_nhds_unique ((hsub t).sub (hsub _))
      ((LatticeProb.tendsto_incrementLimitAfter hconv hmt).comp hs)
  exact ((tendsto_const_nhds (x := G t)).sub
    (h0.tendsto.comp tendsto_invSuccTime_nhdsGT_zero)).congr' heq

/-- **The good set from an LQG clock.** For planar Brownian motion from `z`, if the limit after
positive times `F` of the dyadic approximating LQG clocks is an LQG clock from `z` and is almost
surely continuous, and for all `n, N` the increments after `δ_n = (n + 1)⁻¹` are almost surely
uniformly Cauchy on `[δ_n, N]`, then almost every path lies in the good set: the increment limits
exist, their limits as `δ_m → 0` exist, and `F(b)` is continuous. -/
theorem ae_goodSet_of_isLQGClock {γ : ℝ} {hε : ℝ → ℂ → ℝ} {z : ℂ}
    (hclock : IsLQGClock planarBrownianMotion γ hε z
      (fun b => LatticeProb.limitAfterPositiveTimes
        (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t)))
    (hFc : ∀ᵐ b ∂(planarBrownianMotion z), Continuous (LatticeProb.limitAfterPositiveTimes
      (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t)))
    (hU : ∀ (n N : ℕ), ∀ᵐ b ∂(planarBrownianMotion z), UniformCauchySeqOn
      (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t
        - lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b (LatticeProb.invSuccTime n))
      atTop (Icc (LatticeProb.invSuccTime n) (N : ℝ≥0))) :
    ∀ᵐ b ∂(planarBrownianMotion z),
      (∀ m t, LatticeProb.invSuccTime m ≤ t → ∃ L, Tendsto (fun k =>
        lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t -
          lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b (LatticeProb.invSuccTime m))
          atTop (𝓝 L)) ∧
      (∀ t, 0 < t → ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter
        (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) m t) atTop (𝓝 L)) ∧
      Continuous (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) := by
  obtain ⟨s, hs, hsub⟩ := hclock.exists_seq_locally_uniform_clockApprox
  have hU' : ∀ᵐ b ∂(planarBrownianMotion z), ∀ n N : ℕ, UniformCauchySeqOn
      (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t
        - lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b (LatticeProb.invSuccTime n))
      atTop (Icc (LatticeProb.invSuccTime n) (N : ℝ≥0)) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun N => hU n N
  filter_upwards [hsub, hFc, hU'] with b hb hc hu
  obtain ⟨h1, h2⟩ := convergence_of_uniformCauchySeqOn_increments_of_subseq hs.tendsto_atTop
    (fun n T => (hu n ⌈T⌉₊).mono (Icc_subset_Icc le_rfl (Nat.le_ceil T)))
    (fun t => Metric.tendsto_nhds.2 fun η hη =>
      (hb t η hη).mono fun n hn => by rw [Real.dist_eq]; exact hn t le_rfl)
    hc.continuousWithinAt
  exact ⟨h1, h2, hc⟩

/-- **The good set of the reference cone clock from every start.** Almost surely, if the dyadic
approximating LQG clocks of the reference cone (built from `c (Y ω)` and `w ω`) are almost surely
uniformly Cauchy on `[0, h]` for planar Brownian motion from Lebesgue-almost every start, on the
event that the path stays in a closed disc `closedBall a r` with `r < ‖a‖` up to time `h`, then from
every start `z` almost every path lies in the good set of the limit after positive times. -/
theorem ae_coneRef_goodSet_of_local
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ)
    (hpolar : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), ∀ t, b t ≠ 0) :
    ∀ᵐ ω ∂P,
      (∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ →
        ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
          (∀ t ∈ Icc 0 h, b t ∈ closedBall a r) →
          UniformCauchySeqOn
            (fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
              (HarmonicBalls.dyadicScale k) b t)
            atTop (Icc 0 h)) →
      ∀ z : ℂ, ∀ᵐ b ∂(planarBrownianMotion z),
        (∀ m t, LatticeProb.invSuccTime m ≤ t → ∃ L, Tendsto (fun k =>
          lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω)) (HarmonicBalls.dyadicScale k) b t -
            lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω)) (HarmonicBalls.dyadicScale k) b
              (LatticeProb.invSuccTime m)) atTop (𝓝 L)) ∧
        (∀ t, 0 < t → ∃ L, Tendsto (fun m => LatticeProb.incrementLimitAfter
          (fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
            (HarmonicBalls.dyadicScale k) b t) m t) atTop (𝓝 L)) ∧
        Continuous (LatticeProb.limitAfterPositiveTimes
          fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
            (HarmonicBalls.dyadicScale k) b t) := by
  filter_upwards [ae_coneRef_isLQGClock_continuous_monotone_of_local
    hY hp hc hcont hmeas hγ hγ2 w hpolar] with ω hω hloc z
  have hcontk : ∀ k : ℕ,
      Continuous (coneRefCircle γ (c (Y ω)) (w ω) (HarmonicBalls.dyadicScale k)) := fun k =>
    (continuousOn_coneRefCircle γ (hcont (Y ω)) (w ω)).comp_continuous
      (continuous_const.prodMk continuous_id)
      fun x => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  obtain ⟨hclk, hae⟩ := hω hloc z
  exact ae_goodSet_of_isLQGClock hclk (hae.mono fun b hb => hb.2.1)
    fun n N => uniformCauchySeqOn_increments_of_ae_start hcontk
      (fun T => ae_uniformCauchySeqOn_lqgClockApprox_of_local hcontk hpolar hloc T) z n N

/-- **Monotonicity and shift additivity of the reference cone clock from every start.** Almost surely,
under the local uniform Cauchy property of `ae_coneRef_goodSet_of_local`, from every start `z` the
limit after positive times `F` of the dyadic approximating LQG clocks of the reference cone is almost
surely nondecreasing and satisfies `F(θ_s b)_t = F(b)_{s+t} - F(b)_s` for all `s, t`: the hypothesis
`hadd` of `planarBrownianMotion_ae_tendsto_atTop_of_additive`. -/
theorem ae_coneRef_monotone_and_shift_of_local
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ)
    (hpolar : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), ∀ t, b t ≠ 0) :
    ∀ᵐ ω ∂P,
      (∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ →
        ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
          (∀ t ∈ Icc 0 h, b t ∈ closedBall a r) →
          UniformCauchySeqOn
            (fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
              (HarmonicBalls.dyadicScale k) b t)
            atTop (Icc 0 h)) →
      ∀ z : ℂ, ∀ᵐ b ∂(planarBrownianMotion z),
        Monotone (LatticeProb.limitAfterPositiveTimes
          fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
            (HarmonicBalls.dyadicScale k) b t) ∧
        ∀ s t, LatticeProb.limitAfterPositiveTimes
            (fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
              (HarmonicBalls.dyadicScale k) (ContinuousPath.shift s b) t) t =
          LatticeProb.limitAfterPositiveTimes
              (fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
                (HarmonicBalls.dyadicScale k) b t) (s + t) -
            LatticeProb.limitAfterPositiveTimes
              (fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
                (HarmonicBalls.dyadicScale k) b t) s := by
  filter_upwards [ae_coneRef_goodSet_of_local hY hp hc hcont hmeas hγ hγ2 w hpolar]
    with ω hω hloc z
  have hcontk : ∀ k : ℕ,
      Continuous (coneRefCircle γ (c (Y ω)) (w ω) (HarmonicBalls.dyadicScale k)) := fun k =>
    (continuousOn_coneRefCircle γ (hcont (Y ω)) (w ω)).comp_continuous
      (continuous_const.prodMk continuous_id)
      fun x => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  exact LQGLimitClockShift.ae_monotone_and_shift_limitAfterPositiveTimes_dyadic hcontk (hω hloc z)

/-- **Strict monotonicity from strict increase after the times `δ_n` at rational lags.** A
nondecreasing `G : ℝ≥0 → ℝ` such that `G (δ_n + p) < G (δ_n + q)` for every `n` and all rationals
`p, q` with `p⁺ < q⁺` (where `δ_n = (n + 1)⁻¹`) is strictly increasing. -/
theorem strictMono_of_monotone_of_rat_shift {G : ℝ≥0 → ℝ} (hmono : Monotone G)
    (h : ∀ (n : ℕ) (p q : ℚ), Real.toNNReal p < Real.toNNReal q →
      G (LatticeProb.invSuccTime n + Real.toNNReal p) <
        G (LatticeProb.invSuccTime n + Real.toNNReal q)) :
    StrictMono G := by
  have hpos : ∀ t₁ t₂ : ℝ≥0, 0 < t₁ → t₁ < t₂ → G t₁ < G t₂ := by
    intro t₁ t₂ h₁ h₁₂
    obtain ⟨n, hn⟩ := LatticeProb.exists_invSuccTime_le (half_pos h₁)
    have hδ : LatticeProb.invSuccTime n < t₁ := hn.trans_lt (half_lt_self h₁)
    have hu : ((t₁ - LatticeProb.invSuccTime n : ℝ≥0) : ℝ) <
        ((t₂ - LatticeProb.invSuccTime n : ℝ≥0) : ℝ) :=
      NNReal.coe_lt_coe.2 (tsub_lt_tsub_right_of_le hδ.le h₁₂)
    obtain ⟨p, hp₁, hp₂⟩ := exists_rat_btwn hu
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hp₂
    have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (NNReal.coe_nonneg _) hp₁
    have hq0 : (0 : ℝ) < q := hp0.trans hq₁
    have hpq : Real.toNNReal p < Real.toNNReal q := (Real.toNNReal_lt_toNNReal_iff hq0).2 hq₁
    calc G t₁ = G (LatticeProb.invSuccTime n + (t₁ - LatticeProb.invSuccTime n)) := by
            rw [add_tsub_cancel_of_le hδ.le]
      _ ≤ G (LatticeProb.invSuccTime n + Real.toNNReal p) :=
            hmono (add_le_add le_rfl (Real.lt_toNNReal_iff_coe_lt.2 hp₁).le)
      _ < G (LatticeProb.invSuccTime n + Real.toNNReal q) := h n p q hpq
      _ ≤ G (LatticeProb.invSuccTime n + (t₂ - LatticeProb.invSuccTime n)) :=
            hmono (add_le_add le_rfl ((Real.toNNReal_lt_iff_lt_coe hq0.le).2 hq₂).le)
      _ = G t₂ := by rw [add_tsub_cancel_of_le (hδ.trans h₁₂).le]
  intro t₁ t₂ h₁₂
  rcases eq_or_ne t₁ 0 with rfl | h₁
  · exact (hmono zero_le).trans_lt (hpos _ _ (half_pos h₁₂) (half_lt_self h₁₂))
  · exact hpos t₁ t₂ (pos_iff_ne_zero.2 h₁) h₁₂

/-- **Strict monotonicity of an additive clock at every start, from almost every start.** Let
`F : C([0, ∞), ℂ) → ℝ≥0 → ℝ` be measurable at each time. If, for planar Brownian motion from
Lebesgue-almost every start, `F(b)` is almost surely strictly increasing, and from `z` the clock is
almost surely nondecreasing and satisfies `F(θ_s b)_t = F(b)_{s+t} - F(b)_s`, then from `z` it is
almost surely strictly increasing. -/
theorem ae_strictMono_of_ae_start {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hFm : ∀ t, Measurable fun b => F b t)
    (hsm : ∀ᵐ w ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion w), StrictMono (F b))
    (z : ℂ)
    (hadd : ∀ᵐ b ∂(planarBrownianMotion z), Monotone (F b) ∧
      ∀ s t, F (ContinuousPath.shift s b) t = F b (s + t) - F b s) :
    ∀ᵐ b ∂(planarBrownianMotion z), StrictMono (F b) := by
  set S : Set (ContinuousPath ℂ) := {b | ∀ p q : ℚ, Real.toNNReal p < Real.toNNReal q →
    F b (Real.toNNReal p) < F b (Real.toNNReal q)} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_setOfPred.2 (Measurable.forall fun p => Measurable.forall fun q =>
      measurable_const.imp (measurableSet_setOfPred.1 (measurableSet_lt (hFm _) (hFm _))))
  have hS0 : ∀ᵐ w ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion w), b ∈ S := by
    filter_upwards [hsm] with w hw
    filter_upwards [hw] with b hb
    exact fun p q hpq => hb hpq
  have hshift : ∀ᵐ b ∂(planarBrownianMotion z), ∀ n : ℕ,
      ContinuousPath.shift (LatticeProb.invSuccTime n) b ∈ S :=
    ae_all_iff.2 fun n => ae_planarBrownianMotion_shift_of_ae_start z
      (LatticeProb.invSuccTime_pos n).ne' hS hS0
  filter_upwards [hadd, hshift] with b hb hsb
  refine strictMono_of_monotone_of_rat_shift hb.1 fun n p q hpq => ?_
  have h := hsb n p q hpq
  rw [hb.2, hb.2] at h
  exact (sub_lt_sub_iff_right _).1 h

/-- **Strict monotonicity of the reference cone clock from every start.** Almost surely, under the
local uniform Cauchy property of `ae_coneRef_goodSet_of_local`, if the limit after positive times `F`
of the dyadic approximating LQG clocks of the reference cone is almost surely strictly increasing
for planar Brownian motion from Lebesgue-almost every start, then it is almost surely strictly
increasing from every start. -/
theorem ae_coneRef_strictMono_of_local
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ)
    (hpolar : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), ∀ t, b t ≠ 0) :
    ∀ᵐ ω ∂P,
      (∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ →
        ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
          (∀ t ∈ Icc 0 h, b t ∈ closedBall a r) →
          UniformCauchySeqOn
            (fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
              (HarmonicBalls.dyadicScale k) b t)
            atTop (Icc 0 h)) →
      (∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
        StrictMono (LatticeProb.limitAfterPositiveTimes
          fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
            (HarmonicBalls.dyadicScale k) b t)) →
      ∀ z : ℂ, ∀ᵐ b ∂(planarBrownianMotion z),
        StrictMono (LatticeProb.limitAfterPositiveTimes
          fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
            (HarmonicBalls.dyadicScale k) b t) := by
  filter_upwards [ae_coneRef_monotone_and_shift_of_local hY hp hc hcont hmeas hγ hγ2 w hpolar]
    with ω hω hloc hsm z
  have hcontk : ∀ k : ℕ,
      Continuous (coneRefCircle γ (c (Y ω)) (w ω) (HarmonicBalls.dyadicScale k)) := fun k =>
    (continuousOn_coneRefCircle γ (hcont (Y ω)) (w ω)).comp_continuous
      (continuous_const.prodMk continuous_id)
      fun x => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  exact ae_strictMono_of_ae_start
    (fun t => LatticeProb.measurable_limitAfterPositiveTimes
      (fun k t => MatedCRT.measurable_lqgClockApprox (hcontk k) t) t)
    hsm z (hω hloc z)

end MatedCRT.FirstPass.Derived
