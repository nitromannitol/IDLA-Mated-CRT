import MatedCRT.FirstPass.Derived.ConeReferenceClockRegularity
import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller

/-!
# Markov transfer of the dyadic clock convergence to every start

The dyadic approximating LQG clocks `A^k(b, t) = ∫_0^t ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds`
(`ε_k = 2^{-k}`) of a field with continuous circle averages are additive under time shifts of the
path: `A^k(b, s + t) = A^k(b, s) + A^k(θ_s b, t)`. Together with the simple Markov property of
planar Brownian motion at a deterministic time `s > 0` and the absolute continuity of the law of
`b_s`, this transfers a uniform Cauchy property of the dyadic clocks that holds almost surely from
Lebesgue-almost every start to the increments after every positive time, from every start.

This is the step "every start, after a positive time" of the derivation of the LQG clock at every
start (Berestycki 2015, Theorem 1.2, holds for a fixed start; the passage to every start uses the
Markov property at positive times).

## Main statements

* `planarHeatSemigroup_absolutelyContinuous`: at a positive time, the planar heat kernel is
  absolutely continuous with respect to Lebesgue measure.
* `ae_planarBrownianMotion_shift_of_ae_start`: a measurable path event that holds almost surely
  from Lebesgue-almost every start holds, from every start, for the path shifted by any positive
  time.
* `lqgClockApprox_add_eq_add_shift`: additivity of the approximating clock under time shifts.
* `measurableSet_uniformCauchySeqOn_lqgClockApprox`: the event that the dyadic clocks are uniformly
  Cauchy on a set of times is measurable.
* `uniformCauchySeqOn_increments_of_ae_start`: uniform Cauchy dyadic clocks on every `[0, T]` from
  almost every start give, from every start, uniform Cauchy increments after each
  `δ_n = (n + 1)⁻¹` on every `[δ_n, T]`.
* `ae_coneRef_isLQGClock_continuous_monotone_of_ae_start`: the corresponding statement for the
  reference cone: the LQG clock at every start, which starts at `0` and is continuous and
  nondecreasing, follows from the uniform Cauchy property from almost every start.
-/

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric MarkovProcess
open Filter Topology Metric
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- At a positive time the planar heat kernel (the law of planar Brownian motion at that time) is
absolutely continuous with respect to Lebesgue measure. -/
theorem planarHeatSemigroup_absolutelyContinuous (x : ℂ) {s : ℝ≥0} (hs : s ≠ 0) :
    planarHeatSemigroup s x ≪ volume := by
  rw [planarHeatSemigroup_apply]
  have h := (gaussianReal_absolutelyContinuous x.re hs).prod
    (gaussianReal_absolutelyContinuous x.im hs)
  have hm := h.map Complex.measurableEquivRealProd.symm.measurable
  rw [← Measure.volume_eq_prod ℝ ℝ, Complex.volume_preserving_equiv_real_prod.symm.map_eq] at hm
  exact hm

/-- **Markov transfer from almost every start.** A measurable path event that holds almost surely
for planar Brownian motion started from Lebesgue-almost every point holds, from every start, for
the path shifted by any positive time (simple Markov property at the time `s`; the law of `b_s` is
absolutely continuous). -/
theorem ae_planarBrownianMotion_shift_of_ae_start (x : ℂ) {s : ℝ≥0} (hs : s ≠ 0)
    {S : Set (ContinuousPath ℂ)} (hS : MeasurableSet S)
    (h : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), b ∈ S) :
    ∀ᵐ b ∂(planarBrownianMotion x), ContinuousPath.shift s b ∈ S := by
  have ha : ∀ᵐ b ∂(planarBrownianMotion x).map (ContinuousPath.shift s), b ∈ S := by
    rw [planarBrownianMotion_eq_continuousProcess]
    have hshift := congrArg (fun K => K x)
      (SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift
        planarHeatSemigroup isConservative_planarHeatSemigroup
        isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup s)
    rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed s) x] at hshift
    rw [hshift]
    apply ProbabilityTheory.Kernel.ae_comp_of_ae_ae hS
    filter_upwards [(planarHeatSemigroup_absolutelyContinuous x hs).ae_le h] with y hy
    change ∀ᵐ b ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess
      planarHeatSemigroup isConservative_planarHeatSemigroup y), b ∈ S
    rw [← planarBrownianMotion_eq_continuousProcess]
    exact hy
  exact (ae_map_iff (ContinuousPath.measurable_shift_fixed s).aemeasurable hS).mp ha

/-- **Additivity of the approximating clock under time shifts.** For a field with continuous
circle averages at the scale `ε`, `A(b, s + t) = A(b, s) + A(θ_s b, t)`, where `θ_s b = b(s + ·)`. -/
theorem lqgClockApprox_add_eq_add_shift {γ ε : ℝ} {hε : ℝ → ℂ → ℝ} (hcont : Continuous (hε ε))
    (b : ContinuousPath ℂ) (s t : ℝ≥0) :
    lqgClockApprox γ hε ε b (s + t) =
      lqgClockApprox γ hε ε b s + lqgClockApprox γ hε ε (ContinuousPath.shift s b) t := by
  unfold lqgClockApprox
  rw [NNReal.coe_add, ← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_clockDensity (γ := γ) hcont b 0 s)
    (intervalIntegrable_clockDensity (γ := γ) hcont b s (s + t))]
  congr 1
  have hshift : ∫ u in (s : ℝ)..(s : ℝ) + t, ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b u.toNNReal)) =
      ∫ u in (0 : ℝ)..(t : ℝ), ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b (u + s).toNNReal)) := by
    rw [intervalIntegral.integral_comp_add_right
      (fun u : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b u.toNNReal))), zero_add, add_comm]
  rw [hshift]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le (NNReal.coe_nonneg t)] at hu
  have hpt : (u + s).toNNReal = s + u.toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (add_nonneg hu.1 (NNReal.coe_nonneg s)), NNReal.coe_add,
      Real.coe_toNNReal _ hu.1, add_comm]
  simp only [hpt, ContinuousPath.shift_apply]

/-- The event that the dyadic approximating clocks are uniformly Cauchy on a set of times is
measurable (continuity in time reduces it to countably many times). -/
theorem measurableSet_uniformCauchySeqOn_lqgClockApprox {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hε (HarmonicBalls.dyadicScale k))) (s : Set ℝ≥0) :
    MeasurableSet {b : ContinuousPath ℂ | UniformCauchySeqOn
      (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) atTop s} := by
  have hEq : {b : ContinuousPath ℂ | UniformCauchySeqOn
      (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) atTop s} =
      ⋂ j : ℕ, ⋃ N : ℕ, ⋂ m ≥ N, ⋂ n ≥ N, {b | ∃ t ∈ s, ((j : ℝ) + 1)⁻¹ <
        |lqgClockApprox γ hε (HarmonicBalls.dyadicScale m) b t -
          lqgClockApprox γ hε (HarmonicBalls.dyadicScale n) b t|}ᶜ := by
    ext b
    simp only [mem_ofPred_eq, Metric.uniformCauchySeqOn_iff, mem_iInter, mem_iUnion,
      mem_compl_iff, not_exists, not_and, not_lt, Real.dist_eq]
    constructor
    · intro h j
      obtain ⟨N, hN⟩ := h _ (by positivity : (0 : ℝ) < ((j : ℝ) + 1)⁻¹)
      exact ⟨N, fun m hm n hn t ht => (hN m hm n hn t ht).le⟩
    · intro h ε hε
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h j
      refine ⟨N, fun m hm n hn t ht => ?_⟩
      have h1 := hN m hm n hn t ht
      rw [one_div] at hj
      exact h1.trans_lt hj
  rw [hEq]
  refine MeasurableSet.iInter fun j => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
        (LatticeProb.measurableSet_exists_mem_lt_of_continuous
          (fun b t => |lqgClockApprox γ hε (HarmonicBalls.dyadicScale m) b t -
            lqgClockApprox γ hε (HarmonicBalls.dyadicScale n) b t|)
          (fun b => ((continuous_lqgClockApprox_time (hcont m) b).sub
            (continuous_lqgClockApprox_time (hcont n) b)).abs)
          (fun t => ((measurable_lqgClockApprox (hcont m) t).sub
            (measurable_lqgClockApprox (hcont n) t)).abs) s _).compl

/-- **Dyadic clock convergence after positive times, from every start.** If, for every horizon
`T`, the dyadic approximating LQG clocks are almost surely uniformly Cauchy on `[0, T]` for planar
Brownian motion started from Lebesgue-almost every point, then from every start `z` their
increments after each time `δ_n = (n + 1)⁻¹` are almost surely uniformly Cauchy on every
`[δ_n, T]`. -/
theorem uniformCauchySeqOn_increments_of_ae_start {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hε (HarmonicBalls.dyadicScale k)))
    (hae : ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
      UniformCauchySeqOn (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t)
        atTop (Icc 0 T))
    (z : ℂ) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ b ∂(planarBrownianMotion z), UniformCauchySeqOn
      (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t
        - lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b (LatticeProb.invSuccTime n))
      atTop (Icc (LatticeProb.invSuccTime n) T) := by
  set δ := LatticeProb.invSuccTime n with hδdef
  have hδ : δ ≠ 0 := (LatticeProb.invSuccTime_pos n).ne'
  filter_upwards [ae_planarBrownianMotion_shift_of_ae_start z hδ
    (measurableSet_uniformCauchySeqOn_lqgClockApprox (γ := γ) hcont (Icc 0 (T - δ)))
    (hae (T - δ))] with b hb
  rw [Metric.uniformCauchySeqOn_iff] at hb
  rw [Metric.uniformCauchySeqOn_iff]
  intro η hη
  obtain ⟨N, hN⟩ := hb η hη
  refine ⟨N, fun m hm k hk t ht => ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u, t = δ + u := ⟨t - δ, (add_tsub_cancel_of_le ht.1).symm⟩
  have hmem : u ∈ Icc 0 (T - δ) := ⟨zero_le, le_tsub_of_add_le_left ht.2⟩
  show dist (lqgClockApprox γ hε (HarmonicBalls.dyadicScale m) b (δ + u)
      - lqgClockApprox γ hε (HarmonicBalls.dyadicScale m) b δ)
    (lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b (δ + u)
      - lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b δ) < η
  rw [lqgClockApprox_add_eq_add_shift (hcont m) b δ u,
    lqgClockApprox_add_eq_add_shift (hcont k) b δ u, add_sub_cancel_left, add_sub_cancel_left]
  exact hN m hm k hk u hmem

/-- **The LQG clock of the reference cone at every start, from almost every start.** Almost
surely, if for every horizon `T` the dyadic approximating LQG clocks of the reference cone (built
from `c (Y ω)` and `w ω`) are almost surely uniformly Cauchy on `[0, T]` for planar Brownian motion
started from Lebesgue-almost every point, then from every start `z` their limit `F` after positive
times is an LQG clock of the reference cone, and for almost every path `b` the clock `F(b, ·)`
starts at `0`, is continuous and is nondecreasing. -/
theorem ae_coneRef_isLQGClock_continuous_monotone_of_ae_start
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ) :
    ∀ᵐ ω ∂P,
      (∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
        UniformCauchySeqOn
          (fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
            (HarmonicBalls.dyadicScale k) b t)
          atTop (Icc 0 T)) →
      ∀ z : ℂ,
        IsLQGClock planarBrownianMotion γ (coneRefCircle γ (c (Y ω)) (w ω)) z
            (fun b => LatticeProb.limitAfterPositiveTimes
              (fun j => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
                (HarmonicBalls.dyadicScale j) b)) ∧
          ∀ᵐ b ∂(planarBrownianMotion z),
            LatticeProb.limitAfterPositiveTimes
                (fun j => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
                  (HarmonicBalls.dyadicScale j) b) 0 = 0 ∧
            Continuous (LatticeProb.limitAfterPositiveTimes
                (fun j => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
                  (HarmonicBalls.dyadicScale j) b)) ∧
            Monotone (LatticeProb.limitAfterPositiveTimes
                (fun j => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
                  (HarmonicBalls.dyadicScale j) b)) := by
  filter_upwards [ae_coneRef_isLQGClock_continuous_monotone_of_uniformCauchySeqOn
    hY hp hc hcont hmeas hγ hγ2 w] with ω hω hae z
  have hcontk : ∀ k : ℕ,
      Continuous (coneRefCircle γ (c (Y ω)) (w ω) (HarmonicBalls.dyadicScale k)) := fun k =>
    (continuousOn_coneRefCircle γ (hcont (Y ω)) (w ω)).comp_continuous
      (continuous_const.prodMk continuous_id)
      fun x => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  exact hω z fun n T => uniformCauchySeqOn_increments_of_ae_start hcontk hae z n T

end MatedCRT.FirstPass.Derived
