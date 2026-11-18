import MatedCRT.FirstPass.Derived.ConeReferenceInitialClockSmall
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxPathMeasurable
import LatticeProb.Prob.UniformLimitAfterPositiveTimes

/-!
# The LQG clock of the reference cone from convergence after each positive time

Let `A_k(b, t) = ∫_0^t ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds`, `ε_k = 2^{-k}`, be the approximating LQG
clocks (`lqgClockApprox`) of a field with continuous circle averages along a path `b`. They are
continuous, nondecreasing and nonnegative in `t`, and measurable in `b` at each fixed time. If,
for planar Brownian motion from `z`,

* after each time `δ_n = (n + 1)⁻¹` the increments `A_k(t) - A_k(δ_n)` form almost surely a uniform
  Cauchy sequence on every `[δ_n, T]`, and
* `sup_k P_z(A_k(t) ≥ η) → 0` as `t ↓ 0`, for every `η > 0`,

then the limit `F(b, t) = lim_k A_k(b, t)`, taken after positive times
(`LatticeProb.limitAfterPositiveTimes`), is an LQG clock of the field from `z` in the sense of
`IsLQGClock`: `A_k → F` in probability, uniformly on `[0, T]`
(`isLQGClock_limitAfterPositiveTimes_of_uniformCauchySeqOn`). This is the criterion "uniform
convergence in measure from convergence after each positive time" for the approximating clocks.

For the dyadic approximants of the reference cone the second condition holds almost surely for
every start (`ae_coneRef_lqgClockApprox_small_initial`). Hence, almost surely, at every start `z`
where the increments after positive times converge uniformly, the limit after positive times is an
LQG clock of the reference cone (`ae_coneRef_isLQGClock_of_uniformCauchySeqOn`). The uniform
convergence after positive times is kept as an explicit hypothesis.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric MarkovProcess
open Filter Topology Metric
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- The times `δ_n = (n + 1)⁻¹` tend to `0` from the right. -/
theorem tendsto_invSuccTime_nhdsGT_zero :
    Tendsto LatticeProb.invSuccTime atTop (𝓝[>] (0 : ℝ≥0)) :=
  tendsto_nhdsWithin_iff.2 ⟨(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).congr
    fun n => by rw [one_div]; rfl, Eventually.of_forall LatticeProb.invSuccTime_pos⟩

/-- **The LQG clock as the limit after positive times.** Let the circle averages `hε ε` of a
field be continuous at every dyadic scale `ε = 2^{-k}`. If, for planar Brownian motion from `z`,
the increments `A_k(t) - A_k(δ_n)` of the approximating LQG clocks after each time
`δ_n = (n + 1)⁻¹` form almost surely a uniform Cauchy sequence on every `[δ_n, T]`, and
`sup_k P_z(A_k(t) ≥ η) → 0` as `t ↓ 0` for every `η > 0`, then the limit of the approximating
clocks after positive times is an LQG clock of the field from `z`. -/
theorem isLQGClock_limitAfterPositiveTimes_of_uniformCauchySeqOn
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} (hcont : ∀ k : ℕ, Continuous (hε (HarmonicBalls.dyadicScale k)))
    {z : ℂ}
    (hpos : ∀ n : ℕ, ∀ T : ℝ≥0, ∀ᵐ b ∂(planarBrownianMotion z), UniformCauchySeqOn
      (fun k t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t
        - lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b (LatticeProb.invSuccTime n))
      atTop (Icc (LatticeProb.invSuccTime n) T))
    (hsmall : ∀ η : ℝ, 0 < η → Tendsto (fun t : ℝ≥0 => ⨆ k : ℕ, planarBrownianMotion z
      {b | η ≤ lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t}) (𝓝[>] 0) (𝓝 0)) :
    IsLQGClock planarBrownianMotion γ hε z
      (fun b => LatticeProb.limitAfterPositiveTimes
        (fun j => lqgClockApprox γ hε (HarmonicBalls.dyadicScale j) b)) := by
  intro T η hη
  have hmono : ∀ (k : ℕ) (b : ContinuousPath ℂ),
      Monotone (fun t : ℝ≥0 => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) :=
    fun k b => (strictMono_lqgClockApprox (γ := γ) (HarmonicBalls.dyadicScale_pos k)
      (hcont k) b).monotone
  exact LatticeProb.tendsto_measure_exists_le_abs_sub_limitAfterPositiveTimes
    (planarBrownianMotion z)
    (fun k b t => lqgClockApprox γ hε (HarmonicBalls.dyadicScale k) b t) hmono
    (fun k b t => (lqgClockApprox_zero γ hε _ b).symm.le.trans
      (hmono k b (by positivity : (0 : ℝ≥0) ≤ t)))
    (fun k b => continuous_lqgClockApprox_time (hcont k) b)
    (fun k t => measurable_lqgClockApprox (hcont k) t) hpos
    (fun η hη => (hsmall η hη).comp tendsto_invSuccTime_nhdsGT_zero) T hη

/-- **The LQG clock of the reference cone from convergence after positive times.** Almost surely,
for every start `z` at which the increments of the dyadic approximating LQG clocks of the
reference cone (built from `c (Y ω)` and `w ω`) after each time `δ_n = (n + 1)⁻¹` form almost
surely a uniform Cauchy sequence on every `[δ_n, T]`, their limit after positive times is an LQG
clock of the reference cone from `z`. The small initial values are supplied by the stopped heat
bound (`ae_coneRef_lqgClockApprox_small_initial`). -/
theorem ae_coneRef_isLQGClock_of_uniformCauchySeqOn
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      (∀ n : ℕ, ∀ T : ℝ≥0, ∀ᵐ b ∂(planarBrownianMotion z), UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
            (HarmonicBalls.dyadicScale k) b t
          - lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
            (HarmonicBalls.dyadicScale k) b (LatticeProb.invSuccTime n))
        atTop (Icc (LatticeProb.invSuccTime n) T)) →
      IsLQGClock planarBrownianMotion γ (coneRefCircle γ (c (Y ω)) (w ω)) z
        (fun b => LatticeProb.limitAfterPositiveTimes
          (fun j => lqgClockApprox γ (coneRefCircle γ (c (Y ω)) (w ω))
            (HarmonicBalls.dyadicScale j) b)) := by
  filter_upwards [ae_coneRef_lqgClockApprox_small_initial hY hp hc hcont hmeas hγ hγ2 w]
    with ω hω z hpos
  exact isLQGClock_limitAfterPositiveTimes_of_uniformCauchySeqOn
    (fun k => (continuousOn_coneRefCircle γ (hcont (Y ω)) (w ω)).comp_continuous
      (continuous_const.prodMk continuous_id)
      fun x => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩)
    hpos (hω z)

end MatedCRT.FirstPass.Derived
