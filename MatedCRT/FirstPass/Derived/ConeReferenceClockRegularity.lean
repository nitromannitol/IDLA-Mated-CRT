import MatedCRT.FirstPass.Derived.ConeReferenceClockAfterPositiveTimes
import HarmonicBalls.Proofs.Potential.LQGClockUniformSubsequence

/-!
# Continuity and monotonicity of the LQG clock of the reference cone

If `F` is an LQG clock of a field whose circle averages are continuous at every dyadic scale, then
almost surely the clock `t ↦ F(b, t)` of a planar Brownian path is continuous and nondecreasing
(`ae_continuous_monotone_of_isLQGClock`): a deterministic subsequence of the approximating clocks
`A_k(b, t) = ∫_0^t ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds` converges almost surely uniformly on every
bounded time interval (`IsLQGClock.exists_seq_locally_uniform_clockApprox`), and each `A_k(b, ·)`
is continuous and increasing.

For the reference cone this gives, almost surely, at every start `z` where the increments of the
dyadic approximating clocks after positive times are uniformly Cauchy: the limit after positive
times is an LQG clock from `z`, and `Q_z`-almost every path has a continuous nondecreasing clock
starting at `0` (`ae_coneRef_isLQGClock_continuous_monotone_of_uniformCauchySeqOn`). Strict
monotonicity and divergence of the clock are not addressed here.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric MarkovProcess
open Filter Topology Metric
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- **An LQG clock is almost surely continuous and nondecreasing.** If the circle averages
`hε ε` are continuous at every dyadic scale `ε = 2^{-k}` and `F` is an LQG clock of the field from
`x`, then for planar Brownian motion from `x`, almost every path has a continuous nondecreasing
clock `t ↦ F(b, t)`. -/
theorem ae_continuous_monotone_of_isLQGClock
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hε (HarmonicBalls.dyadicScale k)))
    (hclock : IsLQGClock planarBrownianMotion γ hε x F) :
    ∀ᵐ b ∂(planarBrownianMotion x), Continuous (F b) ∧ Monotone (F b) := by
  obtain ⟨s, -, hs⟩ := hclock.exists_seq_locally_uniform_clockApprox
  filter_upwards [hs] with b hb
  -- pointwise convergence along the subsequence
  have htend : ∀ t : ℝ≥0, Tendsto (fun n => lqgClockApprox γ hε (HarmonicBalls.dyadicScale (s n))
      b t) atTop (𝓝 (F b t)) := fun t =>
    Metric.tendsto_nhds.2 fun η hη =>
      (hb t η hη).mono fun n hn => by rw [Real.dist_eq]; exact hn t le_rfl
  refine ⟨continuous_iff_continuousAt.2 fun t => ?_, fun t₁ t₂ h => ?_⟩
  · have hunif : TendstoUniformlyOn
        (fun n => fun u : ℝ≥0 => lqgClockApprox γ hε (HarmonicBalls.dyadicScale (s n)) b u)
        (F b) atTop (Iic (t + 1)) :=
      Metric.tendstoUniformlyOn_iff.2 fun η hη =>
        (hb (t + 1) η hη).mono fun n hn u hu => by
          rw [dist_comm, Real.dist_eq]; exact hn u hu
    have hon : ContinuousOn (F b) (Iic (t + 1)) :=
      hunif.continuousOn (Eventually.of_forall fun n =>
        (continuous_lqgClockApprox_time (hcont (s n)) b).continuousOn).frequently
    exact hon.continuousAt (Iic_mem_nhds (lt_add_one t))
  · exact le_of_tendsto_of_tendsto' (htend t₁) (htend t₂) fun n =>
      (strictMono_lqgClockApprox (γ := γ) (HarmonicBalls.dyadicScale_pos (s n))
        (hcont (s n)) b).monotone h

/-- **Regularity of the LQG clock of the reference cone.** Almost surely, for every start `z` at
which the increments of the dyadic approximating LQG clocks of the reference cone (built from
`c (Y ω)` and `w ω`) after each time `δ_n = (n + 1)⁻¹` are almost surely uniformly Cauchy on every
`[δ_n, T]`, their limit `F` after positive times is an LQG clock of the reference cone from `z`,
and for `Q_z`-almost every path `b` the clock `F(b, ·)` starts at `0`, is continuous and is
nondecreasing. -/
theorem ae_coneRef_isLQGClock_continuous_monotone_of_uniformCauchySeqOn
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
  filter_upwards [ae_coneRef_isLQGClock_of_uniformCauchySeqOn hY hp hc hcont hmeas hγ hγ2 w]
    with ω hω z hpos
  have hclock := hω z hpos
  have hcontk : ∀ k : ℕ,
      Continuous (coneRefCircle γ (c (Y ω)) (w ω) (HarmonicBalls.dyadicScale k)) := fun k =>
    (continuousOn_coneRefCircle γ (hcont (Y ω)) (w ω)).comp_continuous
      (continuous_const.prodMk continuous_id)
      fun x => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  refine ⟨hclock, ?_⟩
  filter_upwards [ae_continuous_monotone_of_isLQGClock hcontk hclock] with b hb
  exact ⟨LatticeProb.limitAfterPositiveTimes_zero _, hb⟩

end MatedCRT.FirstPass.Derived
