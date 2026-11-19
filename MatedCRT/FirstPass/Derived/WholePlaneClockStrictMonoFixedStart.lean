import MatedCRT.FirstPass.Derived.WholePlaneClockFixedStart
import MatedCRT.FirstPass.Derived.ConeClockStrictMono
import MatedCRT.FirstPass.Derived.LQGLimitClockShiftAdditive
import LatticeProb.Prob.LimitAfterPositiveTimesMeasurable

/-!
# Strict monotonicity of the limit clock from the fixed-start annealed statement

Berestycki (2015) proves, for a **fixed** starting point `y`, that almost surely for the joint law
of the field and the Brownian path the approximating Liouville clocks
`A_ε(t) = ∫_0^t ε^{γ²/2} e^{γ h_ε(B_s)} ds` converge and that the limiting clock is strictly
increasing. The reference-environment wrapper of the whole-plane clock binds the quenched form:
almost surely in the field, from Lebesgue-almost every start, almost surely in the path, the limit
clock `LatticeProb.limitAfterPositiveTimes` of the dyadic clocks is strictly increasing.

This file derives the quenched form from the fixed-start annealed one by Fubini's theorem
(`ae_ae_ae_of_ae_prod_kernel`). The swap needs a measurable event; strict monotonicity of the limit
clock is not obviously measurable, so we intersect it with the event `U` that the dyadic clocks are
uniformly Cauchy on every `[0, N]`. On `U` the limit clock is the pointwise limit of nondecreasing
clocks, hence nondecreasing, and a nondecreasing function is strictly increasing as soon as it is
strictly increasing along pairs of rational times. This identifies the intersection with a
countable intersection of measurable events.

## Main statements

* `measurableSet_uniformCauchy_strictMono_limitAfterPositiveTimes_field`: joint measurability in
  the field and the path of the event "uniformly Cauchy on every `[0, N]` and strictly increasing
  limit clock".
* `ae_ae_ae_strictMono_limitAfterPositiveTimes_of_fixedStart`: the quenched strict monotonicity
  from the fixed-start annealed statements.
* `ae_strictMono_wholePlane_of_fixedStart`: the same, in the form of the strict-monotonicity
  hypothesis of the whole-plane reference-environment wrapper.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter HarmonicBalls LQGMetric MarkovProcess
open MatedCRT.LQGClockApproxMeasurable
open scoped NNReal

namespace MatedCRT.Sec1

/-- A nondecreasing function on `ℝ≥0` that is strictly increasing along all pairs of times of the
form `q.toNNReal` with `q` rational is strictly increasing. -/
theorem strictMono_of_monotone_of_rat {L : ℝ≥0 → ℝ} (hL : Monotone L)
    (hq : ∀ q₁ q₂ : ℚ, Real.toNNReal q₁ < Real.toNNReal q₂ →
      L (Real.toNNReal q₁) < L (Real.toNNReal q₂)) : StrictMono L := by
  intro s t hst
  have hst' : (s : ℝ) < t := hst
  obtain ⟨q₁, hsq₁, hq₁t⟩ := exists_rat_btwn hst'
  obtain ⟨q₂, hq₁q₂, hq₂t⟩ := exists_rat_btwn hq₁t
  have hq₁0 : (0 : ℝ) < q₁ := lt_of_le_of_lt s.2 hsq₁
  have h1 : s ≤ Real.toNNReal q₁ := (Real.lt_toNNReal_iff_coe_lt.2 hsq₁).le
  have h2 : Real.toNNReal q₂ ≤ t := Real.toNNReal_le_iff_le_coe.2 hq₂t.le
  have h12 : Real.toNNReal q₁ < Real.toNNReal q₂ :=
    (Real.toNNReal_lt_toNNReal_iff (hq₁0.trans hq₁q₂)).2 hq₁q₂
  exact (hL h1).trans_lt ((hq q₁ q₂ h12).trans_le (hL h2))

/-- **Joint measurability of the strict-monotonicity event on the uniform-Cauchy event.** If the
circle averages `F x ε` at every dyadic scale are continuous in the point and jointly measurable in
the field and the point, then the event that the dyadic approximating clocks of the field `x` along
the path `b` are uniformly Cauchy on every `[0, N]` and that their limit clock is strictly
increasing is measurable in `(x, b)`. -/
theorem measurableSet_uniformCauchy_strictMono_limitAfterPositiveTimes_field {X : Type*}
    [MeasurableSpace X] {γ : ℝ} {F : X → ℝ → ℂ → ℝ}
    (hcont : ∀ x k, Continuous (F x (HarmonicBalls.dyadicScale k)))
    (hm : ∀ k, Measurable fun q : X × ℂ => F q.1 (HarmonicBalls.dyadicScale k) q.2) :
    MeasurableSet {p : X × ContinuousPath ℂ |
      (∀ N : ℕ, UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t) atTop
          (Icc 0 (N : ℝ≥0))) ∧
      StrictMono (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t)} := by
  have hA : ∀ k t, Measurable fun p : X × ContinuousPath ℂ =>
      lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t := fun k t => by
    have h0 := measurable_lqgClockApprox_field_path_time_of_scale (c := F) γ (hm k)
    have h1 : Measurable fun p : X × ContinuousPath ℂ => (p.1, p.2, t) :=
      measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
    exact h0.comp h1
  have hL : ∀ t, Measurable fun p : X × ContinuousPath ℂ => LatticeProb.limitAfterPositiveTimes
      (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t) t :=
    LatticeProb.measurable_limitAfterPositiveTimes
      (a := fun (p : X × ContinuousPath ℂ) (k : ℕ) (t : ℝ≥0) =>
        lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t) hA
  have hEq : {p : X × ContinuousPath ℂ |
      (∀ N : ℕ, UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t) atTop
          (Icc 0 (N : ℝ≥0))) ∧
      StrictMono (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t)} =
      (⋂ N : ℕ, {p : X × ContinuousPath ℂ | UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t) atTop
          (Icc 0 (N : ℝ≥0))}) ∩
      ⋂ q₁ : ℚ, ⋂ q₂ : ℚ, ⋂ (_ : Real.toNNReal q₁ < Real.toNNReal q₂),
        {p : X × ContinuousPath ℂ |
          LatticeProb.limitAfterPositiveTimes
            (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t)
              (Real.toNNReal q₁) <
          LatticeProb.limitAfterPositiveTimes
            (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t)
              (Real.toNNReal q₂)} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hU, hS⟩
      exact ⟨hU, fun q₁ q₂ h => hS h⟩
    · rintro ⟨hU, hq⟩
      refine ⟨hU, strictMono_of_monotone_of_rat ?_ hq⟩
      have hc : ∀ k, Continuous fun t =>
          lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t := fun k =>
        continuous_lqgClockApprox_field F γ _ p.1 (hcont p.1 k) p.2
      have h0 : ∀ k, lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 0 = 0 :=
        fun k => by simp [lqgClockApprox]
      have hlim := MatedCRT.FirstPass.Derived.tendsto_limitAfterPositiveTimes_of_uniformCauchySeqOn
        hc h0 hU
      intro s t hst
      exact le_of_tendsto_of_tendsto' (hlim s) (hlim t) fun k =>
        MatedCRT.FirstPass.Derived.LQGLimitClockShift.monotone_lqgClockApprox
          (HarmonicBalls.dyadicScale_pos k).le (hcont p.1 k) p.2 hst
  rw [hEq]
  exact (MeasurableSet.iInter fun N =>
      measurableSet_uniformCauchySeqOn_lqgClockApprox_field hcont hm _).inter
    (MeasurableSet.iInter fun q₁ => MeasurableSet.iInter fun q₂ =>
      MeasurableSet.iInter fun _ => measurableSet_lt (hL _) (hL _))

/-- **Quenched strict monotonicity from the fixed-start annealed statements.** Suppose that for
every horizon `T`, from Lebesgue-almost every start `y`, the dyadic approximating clocks of the
field `F ω` along the path `b` are uniformly Cauchy on `[0, T]` for almost every `(ω, b)` under the
product of the field law and planar Brownian motion started at `y`, and that from
Lebesgue-almost every start the limit clock is strictly increasing for almost every `(ω, b)`
(Berestycki 2015, fixed starting point). Then almost surely in the field, from Lebesgue-almost
every start, almost surely in the path, the limit clock is strictly increasing. -/
theorem ae_ae_ae_strictMono_limitAfterPositiveTimes_of_fixedStart {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [SFinite P'] {γ : ℝ} {F : Ω' → ℝ → ℂ → ℝ}
    (hcont : ∀ ω k, Continuous (F ω (HarmonicBalls.dyadicScale k)))
    (hm : ∀ k, Measurable fun q : Ω' × ℂ => F q.1 (HarmonicBalls.dyadicScale k) q.2)
    (hfix : ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      UniformCauchySeqOn (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t)
        atTop (Icc 0 T))
    (hfixsm : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      StrictMono (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t)) :
    ∀ᵐ ω ∂P', ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
      StrictMono (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ (F ω) (HarmonicBalls.dyadicScale k) b t) := by
  have hS := measurableSet_uniformCauchy_strictMono_limitAfterPositiveTimes_field
    (γ := γ) hcont hm
  have h1 : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      p ∈ {p : Ω' × ContinuousPath ℂ |
        (∀ N : ℕ, UniformCauchySeqOn
          (fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t) atTop
            (Icc 0 (N : ℝ≥0))) ∧
        StrictMono (LatticeProb.limitAfterPositiveTimes
          fun k t => lqgClockApprox γ (F p.1) (HarmonicBalls.dyadicScale k) p.2 t)} := by
    filter_upwards [ae_all_iff.2 fun N : ℕ => hfix N, hfixsm] with y hy hsm
    filter_upwards [ae_all_iff.2 hy, hsm] with p hp hp'
    exact ⟨hp, hp'⟩
  filter_upwards [ae_ae_ae_of_ae_prod_kernel planarBrownianMotion hS h1] with ω hω
  filter_upwards [hω] with y hy
  filter_upwards [hy] with b hb
  exact hb.2

/-- **The strict-monotonicity hypothesis of the whole-plane wrapper from the fixed-start
statements.** For a measurable field `Y'` and a version `c'` of its circle averages that is
continuous at positive radii and jointly measurable, the quenched strict monotonicity of the limit
clock (almost surely in the field, from Lebesgue-almost every start, almost surely in the path)
follows from the fixed-start annealed uniform-Cauchy and strict-monotonicity statements. -/
theorem ae_strictMono_wholePlane_of_fixedStart {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [SFinite P'] {γ : ℝ} {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ}
    (hY : Measurable Y')
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2))
    (hfix : ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
        atTop (Icc 0 T))
    (hfixsm : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      StrictMono (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)) :
    ∀ᵐ ω' ∂P', ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
      StrictMono (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ (c' (Y' ω')) (HarmonicBalls.dyadicScale k) b t) := by
  have hc : ∀ x k, Continuous (c' x (HarmonicBalls.dyadicScale k)) := fun x k =>
    (hcont x).comp_continuous (continuous_const.prodMk continuous_id)
      fun z => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ z⟩
  have hm : ∀ k, Measurable fun q : Ω' × ℂ =>
      c' (Y' q.1) (HarmonicBalls.dyadicScale k) q.2 := fun k =>
    hmeas.comp (((measurable_const : Measurable fun _ : Ω' × ℂ =>
      (⟨HarmonicBalls.dyadicScale k, HarmonicBalls.dyadicScale_pos k⟩ : Ioi (0 : ℝ))).prodMk
        measurable_snd).prodMk (hY.comp measurable_fst))
  exact ae_ae_ae_strictMono_limitAfterPositiveTimes_of_fixedStart
    (F := fun ω => c' (Y' ω)) (fun ω k => hc (Y' ω) k) hm hfix hfixsm

end MatedCRT.Sec1
