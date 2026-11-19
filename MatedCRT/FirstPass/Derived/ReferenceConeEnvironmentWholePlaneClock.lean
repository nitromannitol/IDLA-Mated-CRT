import MatedCRT.FirstPass.Derived.PlanarBrownianPointPolarity
import MatedCRT.FirstPass.Derived.ConeClockUniformCauchy
import MatedCRT.FirstPass.Derived.LQGLimitClockAdapted
import MatedCRT.FirstPass.Derived.LQGLimitClockGoodSet
import MatedCRT.FirstPass.Derived.PlanarBrownianAdditiveClockDivergence

/-!
# Reference cone environments: the clock hypotheses for the whole-plane field

`exists_reference_cone_environment_limitClock_of_coupling_derived` reduces the validity of the
limit-clock reference cone environment of a mating-of-trees coupling to the SLE property and two
clock hypotheses on the cone field: the local convergence of its dyadic clocks on discs avoiding the
origin, and the strict monotonicity and infinite lifetime of its limiting clock from every start.
Here these are reduced as follows.

* The local convergence is required only for a **whole-plane** Gaussian free field: for every
  normalized whole-plane GFF `Y` and every jointly continuous version `c` of its circle averages,
  almost surely, for every closed disc avoiding the origin and every horizon, from Lebesgue-almost
  every start, the dyadic clocks of `c (Y ω)` are uniformly Cauchy on `[0, h]` on the event that the
  Brownian path stays in the disc (the localized form of Berestycki 2015, Theorem 1.2). It is
  transferred to the cone field by `coneRefCircle_localUniformCauchy`.
* The strict monotonicity of the limiting cone clock is required only from Lebesgue-almost every
  start; it then holds from every start by `ae_coneRef_strictMono_of_local`.
* The infinite lifetime is proved: the limiting clock is adapted
  (`measurable_limitAfterPositiveTimes_lqgClockApprox_canonicalFiltration`), positive at time `1/2`
  from almost every start, nondecreasing and additive under the time shift
  (`ae_coneRef_monotone_and_shift_of_local`), so it tends to infinity
  (`planarBrownianMotion_ae_tendsto_atTop_of_additive`).

## Main statement

* `exists_reference_cone_environment_limitClock_of_coupling_wholePlane`.
-/

noncomputable section

open MeasureTheory Set Filter HarmonicBalls MarkovProcess LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT.Sec1

/-- The limit-clock reference cone environment of a mating-of-trees coupling is valid as soon as the
curve is an SLE, the dyadic clocks of every normalized whole-plane Gaussian free field (through any
jointly continuous version of its circle averages) converge locally on discs avoiding the origin
from Lebesgue-almost every start, and the limiting cone clock is strictly increasing from
Lebesgue-almost every start. -/
theorem exists_reference_cone_environment_limitClock_of_coupling_wholePlane
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (𝒮 : SpaceFillingSLEModel) :
    ∃ S : MatedCRTEnv Ω,
      S.P = P ∧ S.bm = bm ∧ S.η = (fun ω => ⇑(η ω)) ∧
      (∀ ω b, S.clock ω b = LatticeProb.limitAfterPositiveTimes
        (fun j => lqgClockApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale j) b)) ∧
      IsQuantumCone γ S.P S.hC S.hcirc ∧ IsLQGMeasure S.P γ S.hcirc S.μ ∧
      (∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω ∧ ∀ φ : TestC,
        S.hC ω ⇑φ = coneField (X ω)
          (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) ∧
      (𝒮.IsSLE S.P S.fieldSigma (16 / γ ^ 2) S.η →
        (∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
            {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
            IsNormalizedWPGFF Y' P' →
            (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
            (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
            Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
            ∀ᵐ ω' ∂P', ∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ →
              ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
                (∀ t ∈ Icc 0 h, b t ∈ Metric.closedBall a r) →
                UniformCauchySeqOn
                  (fun k t => lqgClockApprox γ (c' (Y' ω')) (HarmonicBalls.dyadicScale k) b t)
                  atTop (Icc 0 h)) →
        (∀ᵐ ω ∂S.P, ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
          StrictMono (S.clock ω b)) →
        S.IsValid 𝒮 γ) := by
  obtain ⟨R, W, F, hC, c, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw,
    hG, hind, hpair, hhC, hc, hcont, hmeas, hcone, hobs, μ, hμmap, hμpull,
    hμcone, hmatching⟩ := exists_reference_cone_observables_with_matching_area D hγ.1 hγ.2
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  let Y : Ω → DistC := MatedCRTHarmonic.GMCFacts.replField X
    (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩)
  let S : MatedCRTEnv Ω := {
    P := P
    hC := fun ω => MatedCRT.FirstPass.Derived.coneRefPairing γ (hC (Y ω)) (c (Y ω)) (F ω)
    hcirc := fun ω => MatedCRT.FirstPass.Derived.coneRefCircle γ (c (Y ω)) (F ω)
    μ := fun ω => MatedCRT.FirstPass.Derived.coneRefMeasure γ (c (Y ω)) (F ω) (μ (Y ω))
    η := fun ω => η ω
    clock := fun ω b => LatticeProb.limitAfterPositiveTimes
      (fun j => lqgClockApprox γ (MatedCRT.FirstPass.Derived.coneRefCircle γ (c (Y ω)) (F ω))
        (HarmonicBalls.dyadicScale j) b)
    bm := bm }
  have hmatch : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω ∧ ∀ φ : TestC,
      S.hC ω ⇑φ = coneField (X ω)
        (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ := by
    filter_upwards [hmatching] with ω hω
    exact ⟨rfl, hω.1⟩
  refine ⟨S, rfl, rfl, rfl, fun _ _ => rfl, hcone, hμcone, hmatch, ?_⟩
  intro hSLE hWP hsm
  have hpolar := ae_planarBrownianMotion_ae_forall_ne_zero
  have hloc : ∀ᵐ ω ∂P, ∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ →
      ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
        (∀ t ∈ Icc 0 h, b t ∈ Metric.closedBall a r) →
        UniformCauchySeqOn
          (fun k t => lqgClockApprox γ (MatedCRT.FirstPass.Derived.coneRefCircle γ (c (Y ω)) (F ω))
            (HarmonicBalls.dyadicScale k) b t)
          atTop (Icc 0 h) := by
    filter_upwards [hWP hG hc hcont hmeas] with ω hω
    exact MatedCRT.FirstPass.Derived.coneRefCircle_localUniformCauchy γ (hcont (Y ω)) (F ω) hω
  refine S.isValid_of_matching_coupling hγ D hcone hμcone hSLE ?_ hmatch
  filter_upwards [MatedCRT.FirstPass.Derived.ae_coneRef_isLQGClock_continuous_monotone_of_local
      hG hhC hc hcont hmeas hγ.1 hγ.2 F hpolar,
    MatedCRT.FirstPass.Derived.ae_coneRef_strictMono_of_local
      hG hhC hc hcont hmeas hγ.1 hγ.2 F hpolar,
    MatedCRT.FirstPass.Derived.ae_coneRef_monotone_and_shift_of_local
      hG hhC hc hcont hmeas hγ.1 hγ.2 F hpolar, hloc, hsm] with ω hω hsω haω hlocω hsmω
  intro z
  obtain ⟨hclk, hae⟩ := hω hlocω z
  refine ⟨hclk, ?_⟩
  have hcontk : ∀ k : ℕ, Continuous
      (MatedCRT.FirstPass.Derived.coneRefCircle γ (c (Y ω)) (F ω) (HarmonicBalls.dyadicScale k)) :=
    fun k => (MatedCRT.FirstPass.Derived.continuousOn_coneRefCircle γ (hcont (Y ω)) (F ω)).comp_continuous
      (continuous_const.prodMk continuous_id)
      fun x => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ _⟩
  have hFm' := MatedCRT.LQGClockApproxAdapted.measurable_limitAfterPositiveTimes_lqgClockApprox_canonicalFiltration
    γ (fun j => (hcontk j).measurable) 2⁻¹
  have hpos := MatedCRT.FirstPass.Derived.LQGLimitClockShift.ae_ae_pos_limitAfterPositiveTimes_of_strictMono
    (Q := planarBrownianMotion)
    (a := fun b k t => lqgClockApprox γ (MatedCRT.FirstPass.Derived.coneRefCircle γ (c (Y ω)) (F ω))
      (HarmonicBalls.dyadicScale k) b t) hsmω (t := 2⁻¹) (by norm_num)
  have htend := MatedCRT.KilledOccupation.planarBrownianMotion_ae_tendsto_atTop_of_additive
    (F := fun b => LatticeProb.limitAfterPositiveTimes fun k t =>
      lqgClockApprox γ (MatedCRT.FirstPass.Derived.coneRefCircle γ (c (Y ω)) (F ω))
        (HarmonicBalls.dyadicScale k) b t) hFm' hpos z (haω hlocω z)
  filter_upwards [hae, hsω hlocω hsmω z, htend] with b hb hs ht
  exact ⟨hb.1, hb.2.1, hs, ht⟩

end MatedCRT.Sec1
