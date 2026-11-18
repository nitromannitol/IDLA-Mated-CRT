import MatedCRT.FirstPass.Derived.ConeReferenceClockLocalChain
import MatedCRT.FirstPass.Derived.ReferenceConeEnvironment

/-!
# Reference cone environments with the limiting LQG clock

`exists_reference_cone_environment_of_coupling` builds, from a mating-of-trees coupling, a reference
cone environment for an arbitrary clock and reduces its validity to the SLE property and the
all-start clock property. Here the clock is chosen as the limit after positive times of the dyadic
approximating LQG clocks `A^k(b, t)` of Berestycki 2015 (`LatticeProb.limitAfterPositiveTimes`), and
the all-start clock property is reduced, through `ae_coneRef_isLQGClock_continuous_monotone_of_local`,
to

* the polarity of the origin for planar Brownian motion from Lebesgue-almost every start;
* the local convergence of the dyadic clocks of the cone field: almost surely in the field, for every
  closed disc avoiding the origin and every time horizon, from Lebesgue-almost every start, the dyadic
  clocks are uniformly Cauchy on `[0, h]` on the event that the path stays in the disc (the localized
  form of Berestycki 2015, Theorem 1.2);
* the strict monotonicity and the infinite lifetime of the limiting clock, from every start.

The limiting clock starts at `0`, is continuous and is an LQG clock at every start by the chain
argument; the remaining two clauses of `IsTimeChangeClock` are the third item.

## Main statement

* `exists_reference_cone_environment_limitClock_of_coupling`.
-/

noncomputable section

open MeasureTheory Set Filter HarmonicBalls MarkovProcess LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT.Sec1

/-- The reference cone environment of a mating-of-trees coupling whose clock is the limit after
positive times of the dyadic approximating LQG clocks. It is valid as soon as the curve is an SLE,
the dyadic clocks of the cone field converge locally on discs avoiding the origin (from
Lebesgue-almost every start), and the limiting clock is strictly increasing with infinite lifetime
from every start; the polarity of the origin for planar Brownian motion is an explicit hypothesis. -/
theorem exists_reference_cone_environment_limitClock_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (𝒮 : SpaceFillingSLEModel)
    (hpolar : ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), ∀ t, b t ≠ 0) :
    ∃ S : MatedCRTEnv Ω,
      S.P = P ∧ S.bm = bm ∧ S.η = (fun ω => ⇑(η ω)) ∧
      (∀ ω b, S.clock ω b = LatticeProb.limitAfterPositiveTimes
        (fun j => lqgClockApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale j) b)) ∧
      IsQuantumCone γ S.P S.hC S.hcirc ∧ IsLQGMeasure S.P γ S.hcirc S.μ ∧
      (∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω ∧ ∀ φ : TestC,
        S.hC ω ⇑φ = coneField (X ω)
          (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) ∧
      (𝒮.IsSLE S.P S.fieldSigma (16 / γ ^ 2) S.η →
        (∀ᵐ ω ∂S.P, ∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ →
          ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
            (∀ t ∈ Icc 0 h, b t ∈ Metric.closedBall a r) →
            UniformCauchySeqOn
              (fun k t => lqgClockApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale k) b t)
              atTop (Icc 0 h)) →
        (∀ᵐ ω ∂S.P, ∀ z : ℂ, ∀ᵐ b ∂(planarBrownianMotion z),
          StrictMono (S.clock ω b) ∧ Tendsto (S.clock ω b) atTop atTop) →
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
  intro hSLE hloc hstrict
  refine S.isValid_of_matching_coupling hγ D hcone hμcone hSLE ?_ hmatch
  filter_upwards [MatedCRT.FirstPass.Derived.ae_coneRef_isLQGClock_continuous_monotone_of_local
    hG hhC hc hcont hmeas hγ.1 hγ.2 F hpolar, hloc, hstrict] with ω hω hlocω hstrictω
  intro z
  obtain ⟨hclk, hae⟩ := hω hlocω z
  refine ⟨hclk, ?_⟩
  filter_upwards [hae, hstrictω z] with b hb hs
  exact ⟨hb.1, hb.2.1, hs.1, hs.2⟩

end MatedCRT.Sec1
