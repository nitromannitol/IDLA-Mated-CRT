import LatticeProb.Prob.BrownianPointPolarity
import MatedCRT.FirstPass.LPBridge.PlanarBrownianSpace
import MatedCRT.FirstPass.Derived.ReferenceConeEnvironmentLimitClock

/-!
# Polarity of points for planar Brownian motion, and the limit-clock reference environment

Points are polar for planar Brownian motion: started at `z`, it almost surely never visits a point
`w ≠ z` (`LatticeProb.IsBrownianSpace.ae_forall_ne`, transported through the half-speed coordinates
`MatedCRT.PlanarBrownianSpace.halfSpeedPath`). In particular, from Lebesgue-almost every start, the
path almost surely avoids the origin. This discharges the polarity hypothesis of
`exists_reference_cone_environment_limitClock_of_coupling`.

## Main statements

* `planarBrownianMotion_ae_forall_ne`;
* `ae_planarBrownianMotion_ae_forall_ne_zero`;
* `exists_reference_cone_environment_limitClock_of_coupling_derived`.
-/

noncomputable section

open MeasureTheory Set Filter HarmonicBalls MarkovProcess LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT.Sec1

/-- **Points are polar for planar Brownian motion.** Planar Brownian motion started at `z` almost
surely never visits a point `w ≠ z`. -/
theorem planarBrownianMotion_ae_forall_ne {z w : ℂ} (hzw : z ≠ w) :
    ∀ᵐ b ∂(planarBrownianMotion z), ∀ t, b t ≠ w := by
  have hne : (0 : EuclideanSpace ℝ (Fin 2)) ≠ PlanarBrownianSpace.toEuclid (w - z) := by
    intro h
    have h' : w - z = 0 := PlanarBrownianSpace.toEuclid.injective (by rw [← h, map_zero])
    exact hzw (sub_eq_zero.1 h').symm
  filter_upwards [(PlanarBrownianSpace.isBrownianSpace_halfSpeedPath z).ae_forall_ne hne]
    with b hb t hbt
  apply hb (2 * t)
  have ht : (2⁻¹ : ℝ≥0) * (2 * t) = t := inv_mul_cancel_left₀ two_ne_zero t
  simp only [PlanarBrownianSpace.halfSpeedPath, ht, hbt]

/-- From Lebesgue-almost every start, planar Brownian motion almost surely never visits the
origin. -/
theorem ae_planarBrownianMotion_ae_forall_ne_zero :
    ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), ∀ t, b t ≠ 0 := by
  have h0 : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ 0 :=
    compl_mem_ae_iff.2 (measure_singleton (μ := (volume : Measure ℂ)) 0)
  filter_upwards [h0] with y hy
  exact planarBrownianMotion_ae_forall_ne hy

/-- `exists_reference_cone_environment_limitClock_of_coupling` with the polarity of the origin for
planar Brownian motion supplied by `ae_planarBrownianMotion_ae_forall_ne_zero`. -/
theorem exists_reference_cone_environment_limitClock_of_coupling_derived
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
        (∀ᵐ ω ∂S.P, ∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ →
          ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y),
            (∀ t ∈ Icc 0 h, b t ∈ Metric.closedBall a r) →
            UniformCauchySeqOn
              (fun k t => lqgClockApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale k) b t)
              atTop (Icc 0 h)) →
        (∀ᵐ ω ∂S.P, ∀ z : ℂ, ∀ᵐ b ∂(planarBrownianMotion z),
          StrictMono (S.clock ω b) ∧ Tendsto (S.clock ω b) atTop atTop) →
        S.IsValid 𝒮 γ) :=
  exists_reference_cone_environment_limitClock_of_coupling D hγ 𝒮
    ae_planarBrownianMotion_ae_forall_ne_zero

end MatedCRT.Sec1
