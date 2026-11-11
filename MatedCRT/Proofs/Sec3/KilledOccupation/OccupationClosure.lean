import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationAssembly
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockProof
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockFinite

/-!
# Frozen killed-occupation input of the Green function, with the Appendix B binders discharged

`frozenLBMGreenOccupationRescaled_closed` is `frozenLBMGreenOccupationRescaled_of_appendixB`
(OccupationAssembly.lean:178) with the binders that have a committed concluder discharged:

* `hExit` (planar Brownian motion leaves the disc in finite time, a.s.) by `planar_exit_ae_lt_top`
  (ClockFinite.lean:412);
* `hBase` (the base occupation identity of Lemma `lem:occ-base`) by `baseOccupationIdentity_of_GMC`
  (BaseClockProof.lean:1304). Its GMC binders are the named binders `hS0`, `hτ`, `hτmeas`, `hGint`, `hσint`,
  `hw`, `hVar`, `hνmeas`, `hconvB1`, `hLjoint`, `hLpath`; `hGmeas` is `measurable_greenFunction` (Harmonic-Balls
  Proofs/Sec4/GreenAwayFromPole.lean), `hDB` is the inclusion `ball 0 ρ ⊆ ball 0 1`, and `hmeasKernel` is the
  binder `hMeas` of the appendix.

The binders kept as named hypotheses are `hm0`, `hWeight`, `hMeas`, `hS6`, `hBG` (Appendix B inputs) and `hGreen`
(the Green disc formula `GreenDiskFormula`, Potential.lean:34; no committed concluder).

The binder `hS0` is the Prop `KilledBrownianOccupationOnBall` (Potential.lean:275), the classical occupation formula
for planar Brownian motion killed on exiting a disc (Green potential of the disc, Armitage-Gardiner); it has no
committed concluder and is the same input as `regClock_identification_closed` (ClockClosure.lean:118).
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric MarkovProcess ProbabilityTheory
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- **Frozen killed-occupation input of the Green function** (`FrozenLBMGreenOccupationRescaled`), with the
Appendix B binders `hExit` and `hBase` discharged and the GMC binders of `baseOccupationIdentity_of_GMC` named. -/
theorem frozenLBMGreenOccupationRescaled_closed (𝒮 : SpaceFillingSLEModel)
    (ν : (γ : ℝ) → (Ω : Type) → [MeasurableSpace Ω] → MatedCRTEnv Ω → Ω → Measure ℂ)
    (dA : (γ : ℝ) → (Ω : Type) → [MeasurableSpace Ω] → MatedCRTEnv Ω → Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hm0 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → 0 < S.m₀)
    (hWeight : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → OccWeightIdentity S.P S.μ (ν γ Ω S) γ)
    (hMeas : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᵐ ω ∂S.P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
        Measurable fun b => ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(dA γ Ω S ω b))
    (hS6 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, ∀ s ≤ exitNN z r b,
        S.clock ω b s = (weightedClock (dA γ Ω S ω b) (fun u => gammaWeight γ (b u)) (exitNN z r b) s).toReal)
    (hBG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∃ e : ℝ, 0 < e ∧ BGMassUpperBoundDyadic S.P S.μ e)
    (hGreen : ∀ ρ : ℝ, ∀ z : ℂ, ∀ r : ℝ, 0 < r → ball z r ⊆ ball 0 ρ → GreenDiskFormula z r)
    (hS0 : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (z : ℂ) (r : ℝ), 0 < r → ball z r ⊆ ball 0 ρ →
      KilledBrownianOccupationOnBall z r)
    (hτ : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (z y : ℂ) (r : ℝ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      Integrable (fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toReal) (planarBrownianMotion y))
    (hτmeas : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (z : ℂ) (r : ℝ), 0 < r → ball z r ⊆ ball 0 ρ →
      Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b)
    (hGint : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (z y : ℂ) (r : ℝ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      IntegrableOn (fun x => greenFunction (ball z r) y x) (ball z r))
    (hσint : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (z y : ℂ) (r : ℝ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∫⁻ b, ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) ∂planarBrownianMotion y ≠ ⊤)
    (hw : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ S.hcirc p.1 k p.2)
    (hVar : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᶠ k in atTop, ∀ x ∈ ball z r, ∫⁻ ω, ENNReal.ofReal (circleWeight γ S.hcirc ω k x) ∂S.P = 1)
    (hνmeas : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν γ Ω S ω))
    (hconvB1 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) →
      (∀ x ∉ ball 0 1, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ S.hcirc ω k)) (∫⁻ x, ρ x ∂(ν γ Ω S ω)) ∂S.P)
        atTop (𝓝 0))
    (hLjoint : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ q : ℂ → ℝ≥0∞, Measurable q →
        Measurable fun p : Ω × ContinuousPath ℂ => limitClockFun (dA γ Ω S) z r p.1 p.2 q)
    (hLpath : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
        ∀ᵐ b ∂planarBrownianMotion y,
          Tendsto (fun k => clockGapMean S.P γ S.hcirc (dA γ Ω S) z r k q b) atTop (𝓝 0)) :
    FrozenLBMGreenOccupationRescaled 𝒮 := by
  have hExit : ∀ (z y : ℂ) (r : ℝ), 0 < r → y ∈ ball z r →
      ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion y, pathExitTime (ball z r) ⇑b < ⊤ :=
    fun z y r _ _ => planar_exit_ae_lt_top y z r
  have hBase : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      BaseOccupationIdentity S.P (planarBrownianMotion y) (ball z r) (greenFunction (ball z r) y)
        (ν γ Ω S) (dA γ Ω S) (exitNN z r) := by
    intro γ hγ0 hγ2 ρ hρ0 hρ1 Ω _ S hS r z y hr hball hy
    have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
    exact baseOccupationIdentity_of_GMC S.P γ S.hcirc z r hy
      (hball.trans (Metric.ball_subset_ball hρ1.le))
      (hS0 ρ hρ0 hρ1 z r hr hball)
      (hτ ρ hρ0 hρ1 z y r hr hball hy)
      (hτmeas ρ hρ0 hρ1 z r hr hball)
      (measurable_greenFunction isOpen_ball y)
      (hGint ρ hρ0 hρ1 z y r hr hball hy)
      (hw γ hγ0 hγ2 Ω S hS)
      (hVar γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
      (ν γ Ω S) (dA γ Ω S)
      (hνmeas γ hγ0 hγ2 Ω S hS)
      (hconvB1 γ hγ0 hγ2 Ω S hS)
      (hLjoint γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
      (hMeas γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
      (hLpath γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
      (hσint ρ hρ0 hρ1 z y r hr hball hy)
  exact frozenLBMGreenOccupationRescaled_of_appendixB 𝒮 ν dA hm0 hBase hWeight hMeas hS6 hBG hGreen hExit

end MatedCRT.KilledOccupation
