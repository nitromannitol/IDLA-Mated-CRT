import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosure
import MatedCRT.Proofs.Sec3.KilledOccupation.GreenDisk
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockBinders

/-!
# Frozen killed-occupation input of the Green function, with the Green disc formula and the exit-time binders discharged

`frozenLBMGreenOccupationRescaled_closed2` is `frozenLBMGreenOccupationRescaled_closed` (OccupationClosure.lean:35)
with these binders discharged, the others unchanged (same names and types):

* `hGreen`, the Green disc formula `GreenDiskFormula z r` (Potential.lean:34), by `greenDiskFormula` (GreenDisk.lean),
  the Green function of the disc `B_r(z)` in the explicit form of Armitage-Gardiner, Section 4.1;
* `hτ`, `hτmeas`, `hGint`, `hσint` (integrability and measurability of the exit time `pathExitTime (ball z r)` and of
  the Green function `greenFunction (ball z r) y`, Appendix B textbook binders) by `baseOccupationIdentity_of_GMC'`
  (BaseClockBinders.lean:228), which is `baseOccupationIdentity_of_GMC` (BaseClockProof.lean:1304) with them proved;
* `hExit` (planar Brownian motion leaves the disc in finite time a.s.) by `planar_exit_ae_lt_top` (ClockFinite.lean:412).

The proof is that of `frozenLBMGreenOccupationRescaled_closed` (OccupationClosure.lean:81-112), with `hBase` built from
`baseOccupationIdentity_of_GMC'` and fed to `frozenLBMGreenOccupationRescaled_of_appendixB` (OccupationAssembly.lean:178).
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric MarkovProcess ProbabilityTheory
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- **Frozen killed-occupation input of the Green function** (`FrozenLBMGreenOccupationRescaled`), with the
Green disc formula `hGreen` discharged by `greenDiskFormula`, the exit-time and Green-function binders of
`baseOccupationIdentity_of_GMC` discharged by `baseOccupationIdentity_of_GMC'`, and `hExit` discharged by
`planar_exit_ae_lt_top`. The killed-occupation formula `hS0` (`KilledBrownianOccupationOnBall`) is still a binder. -/
theorem frozenLBMGreenOccupationRescaled_closed2 (𝒮 : SpaceFillingSLEModel)
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
    (hS0 : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (z : ℂ) (r : ℝ), 0 < r → ball z r ⊆ ball 0 ρ →
      KilledBrownianOccupationOnBall z r)
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
    exact baseOccupationIdentity_of_GMC' S.P γ S.hcirc z r hy
      (hball.trans (Metric.ball_subset_ball hρ1.le))
      (hS0 ρ hρ0 hρ1 z r hr hball)
      (hw γ hγ0 hγ2 Ω S hS)
      (hVar γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
      (ν γ Ω S) (dA γ Ω S)
      (hνmeas γ hγ0 hγ2 Ω S hS)
      (hconvB1 γ hγ0 hγ2 Ω S hS)
      (hLjoint γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
      (hMeas γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
      (hLpath γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS r z y hr hball hy)
  exact frozenLBMGreenOccupationRescaled_of_appendixB 𝒮 ν dA hm0 hBase hWeight hMeas hS6 hBG
    (fun _ z r _ _ => greenDiskFormula z r) hExit

end MatedCRT.KilledOccupation
