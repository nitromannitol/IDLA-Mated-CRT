import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosure
import MatedCRT.Proofs.Sec3.KilledOccupation.GreenDisk
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockBinders
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockProofCont

/-!
# Frozen killed-occupation input of the Green function, with the bounded continuous weights of the printed route

`frozenLBMGreenOccupationRescaled_closed3` is `frozenLBMGreenOccupationRescaled_closed2` (OccupationClosure2.lean:32)
with `hBase` supplied by `baseOccupationIdentity_of_GMC_cont` (BaseClockProofCont.lean), so that the conditional GMC
clock input `hLpath` is quantified only over bounded nonnegative continuous weights (appendix tex:166-177, Berestycki
2017 Thm 1.1 p. 3). The other binders have the names and types of closure2.

Discharged, as in closure2:
* `hGreen`, the Green disc formula `GreenDiskFormula z r` (Potential.lean:34), by `greenDiskFormula` (GreenDisk.lean);
* `hτ`, `hτmeas`, `hGint`, `hσint` (exit time and Green function of the disc, Appendix B textbook binders), by
  `integrable_pathExitTime_toReal_planar`, `measurable_pathExitTime_ball`, `measurable_greenFunction_ball_left`,
  `integrableOn_greenFunction_ball`, `lintegral_toNNReal_pathExitTime_planar_ne_top` (BaseClockBinders.lean);
* `hExit`, planar Brownian motion leaves the disc a.s., by `planar_exit_ae_lt_top` (ClockFinite.lean).

Still binders (the same as closure2): `hm0`, `hWeight`, `hMeas`, `hS6`, `hBG`, `hS0`, `hw`, `hVar`, `hνmeas`,
`hconvB1`, `hLjoint`, and `hLpath` (now in its continuous-weight form). `hw` is not derived: `IsQuantumCone` gives only
measurability in `ω` for fixed `(r, z)` and a.s. continuity in `(r, z)`, which does not give joint measurability of
`(ω, x) ↦ hcirc ω r x` on `Ω × ℂ` without a modification (the field is not assumed jointly measurable).
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric MarkovProcess ProbabilityTheory
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- The exit-time and Green-function binders of `baseOccupationIdentity_of_GMC_cont` discharged, for the disc
`ball z r` and a point `y ∈ ball z r`; the same as `baseOccupationIdentity_of_GMC'` (BaseClockBinders.lean:228) with
the bounded continuous weights of `hLpath`. -/
theorem baseOccupationIdentity_of_GMC_cont' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (r : ℝ) {y : ℂ} (hy : y ∈ ball z r)
    (hDB : ball z r ⊆ ball 0 1)
    (hS0 : KilledBrownianOccupationOnBall z r)
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ ball z r, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    (ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hνmeas : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν ω))
    (hconvB1 : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) →
      (∀ x ∉ ball 0 1, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0))
    (hLjoint : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun p : Ω × ContinuousPath ℂ => limitClockFun dA z r p.1 p.2 q)
    (hmeasKernel : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b : ContinuousPath ℂ => ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal,
        q (b u) ∂(dA ω b))
    (hLpath : ∀ q : ℂ → ℝ≥0∞, Continuous q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∀ᵐ b ∂planarBrownianMotion y, Tendsto (fun k => clockGapMean P γ hcirc dA z r k q b) atTop (𝓝 0)) :
    BaseOccupationIdentity P (planarBrownianMotion y) (ball z r) (greenFunction (ball z r) y) ν dA
      (fun b => (pathExitTime (ball z r) b).toNNReal) :=
  baseOccupationIdentity_of_GMC_cont P γ hcirc z r hy hDB hS0
    (integrable_pathExitTime_toReal_planar y z r) (measurable_pathExitTime_ball z r)
    (measurable_greenFunction_ball_left z y r) (integrableOn_greenFunction_ball z y r hy)
    hw hVar ν dA hνmeas hconvB1 hLjoint hmeasKernel hLpath
    (lintegral_toNNReal_pathExitTime_planar_ne_top y z r)

/-- **Frozen killed-occupation input of the Green function** (`FrozenLBMGreenOccupationRescaled`), with the Green disc
formula, the exit-time and Green-function binders, and `hExit` discharged; the conditional GMC clock input `hLpath` is
quantified over bounded nonnegative continuous weights only (closure2 has `Measurable` weights). The killed-occupation
formula `hS0` and the field binders (`hw`, `hVar`, `hνmeas`, `hconvB1`, `hLjoint`, `hMeas`, `hS6`, `hBG`, `hWeight`,
`hm0`) remain binders. -/
theorem frozenLBMGreenOccupationRescaled_closed3 (𝒮 : SpaceFillingSLEModel)
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
      ∀ q : ℂ → ℝ≥0∞, Continuous q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
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
    exact baseOccupationIdentity_of_GMC_cont' S.P γ S.hcirc z r hy
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
