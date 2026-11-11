import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosure
import MatedCRT.Proofs.Sec3.KilledOccupation.GreenDisk

/-!
# Frozen killed-occupation input of the Green function, with the Green disc formula discharged

`frozenLBMGreenOccupationRescaled_closed2` is `frozenLBMGreenOccupationRescaled_closed` (OccupationClosure.lean:35)
with the binder `hGreen` discharged: the Green disc formula `GreenDiskFormula z r` (Potential.lean:34) is supplied by
`greenDiskFormula` (GreenDisk.lean), the Green function of the disc `B_r(z)` in the explicit form of Armitage-Gardiner,
Section 4.1. The other binders are those of `frozenLBMGreenOccupationRescaled_closed`, with the same names and types.
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric MarkovProcess ProbabilityTheory
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- **Frozen killed-occupation input of the Green function** (`FrozenLBMGreenOccupationRescaled`), with the
Appendix B binders `hExit` and `hBase` discharged (as in `frozenLBMGreenOccupationRescaled_closed`) and the Green disc
formula `hGreen` discharged by `greenDiskFormula`. -/
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
    FrozenLBMGreenOccupationRescaled 𝒮 :=
  frozenLBMGreenOccupationRescaled_closed 𝒮 ν dA hm0 hWeight hMeas hS6 hBG
    (fun _ z r _ _ => greenDiskFormula z r) hS0 hτ hτmeas hGint hσint hw hVar hνmeas hconvB1 hLjoint hLpath

end MatedCRT.KilledOccupation
