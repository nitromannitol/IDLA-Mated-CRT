import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosure4
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit

/-!
# Frozen killed-occupation input of the Green function, with the positivity of `m₀` discharged

`frozenLBMGreenOccupationRescaled_closed5` is `frozenLBMGreenOccupationRescaled_closed4` (OccupationClosure4.lean:76)
with its hypothesis `hm0` removed. `hm0` is the positivity `0 < S.m₀` of the mated-CRT constant, discharged here by
`MatedCRTEnv.IsValid.m₀_pos` (HarmonicPathExit.lean:114, arguments `hγ hγ2 hS`). Every other binder is the same, in the same order,
and the conclusion is `FrozenLBMGreenOccupationRescaled 𝒮`, unchanged.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- `frozenLBMGreenOccupationRescaled_closed4` with its hypothesis `hm0` discharged by `MatedCRTEnv.IsValid.m₀_pos` (MATH-ANSWERS MQ-li-11: hm0 TRUE). -/
theorem frozenLBMGreenOccupationRescaled_closed5 (𝒮 : SpaceFillingSLEModel)
    (ν : (γ : ℝ) → (Ω : Type) → [MeasurableSpace Ω] → MatedCRTEnv Ω → Ω → Measure ℂ)
    (dA : (γ : ℝ) → (Ω : Type) → [MeasurableSpace Ω] → MatedCRTEnv Ω → Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hWeight : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → OccWeightIdentity S.P S.μ (ν γ Ω S) γ)
    (hMeas : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ᵐ ω ∂S.P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
        Measurable fun b => ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u) ∂(dA γ Ω S ω b))
    (hlaw : ConeUnitDiskGFFLaw)
    (hE : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
        Tendsto (fun ε => (S.P.prod (planarBrownianMotion y))
          {x | ENNReal.ofReal η < clockDistE γ (fun ω => coneShift γ (S.hcirc ω)) (dA γ Ω S) (exitNN z r) ε a x})
          (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hKern : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∃ K : Kernel (Ω × ContinuousPath ℂ) ℝ≥0, IsSFiniteKernel K ∧
        ∀ x, K x = dA γ Ω S x.1 x.2)
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
    FrozenLBMGreenOccupationRescaled 𝒮 :=
  frozenLBMGreenOccupationRescaled_closed4 𝒮 ν dA
    (fun _γ h0 h2 _Ω _ _S hS => hS.m₀_pos h0 h2)
    hWeight hMeas hlaw hE hKern hBG hS0 hw hVar hνmeas hconvB1 hLjoint hLpath

end MatedCRT.KilledOccupation
