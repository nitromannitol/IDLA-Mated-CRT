import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtDerived
import MatedCRT.FirstPass.Derived.IdentificationTransfer

/-!
# Theorem 2.11 (Berestycki-Gwynne Theorem 1.2) from the convergence on reference environments

`RandomWalkToLBMStmt 𝒮` is derived by composing

* `randomWalkToLBMStmt_of_identification` (the scaling theorems of Berestycki-Gwynne Section 6, the sequential
  Prokhorov theorem and the comparison of bounded Lipschitz path functionals in the Lévy-Prokhorov distance, given
  the identification of subsequential limits), with
* `identification_of_reference_convergence` (the identification of every subsequential weak limit of the pairs
  (data, interpolated quenched walk law), transferred from a reference environment to every valid environment with
  the same normalized space-filling SLE law).

The binders `hEnvS`, `hN4`, `hν`, `href` and `hU` are those of `randomWalkToLBMStmt_of_identification`. The data of
the field are `R h` for a measurable map `R` from distributions to a Polish space `X`, and the Liouville Brownian law
field is `Φ γ (R h)` for measurable maps `Φ γ`. The remaining named inputs are two hypotheses (no new Prop):

* `hLBM` (Berestycki-Gwynne Section 7.3, "`P^LBM` is a.s. determined by `h`"): in every valid environment,
  `Φ γ (R H)` for a measurable version `H` of the field almost surely integrates every bounded Lipschitz path
  functional as the law of the rescaled Liouville Brownian motion started from each `z`;
* `hP1` (Berestycki-Gwynne Theorem 1.2 on the reference environments): in every valid environment on `ℝ`, with
  measurable versions `H₀, η₀` of its field and space-filling SLE curve, the pairs `(R H₀, P̃^ε)` converge in law to
  `(R H₀, Φ γ (R H₀))` as `ε → 0⁺`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MarkovProcess (ContinuousPath)
open _root_.HarmonicBalls

/-- **Theorem 2.11 from the convergence on reference environments.** Given the scaling inputs of
`randomWalkToLBMStmt_of_identification`, measurable Polish data `R` of the field and measurable law fields `Φ γ`
such that `Φ γ (R h)` is a.s. the law field of the rescaled Liouville Brownian motion (`hLBM`, Berestycki-Gwynne
Section 7.3) and the pairs `(R h, P̃^ε)` converge in law to `(R h, Φ γ (R h))` on the reference environments
(`hP1`, Berestycki-Gwynne Theorem 1.2), the embedded random walk on the mated-CRT map converges to Liouville Brownian
motion in every valid environment. -/
theorem randomWalkToLBMStmt_of_reference_convergence {𝒮 : SpaceFillingSLEModel}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [PolishSpace X] [BorelSpace X]
    (R : LQGMetric.DistC → X) (hR : Measurable R)
    (Φ : ℝ → X → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) (hΦ : ∀ γ, Measurable (Φ γ))
    (hLBM : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
        ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
          ∫ q, blPathFunctionalBCF hF q ∂(Φ γ (R (H ω)) z : Measure (ContinuousPath ℂ)))
    (hP1 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ → (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) →
      ∀ η₀ : ℝ → C(ℝ, ℂ), Measurable η₀ → (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) →
      ∀ f : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) →ᵇ ℝ,
        Tendsto (fun ε => ∫ ω, f (R (H₀ ω), interpWalkLaw S₀ η₀ ε ω) ∂S₀.P) (𝓝[>] 0)
          (𝓝 (∫ ω, f (R (H₀ ω), Φ γ (R (H₀ ω))) ∂S₀.P))) :
    RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_identification hEnvS hN4 hν href hU
    (identification_of_reference_convergence hν href hU R hR Φ hΦ hLBM hP1)

end MatedCRT.FirstPass.Derived
