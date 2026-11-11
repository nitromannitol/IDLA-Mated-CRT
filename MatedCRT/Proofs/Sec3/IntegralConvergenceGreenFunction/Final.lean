import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ContinuumTailAssembly
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ContinuumIdentification

/-!
# Lemma 3.4: assembly from its steps

`integralConvergenceGreenFunction_of_steps` derives `IntegralConvergenceGreenFunctionStmt` from the
Revuz identity `LBMGreenOccupationStep` (open) and four named steps:

* `TruncatedOccupationFixedTimeStep`: fixed-time convergence of the truncated occupation sums;
* `LBMExitTimeIntegrableStep`: the LBM exit time from a ball is integrable for almost every environment;
* `LBMTruncatedOccupationMeasurableStep`: measurability of the truncated path integrals;
* `LBMGreenIntegralMeasurableStep`: measurability in the environment of the Green integral.

The discrete tail bounds (Lemma 2.18 with N = 2 and `MepsScalingInput`) and the almost-sure limit
of the truncated continuum occupations are proved in this directory and used here.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- **Fixed-time convergence** of the truncated occupation sums: the hypothesis `hfixed` of
`integralConvergenceGreenFunction_of_fixed_and_ae_continuum`. OPEN. Source: Theorem 2.11 applied to
the environment-dependent functional `φ^{f(ω)}_T`. The Draft encoding of Theorem 2.11
(`RandomWalkToLBMStmt`) covers only deterministic functionals (the encoding question is open). The discrete
Riemann sum must also be compared with the interpolated occupation at the window of the discrete exit
(this comparison is open). -/
def TruncatedOccupationFixedTimeStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ f : Ω → ℂ → ℝ, (∀ x, Measurable[S.envSigma] fun ω => f ω x) →
    (∀ ω, ∃ M : ℝ, ∀ x ∈ ball z r, |f ω x| ≤ M) → (∀ ω, IsHolderContinuousOn (f ω) (ball z r)) →
  ∀ T : ℝ, 0 < T → TendstoInProbability S.P
    (fun ε ω => truncatedDiscreteOccupation S (ball z r) y f ⌊T * S.mε ε⌋₊ ε ω)
    (truncatedLBMOccupation S (ball z r) y f T)

/-- **Integrability of the LBM exit time** from a ball, for almost every environment, in the Brownian
variable: the hypothesis `hexit` of `truncatedLBMOccupation_tendsto_of_integrable_exit`. OPEN. Source
route: Lemma 2.18 with N = 2 and `MepsScalingInput`; Theorem 2.11 for `min(T, τ)`, which is continuous at
regular exits (this needs `BrownianOutwardExcursionAtExitStep`); monotone convergence in `T`. -/
def LBMExitTimeIntegrableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ᵐ ω ∂S.P, Integrable (fun b =>
    (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal) (planarBrownianMotion y)

/-- **Measurability of the truncated LBM occupations**: for almost every environment the truncated path
integrals are strongly measurable in the Brownian variable, and the truncated occupations are
measurable in the environment (the hypotheses `hmeas`, `hVm` of the assembly). OPEN: the extension of
`LBMPathFunctionalMeasurableStep` from bounded Lipschitz functionals to the environment-dependent
functionals `φ^{f(ω)}`. -/
def LBMTruncatedOccupationMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ f : Ω → ℂ → ℝ, (∀ x, Measurable[S.envSigma] fun ω => f ω x) →
    (∀ ω, ∃ M : ℝ, ∀ x ∈ ball z r, |f ω x| ≤ M) → (∀ ω, IsHolderContinuousOn (f ω) (ball z r)) →
  (∀ᵐ ω ∂S.P, ∀ n : ℕ, AEStronglyMeasurable (fun b => ∫ t in Ioc (0 : ℝ)
      (min (n : ℝ) (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
        f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) (planarBrownianMotion y)) ∧
  ∀ n : ℕ, AEMeasurable (truncatedLBMOccupation S (ball z r) y f n) S.P

/-- **Measurability of the Green integral** in the environment: the hypothesis `hUm` of
`integralConvergenceGreenFunction_of_fixed_and_ae_continuum`. PROVED: `lbmGreenIntegralMeasurableStep_holds`
(`GreenIntegralMeasurable.lean`), by Carathéodory joint measurability of `(ω, x) ↦ f ω x` on the ball and a
finite normalized kernel built from `μ_h`; the step is kept here as the statement used by the assemblies. -/
def LBMGreenIntegralMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ f : Ω → ℂ → ℝ, (∀ x, Measurable[S.envSigma] fun ω => f ω x) →
    (∀ ω, ∃ M : ℝ, ∀ x ∈ ball z r, |f ω x| ≤ M) → (∀ ω, IsHolderContinuousOn (f ω) (ball z r)) →
  AEMeasurable (fun ω => S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂S.μ ω) S.P

/-- **Lemma 3.4** (lemma:integral-convergence-of-greens-function) from its steps: the rescaled Green
occupation sums converge in probability to `c₀ ∫ G f dμ_h`, given the Revuz identity and the named
steps. The truncation, tail and almost-sure limit arguments are those of the proved lemmas
`integralConvergenceGreenFunction_of_fixed_and_ae_continuum` and `truncatedLBMOccupation_tendsto_of_integrable_exit`. -/
theorem integralConvergenceGreenFunction_of_steps {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (hrevuz : LBMGreenOccupationStep 𝒮) (hfixedStep : TruncatedOccupationFixedTimeStep 𝒮)
    (hexitStep : LBMExitTimeIntegrableStep 𝒮) (hmeasStep : LBMTruncatedOccupationMeasurableStep 𝒮)
    (hUmStep : LBMGreenIntegralMeasurableStep 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hball hy f hfmeas hfbound hfcont
  have hfixed := hfixedStep γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy f hfmeas hfbound hfcont
  have hexit := hexitStep γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy
  obtain ⟨hmeas, hVm⟩ := hmeasStep γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy f hfmeas hfbound hfcont
  have hUm := hUmStep γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy f hfmeas hfbound hfcont
  have hid := MatedCRTEnv.IsValid.ae_integral_rescaled_occupation_eq hγ hγ2 hS hrevuz hρ hρ1 hr
    hball hy f hfbound hfcont
  have hV : ∀ᵐ ω ∂S.P, Tendsto (fun n : ℕ => truncatedLBMOccupation S (ball z r) y f n ω) atTop
      (𝓝 (S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂S.μ ω)) := by
    filter_upwards [hexit, hmeas, hid] with ω hωexit hωmeas hωid
    obtain ⟨M, hM⟩ := hfbound ω
    rw [← hωid]
    exact truncatedLBMOccupation_tendsto_of_integrable_exit S (ball z r) y f ω (max M 0)
      (le_max_right _ _) (fun x hx => (hM x hx).trans (le_max_left _ _)) hωmeas hωexit
  exact integralConvergenceGreenFunction_of_fixed_and_ae_continuum h17 h18 hscale hγ hγ2 hρ hρ1 S hS
    hr hball hy f hfmeas hfbound hfcont hfixed hVm hUm hV

end MatedCRT
