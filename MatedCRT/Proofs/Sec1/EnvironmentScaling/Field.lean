import MatedCRT.Proofs.Sec1.EnvironmentScaling.DistributionCode

/-!
# Rescaled field pairings

The coding and simultaneous representation from env-steps.tex:176–207 give
an exactly field-measurable distribution.  Lines 309–314 require joint
measurability of its evaluation at a dilated test; that analytic ingredient
is isolated below.  This file does not assert cone law or independence.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Distributions
open HarmonicBalls

namespace MatedCRT.Sec1

/-- Joint measurability of evaluation at a variable dilation, on the imported
plane distribution and test-function carriers (env-steps.tex:309–314). -/
def VariableDilationPairingStep : Prop :=
  ∀ φ : LQGMetric.TestC,
    Measurable fun p : LQGMetric.DistC × ℝ => p.1 (LQGMetric.testAffinePull p.2 0 φ)

/-- Pair a distribution at a variable scale, with zero on non-tests. -/
def rescaledDistributionPairing (γ b : ℝ) (H : LQGMetric.DistC) (r : ℝ)
    (φ : ℂ → ℝ) : ℝ := by
  classical
  exact if hφ : IsTestFunction univ φ then
    (r⁻¹) ^ 2 * H (LQGMetric.testAffinePull r 0 ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩) +
      (lqgQ γ * Real.log r - γ⁻¹ * Real.log b) * ∫ x, φ x
    else 0

/-- The explicit distribution version produces all required pairing and
field-sigma conclusions, given the joint dilation measurability boundary and
an exactly field-measurable version of the positive scale radius. -/
theorem exists_rescaled_pairing_of_variableDilation
    (hscale : VariableDilationPairingStep)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (R : Ω → ℝ) (hRm : Measurable[S.fieldSigma] R)
    (hR : ∀ᵐ ω ∂S.P, R ω = coneScaleRadius γ (S.hcirc ω) b ∧ R ω ≠ 0) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ,
      (∀ᵐ ω ∂S.P, ∀ φ, IsTestFunction univ φ →
        hC' ω φ = rescaledPairing γ (S.hC ω)
          (coneScaleRadius γ (S.hcirc ω) b) b φ) ∧
      (∀ φ, IsTestFunction univ φ → Measurable[S.fieldSigma] fun ω => hC' ω φ) ∧
      (∀ φ, IsTestFunction univ φ → Measurable fun ω => hC' ω φ) ∧
      ∀ c, (S.rescaleWithCircle γ b hC' (fun _ _ _ => 0) c).fieldSigma ≤ S.fieldSigma := by
  obtain ⟨H, hHm, hH⟩ := exists_fieldMeasurable_coneDistribution hS
  let hC' : Ω → (ℂ → ℝ) → ℝ := fun ω => rescaledDistributionPairing γ b (H ω) (R ω)
  have hfield : ∀ φ, IsTestFunction univ φ → Measurable[S.fieldSigma] fun ω => hC' ω φ := by
    intro φ hφ
    let ψ : LQGMetric.TestC := ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
    have heval : Measurable[S.fieldSigma] fun ω => H ω (LQGMetric.testAffinePull (R ω) 0 ψ) := by
      let m := S.fieldSigma
      let : MeasurableSpace Ω := m
      exact (hscale ψ).comp (hHm.prodMk hRm)
    change Measurable[S.fieldSigma] fun ω => rescaledDistributionPairing γ b (H ω) (R ω) φ
    simp only [rescaledDistributionPairing, dite_eq_left hφ]
    let m := S.fieldSigma
    let : MeasurableSpace Ω := m
    exact ((hRm.inv.pow_const 2).mul heval).add
      (((measurable_const.mul hRm.log).sub measurable_const).mul measurable_const)
  have hle : S.fieldSigma ≤ (inferInstance : MeasurableSpace Ω) := by
    simp only [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra]
    refine iSup₂_le fun φ hφ => ?_
    have hm : Measurable fun ω => fieldPairing 0 (S.hC ω) φ := by
      simpa [fieldPairing] using hS.isQuantumCone.measurable_pairing φ hφ
    exact hm.comap_le
  refine ⟨hC', ?_, hfield, (fun φ hφ => (hfield φ hφ).mono hle le_rfl), ?_⟩
  · filter_upwards [hH, hR] with ω hω hRω
    intro φ hφ
    let ψ : LQGMetric.TestC := ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
    have hpull : (fun x => φ (((R ω)⁻¹ : ℂ) * x)) =
        ⇑(LQGMetric.testAffinePull (R ω) 0 ψ) := by
      funext x
      rw [LQGMetric.testAffinePull_apply _ _ hRω.2]
      simp [ψ, div_eq_mul_inv, mul_comm]
    change rescaledDistributionPairing γ b (H ω) (R ω) φ = _
    simp only [rescaledDistributionPairing, dite_eq_left hφ, rescaledPairing]
    rw [← hRω.1, hpull, hω (LQGMetric.testAffinePull (R ω) 0 ψ)]
  · intro c
    simp only [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra]
    refine iSup₂_le fun φ hφ => ?_
    have hm : Measurable[S.fieldSigma] fun ω => fieldPairing 0 (hC' ω) φ := by
      simpa [fieldPairing] using hfield φ hφ
    exact hm.comap_le

/-- Specialization to the existing field-measurable cone scale radius. -/
theorem exists_rescaled_pairing
    (hdilation : VariableDilationPairingStep) (hscale : QuantumConeScalingInput)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hS : S.IsValid 𝒮 γ) (hb : 0 < b) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ,
      (∀ᵐ ω ∂S.P, ∀ φ, IsTestFunction univ φ →
        hC' ω φ = rescaledPairing γ (S.hC ω)
          (coneScaleRadius γ (S.hcirc ω) b) b φ) ∧
      (∀ φ, IsTestFunction univ φ → Measurable[S.fieldSigma] fun ω => hC' ω φ) ∧
      (∀ φ, IsTestFunction univ φ → Measurable fun ω => hC' ω φ) ∧
      ∀ c, (S.rescaleWithCircle γ b hC' (fun _ _ _ => 0) c).fieldSigma ≤ S.fieldSigma := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨R, hRm, hR⟩ := exists_fieldMeasurable_coneScaleRadius hscale hγ hγ2 hS hb
  have hpos := ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone hb
  apply exists_rescaled_pairing_of_variableDilation hdilation hS R hRm
  filter_upwards [hR, hpos] with ω hRω hposω
  exact ⟨hRω, hRω ▸ hposω.ne'⟩

end MatedCRT.Sec1

