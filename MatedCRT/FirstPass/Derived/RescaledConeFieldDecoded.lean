import MatedCRT.FirstPass.Derived.CircleSmearL1
import MatedCRT.FirstPass.Derived.RescaledPairingFieldSigma
import MatedCRT.FirstPass.Derived.RescaledConeFieldSmear
import MatedCRT.FirstPass.Derived.EnvScalingClock
import LatticeProb.Prob.ModificationJointLaw

/-!
# The rescaled cone field: circle smear decoder versus the rescaled pairings

For a valid environment `S` (circle average embedding of a `γ`-quantum cone together with its mating-of-trees
coupling) and `b > 0`, let `R_b` be the cone scale radius and `h^b = h(R_b ·) + Q log R_b - γ⁻¹ log b` the rescaled
field. This file proves, for one test function `φ` at a time:

* `ae_circleSmearLimit_eq_hC`: almost surely the circle smear limit `Λ_φ` of the circle averages of `h` equals `(h, φ)`;
* `ae_circleSmearLimit_rescaled_eq`: almost surely `Λ_φ` of the circle averages of `h^b` equals `(h^b, φ)`;
* `ae_lateralProcess_circleSmearLimit_eq`: the lateral part of the field decoded by `Λ` from the circle averages of
  `h^b` agrees almost surely, at each admissible observable, with the lateral part of any field whose pairings are
  almost surely those of `h^b`.

With these, `rescaledConeFieldStep_of_scaling` proves step F of the environment scaling (`RescaledConeFieldStep`):
the field `hC'` of `MatedCRTEnv.IsValid.exists_rescaledPairing_fieldSigma_le` (pairings of `h^b`, measurable, a
function of `h`) has lateral part independent of the radial part of `c` and with the law of the lateral part of a
whole-plane GFF. The decoded field `φ ↦ Λ_φ(c)` is a `γ`-quantum cone (`isQuantumCone_decoded`, from the scaling
invariance of the cone), and the lateral part of `hC'` is a modification of its lateral part, so the joint law with the
radial part and the law transfer (`ProbabilityTheory.map_prod_eq_of_forall_ae_eq`). Then
`coneEnvironmentScalingUnderSLE_of_mating` removes the binder `hfield` of `coneEnvironmentScalingUnderSLE_of_field_mating`.

The random radius `R_b` is handled by the smeared circle averages at all dilation scales at once
(`MatedCRTEnv.IsValid.exists_ae_tendsto_integral_smul_mul_circle`).
-/

open MeasureTheory Filter Set Topology HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-- **The circle smear limit decodes the pairings.** For a valid environment and a test function `φ`, almost surely
`Λ_φ(h_·(·)) = (h, φ)`. -/
theorem ae_circleSmearLimit_eq_hC {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hv : S.IsValid 𝒮 γ) {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    (fun ω => circleSmearLimit φ (circleProcess (S.hcirc ω))) =ᵐ[S.P] fun ω => S.hC ω φ := by
  obtain ⟨H, hH, hL⟩ := MatedCRTEnv.IsValid.exists_ae_tendsto_integral_smul_mul_circle hv
  let ψ : LQGMetric.TestC := ⟨φ, hφ.1, hφ.2.1, by simp⟩
  filter_upwards [hL ψ, hH, hv.isQuantumCone.ae_continuousOn_circle] with ω hω hHω hcω
  have hψ1 : ⇑(LQGMetric.testAffinePull (1 : ℝ)⁻¹ 0 ψ) = φ := by
    funext x
    rw [LQGMetric.testAffinePull_inv_zero_apply ψ one_ne_zero, one_smul]
    rfl
  have h1 := hω 1 one_pos
  rw [← hHω, hψ1] at h1
  simp only [one_smul] at h1
  exact circleSmearLimit_circleProcess_eq_of_tendsto hφ.1.continuous hφ.2.1 hcω h1

/-- **The circle smear limit decodes the rescaled pairings.** For a valid environment, `b > 0`, a version `c` of the
circle averages of `h^b` and a test function `φ`, almost surely `Λ_φ(c) = (h^b, φ)`. -/
theorem ae_circleSmearLimit_rescaled_eq {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hv : S.IsValid 𝒮 γ) (b : ℝ) {c : Ω → ℝ → ℂ → ℝ}
    (hc : ∀ᵐ ω ∂S.P, c ω = rescaledCircle γ (S.hcirc ω) (coneScaleRadius γ (S.hcirc ω) b) b)
    {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    ∀ᵐ ω ∂S.P, circleSmearLimit φ (circleProcess (c ω)) =
      rescaledPairing γ (S.hC ω) (coneScaleRadius γ (S.hcirc ω) b) b φ := by
  obtain ⟨H, hH, hL⟩ := MatedCRTEnv.IsValid.exists_ae_tendsto_integral_smul_mul_circle hv
  obtain ⟨R, -, hRpos, hRae⟩ := exists_fieldSigma_measurable_coneScaleRadius hγ0 hγ2 S hv b
  let ψ : LQGMetric.TestC := ⟨φ, hφ.1, hφ.2.1, by simp⟩
  filter_upwards [hL ψ, hH, hv.isQuantumCone.ae_continuousOn_circle, hc, hRae]
    with ω hω hHω hcω hcω' hRω
  set r := coneScaleRadius γ (S.hcirc ω) b with hr
  have hrpos : 0 < r := by rw [← hRω]; exact hRpos ω
  have hfun : ⇑(LQGMetric.testAffinePull r⁻¹⁻¹ 0 ψ) = fun x => φ ((r⁻¹ : ℂ) * x) := by
    funext x
    rw [LQGMetric.testAffinePull_inv_zero_apply ψ (inv_ne_zero hrpos.ne'), Complex.real_smul,
      Complex.ofReal_inv]
    rfl
  have h1 := hω r⁻¹ (inv_pos.mpr hrpos)
  rw [← hHω, hfun] at h1
  simp only [Complex.real_smul, Complex.ofReal_inv] at h1
  have h2 := tendsto_integral_mul_rescaledCircle (γ := γ) (b := b) hrpos hφ.1.continuous hφ.2.1 hcω h1
  rw [hcω']
  exact circleSmearLimit_circleProcess_eq_of_tendsto hφ.1.continuous hφ.2.1
    (MatedCRT.LQGMeasure.continuousOn_rescaledCircle γ b _ hrpos hcω) h2

/-- **The decoded lateral part is a modification.** For a valid environment, `b > 0`, a version `c` of the circle
averages of `h^b` and a field `hC'` whose pairings are almost surely those of `h^b`, the lateral part of the field
`φ ↦ Λ_φ(c)` decoded from `c` agrees almost surely with the lateral part of `hC'` at each admissible observable. -/
theorem ae_lateralProcess_circleSmearLimit_eq {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hv : S.IsValid 𝒮 γ) (b : ℝ) {c : Ω → ℝ → ℂ → ℝ}
    (hc : ∀ᵐ ω ∂S.P, c ω = rescaledCircle γ (S.hcirc ω) (coneScaleRadius γ (S.hcirc ω) b) b)
    {hC' : Ω → (ℂ → ℝ) → ℝ}
    (h1 : ∀ᵐ ω ∂S.P, ∀ φ, IsTestFunction univ φ →
      hC' ω φ = rescaledPairing γ (S.hC ω) (coneScaleRadius γ (S.hcirc ω) b) b φ)
    (o : GFFObservable.Admissible) :
    (fun ω => lateralProcess (fun φ => circleSmearLimit φ (circleProcess (c ω))) (c ω) o) =ᵐ[S.P]
      fun ω => lateralProcess (hC' ω) (c ω) o := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ =>
    filter_upwards [ae_circleSmearLimit_rescaled_eq hγ0 hγ2 hv b hc ho, h1] with ω hω h1ω
    simp only [lateralProcess, lateralEval, hω, h1ω φ ho]
  | circle r z => exact Filter.EventuallyEq.rfl

/-- **The rescaled cone field (step F of the environment scaling).** Given the scaling invariance of the
`γ`-quantum cone, every valid environment satisfies `RescaledConeFieldStep`: for `b > 0` and a measurable version `c`
of the circle averages of `h^b` there is a field `hC'` whose pairings are almost surely those of `h^b`, each pairing
measurable, with lateral part independent of the radial part of `c` and with the law of the lateral part of a
whole-plane GFF, and generating a σ-algebra contained in that of `h`. -/
theorem rescaledConeFieldStep_of_scaling (hscale : QuantumConeScalingInput) (𝒮 : SpaceFillingSLEModel) :
    RescaledConeFieldStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hv b hb c hcm hc
  have hQ := hv.isQuantumCone
  have : IsProbabilityMeasure S.P := MatedCRT.LQGMeasure.IsQuantumCone.isProbabilityMeasure hQ
  obtain ⟨hC', h1, h2, h5⟩ := MatedCRTEnv.IsValid.exists_rescaledPairing_fieldSigma_le hγ hγ2 hv b
  have hdec := isQuantumCone_decoded hscale hγ hγ2 hQ hb hcm hc (fun φ => circleSmearLimit φ)
    (fun φ hφ => ⟨measurable_circleSmearLimit φ, ae_circleSmearLimit_eq_hC hv hφ⟩)
  have hmod := ae_lateralProcess_circleSmearLimit_eq hγ hγ2 hv b hc h1
  have hX := MatedCRT.Sec1.aemeasurable_lateralProcess_of_isQuantumCone hdec
  have hY : AEMeasurable (fun ω => lateralProcess (hC' ω) (c ω)) S.P :=
    CirclePairing.aemeasurable_lateralProcess h2 hcm hdec.ae_continuousOn_circle
  have hZ : AEMeasurable (fun ω => radialProcess (c ω)) S.P :=
    (MatedCRT.Sec1.IsQuantumCone.measurable_radialProcess hdec).aemeasurable
  refine ⟨hC', h1, h2, ?_, ?_, h5 _ c⟩
  · exact ProbabilityTheory.IndepFun.of_forall_ae_eq
      (X := fun o ω => lateralProcess (fun φ => circleSmearLimit φ (circleProcess (c ω))) (c ω) o)
      (Y := fun o ω => lateralProcess (hC' ω) (c ω) o) hZ hX hY hmod hdec.indep
  · obtain ⟨Ω', i', P', hC'', hcirc'', hP', hW, hL⟩ := hdec.lateral_law
    exact ⟨Ω', i', P', hC'', hcirc'', hP', hW,
      (ProbabilityTheory.map_eq_of_forall_ae_eq (X := fun o ω => lateralProcess (hC' ω) (c ω) o)
        (Y := fun o ω => lateralProcess (fun φ => circleSmearLimit φ (circleProcess (c ω))) (c ω) o)
        hY hX fun o => (hmod o).symm).trans hL⟩

/-- **The cone environment scaling without the field step.** `coneEnvironmentScalingUnderSLE_of_field_mating` with
the binder `hfield` supplied by `rescaledConeFieldStep_of_scaling`. -/
theorem coneEnvironmentScalingUnderSLE_of_mating (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (hmating : RescaledMatingOfTreesStep 𝒮) : ConeEnvironmentScalingUnderSLE 𝒮 :=
  coneEnvironmentScalingUnderSLE_of_field_mating 𝒮 hscale h22 (rescaledConeFieldStep_of_scaling hscale 𝒮) hmating

end MatedCRT.FirstPass.Derived
