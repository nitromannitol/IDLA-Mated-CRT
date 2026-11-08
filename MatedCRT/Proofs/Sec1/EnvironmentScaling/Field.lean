import MatedCRT.Proofs.Sec1.EnvironmentScaling.DistributionCode

/-!
# Rescaled field pairings

The coding and simultaneous representation from env-steps.tex:176–207 give
an exactly field-measurable distribution.  Lines 309–314 require joint
measurability of its evaluation at a dilated test; this is proved below.  This file does not assert cone law or independence.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Distributions Topology
open HarmonicBalls

namespace MatedCRT.Sec1

/-- Joint measurability of evaluation at a variable dilation, on the imported
plane distribution and test-function carriers (env-steps.tex:309–314). -/
def VariableDilationPairingStep : Prop :=
  ∀ φ : LQGMetric.TestC,
    Measurable fun p : LQGMetric.DistC × ℝ => p.1 (LQGMetric.testAffinePull p.2 0 φ)

/-- The remaining topology step can be reduced to continuity of the
nonzero dilation orbit of each fixed test function. -/
def ContinuousDilationTestStep : Prop :=
  ∀ φ : LQGMetric.TestC,
    Continuous fun r : {r : ℝ // r ≠ 0} => LQGMetric.testAffinePull r 0 φ

/-- Dilation of a test function varies continuously at each nonzero scale. -/
theorem continuousAt_testAffinePull (φ : LQGMetric.TestC) {r₀ : ℝ} (hr₀ : r₀ ≠ 0) :
    ContinuousAt (fun r : ℝ => LQGMetric.testAffinePull r 0 φ) r₀ := by
  let δ : ℝ := |r₀| / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let S : Set ℝ := Metric.closedBall r₀ δ
  have hSn : S ∈ 𝓝 r₀ := Metric.closedBall_mem_nhds _ hδ
  have hS0 : ∀ r : S, (r : ℝ) ≠ 0 := by
    intro r hr
    have hbound : dist (r : ℝ) r₀ ≤ δ := Metric.mem_closedBall.mp r.2
    rw [hr, Real.dist_eq, zero_sub, abs_neg] at hbound
    dsimp [δ] at hbound
    have : 0 < |r₀| := abs_pos.mpr hr₀
    linarith
  let K : TopologicalSpace.Compacts ℂ :=
    ⟨(fun p : ℝ × ℂ => p.1 • p.2) '' (S ×ˢ tsupport φ),
      ((isCompact_closedBall _ _).prod φ.hasCompactSupport.isCompact).image (by fun_prop)⟩
  let Ψ : S → ℂ → ℝ := fun r y => φ ((r : ℝ)⁻¹ • y)
  have hs : ∀ r : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ r) := by
    intro r
    exact φ.contDiff.comp (by fun_prop)
  have hK : ∀ r : S, ∀ y ∉ (K : Set ℂ), Ψ r y = 0 := by
    intro r y hy
    change φ ((r : ℝ)⁻¹ • y) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    apply hy
    change y ∈ (fun p : ℝ × ℂ => p.1 • p.2) '' (S ×ˢ tsupport φ)
    refine ⟨⟨r, (r : ℝ)⁻¹ • y⟩, ⟨r.2, ht⟩, ?_⟩
    simp [hS0 r]
  have hD : ∀ i : ℕ, Continuous fun p : S × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
    intro i
    have hr : Continuous fun p : S × ℂ => (p.1 : ℝ)⁻¹ :=
      (continuous_subtype_val.comp continuous_fst).inv₀ fun p => hS0 p.1
    change Continuous fun p : S × ℂ =>
      iteratedFDeriv ℝ i (fun y => φ ((p.1 : ℝ)⁻¹ • y)) p.2
    simp_rw [iteratedFDeriv_comp_const_smul _ (φ.contDiff.of_le (by exact_mod_cast le_top))]
    exact (hr.pow i).smul
      ((φ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
        (hr.smul continuous_snd))
  have hc := LQGMetric.continuous_testFamK K Ψ hs hK hD
  let I : 𝓓^{⊤}_{K}(ℂ, ℝ) →L[ℝ] LQGMetric.TestC :=
    TestFunction.ofSupportedInCLM ℝ (subset_univ _)
  have heq : (fun r : S => LQGMetric.testAffinePull (r : ℝ) 0 φ) =
      I ∘ LQGMetric.testFamK K Ψ hs hK := by
    funext r
    ext y
    rw [LQGMetric.testAffinePull_apply _ _ (hS0 r)]
    simp [I, LQGMetric.testFamK, Ψ, Complex.real_smul, div_eq_inv_mul]
    rfl
  have hlocal : ContinuousOn (fun r : ℝ => LQGMetric.testAffinePull r 0 φ) S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun r : S => LQGMetric.testAffinePull (r : ℝ) 0 φ)
    rw [heq]
    exact I.continuous.comp hc
  exact (hlocal r₀ (Metric.mem_closedBall_self hδ.le)).continuousAt hSn

/-- Dilation is continuous on the nonzero scale parameter space. -/
theorem continuousDilationTestStep : ContinuousDilationTestStep := by
  intro φ
  rw [continuous_iff_continuousAt]
  intro r
  exact (continuousAt_testAffinePull φ r.property).comp continuous_subtype_val.continuousAt

/-- Joint measurability follows from continuity of the test orbit and the
cylinder measurability of fixed test pairings.  At zero the pullback is zero. -/
theorem variableDilationPairingStep_of_continuous
    (hcont : ContinuousDilationTestStep) : VariableDilationPairingStep := by
  classical
  intro φ
  let ρ : ℝ → {r : ℝ // r ≠ 0} := fun r =>
    if hr : r = 0 then ⟨1, one_ne_zero⟩ else ⟨r, hr⟩
  have hρ : Measurable ρ := by
    apply Measurable.subtype_mk
    have hm : Measurable fun r : ℝ => if r = 0 then (1 : ℝ) else r :=
      Measurable.ite (measurableSet_singleton 0) measurable_const measurable_id
    convert hm using 1
    funext r
    change (ρ r : ℝ) = (if r = 0 then 1 else r)
    by_cases hr : r = 0 <;> simp [ρ, hr]
  have hjoint : Measurable fun p : {r : ℝ // r ≠ 0} × LQGMetric.DistC =>
      p.2 (LQGMetric.testAffinePull p.1 0 φ) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun d => (map_continuous d).comp (hcont φ))
      (fun r => LQGMetric.measurable_distOn_apply _)
  have hm : Measurable fun p : LQGMetric.DistC × ℝ =>
      if p.2 = 0 then (0 : ℝ) else p.1 (LQGMetric.testAffinePull (ρ p.2) 0 φ) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
      (hjoint.comp ((hρ.comp measurable_snd).prodMk measurable_fst))
  convert hm using 1
  funext p
  by_cases hp : p.2 = 0
  · simp [hp, LQGMetric.testAffinePull]
  · simp [hp, ρ]

/-- Variable dilation pairings are jointly measurable. -/
theorem variableDilationPairingStep : VariableDilationPairingStep :=
  variableDilationPairingStep_of_continuous continuousDilationTestStep

/-- A version of the circle averages centered at zero, recovered from
field pairings on a countable dyadic set of positive radii. -/
def fieldRadialVersion {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) : Ω → ℝ → ℝ :=
  CirclePairing.radialVersion (fun ω r _ => FieldCircle.circleField S r 0 ω)

/-- The radial version is jointly measurable for the exact field sigma-algebra. -/
theorem measurable_fieldRadialVersion {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) :
    Measurable[S.fieldSigma.prod (borel ℝ)] (Function.uncurry (fieldRadialVersion S)) := by
  have hm : ∀ r : ℝ, Measurable[S.fieldSigma] (FieldCircle.circleField S r 0) :=
    fun r => FieldCircle.measurable_circleField S r 0
  let m := S.fieldSigma
  let : MeasurableSpace Ω := m
  exact CirclePairing.measurable_radialVersion (fun r _ _ => hm r)

/-- One event suffices for recovering all positive-radius centered circles,
using continuity in the radius (env-steps.tex:259–278). -/
theorem ae_fieldRadialVersion_eq {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ r : ℝ, 0 < r → fieldRadialVersion S ω r = S.hcirc ω r 0 := by
  have hdyad : ∀ᵐ ω ∂S.P, ∀ n : ℕ, ∀ k : ℤ, 0 < k →
      FieldCircle.circleField S ((k : ℝ) / 2 ^ n) 0 ω = S.hcirc ω ((k : ℝ) / 2 ^ n) 0 := by
    simp only [ae_all_iff]
    intro n k hk
    have hp : (0 : ℝ) < (k : ℝ) / 2 ^ n := div_pos (Int.cast_pos.mpr hk) (by positivity)
    exact FieldCircle.ae_circleField_eq hS hp (by simpa only [norm_zero] using hp.ne'.symm)
  filter_upwards [hdyad, hS.isQuantumCone.ae_continuousOn_circle] with ω hω hc
  intro r hr
  have heq : fieldRadialVersion S ω r = CirclePairing.radialVersion S.hcirc ω r := by
    unfold fieldRadialVersion CirclePairing.radialVersion
    congr 1
    funext n
    unfold CirclePairing.radialApprox CirclePairing.dyadicCeil
    by_cases hk : 0 < ⌈r * 2 ^ n⌉
    · simp only [hk, ↓reduceIte]
      exact hω n _ hk
    · simp only [hk, ↓reduceIte]
  rw [heq]
  exact CirclePairing.radialVersion_eq (CirclePairing.continuousOn_radial hc) hr

/-- Centered circle averages recovered as a Borel function of a distribution.
Outside the cone-law event the limsup convention supplies a total function. -/
def distributionRadialVersion (H : LQGMetric.DistC) (r : ℝ) : ℝ :=
  CirclePairing.radialVersion
    (fun d s _ => limsup (fun n => d (LQGMetric.CircleAvg.circBump n 0 s)) atTop) H r

/-- The distribution-to-centered-circle map is jointly Borel measurable. -/
theorem measurable_distributionRadialVersion :
    Measurable (Function.uncurry distributionRadialVersion) := by
  apply CirclePairing.measurable_radialVersion
  intro r z hr
  exact Measurable.limsup fun n => LQGMetric.measurable_distOn_apply _

/-- The field-measurable distribution from the countable code recovers all
positive centered circles on one common event. -/
theorem exists_fieldMeasurable_distribution_with_radial
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ H : Ω → LQGMetric.DistC, Measurable[S.fieldSigma] H ∧
      (∀ᵐ ω ∂S.P, (∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) ∧
        ∀ r : ℝ, 0 < r → distributionRadialVersion (H ω) r = S.hcirc ω r 0) := by
  obtain ⟨H, hHm, hH⟩ := exists_fieldMeasurable_coneDistribution hS
  refine ⟨H, hHm, ?_⟩
  filter_upwards [hH, ae_fieldRadialVersion_eq hS] with ω hω hr
  refine ⟨hω, ?_⟩
  have hcircle : ∀ s : ℝ,
      (limsup (fun k => H ω (LQGMetric.CircleAvg.circBump k 0 s)) atTop) =
        FieldCircle.circleField S s 0 ω := by
    intro s
    unfold FieldCircle.circleField
    apply congrArg (fun f : ℕ → ℝ => limsup f atTop)
    funext k
    exact (hω _).symm
  intro r hrpos
  rw [← hr r hrpos]
  unfold distributionRadialVersion fieldRadialVersion CirclePairing.radialVersion
  apply congrArg (fun f : ℕ → ℝ => limsup f atTop)
  funext n
  unfold CirclePairing.radialApprox
  split
  · exact hcircle _
  · rfl

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
    (hscale : QuantumConeScalingInput)
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
  apply exists_rescaled_pairing_of_variableDilation variableDilationPairingStep hS R hRm
  filter_upwards [hR, hpos] with ω hRω hposω
  exact ⟨hRω, hRω ▸ hposω.ne'⟩

end MatedCRT.Sec1

