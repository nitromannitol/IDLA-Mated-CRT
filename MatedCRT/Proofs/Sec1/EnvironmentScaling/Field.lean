import MatedCRT.Proofs.Sec1.EnvironmentScaling.DistributionCode
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

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

/-- At each circle avoiding the origin, Bonanno's distributional circle
average agrees almost surely with the cone circle observable. This is an
agreement at a fixed circle; no simultaneous continuity of `circleAvg` is
claimed. -/
theorem ae_distribution_circleAvg_eq
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC}
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≠ r) :
    ∀ᵐ ω ∂S.P, LQGMetric.circleAvg (H ω) r z = S.hcirc ω r z := by
  filter_upwards [hH, CirclePairing.ae_tendsto_circBump_of_isQuantumCone
    hS.isQuantumCone hr hz] with ω hω ht
  have ht' : Tendsto (fun n => Real.circleAverage
      (fun x => H ω (LQGMetric.bumpTest n x)) z r) atTop (𝓝 (S.hcirc ω r z)) := by
    apply ht.congr
    intro n
    rw [LQGMetric.CircleAvg.circleAverage_pairing]
    exact hω _
  exact ht'.limUnder_eq

/-- A grid center has irrational norm: in particular it avoids every dyadic
radius, not only reciprocal powers of two. -/
theorem norm_gridPt_ne_dyadic (m n : ℕ) (a b k : ℤ) :
    ‖FieldCircle.gridPt m a b‖ ≠ (k : ℝ) / 2 ^ n := by
  intro h
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  have h2 : ‖FieldCircle.gridPt m a b‖ ^ 2 * ((2 : ℝ) ^ n) ^ 2 = (k : ℝ) ^ 2 := by
    rw [h, div_pow]
    field_simp
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  simp only [FieldCircle.gridPt] at h2
  have hR : (((3 * a + 1) ^ 2 + (3 * b + 1) ^ 2) * ((2 : ℤ) ^ n) ^ 2 : ℤ) =
      ((9 * k ^ 2 * ((2 : ℤ) ^ m) ^ 2 : ℤ) : ℝ) := by
    push_cast
    field_simp at h2
    linear_combination h2
  have hZ : ((3 * a + 1) ^ 2 + (3 * b + 1) ^ 2) * ((2 : ℤ) ^ n) ^ 2 =
      9 * k ^ 2 * ((2 : ℤ) ^ m) ^ 2 := by
    exact_mod_cast hR
  have h3 := congrArg (fun x : ℤ => (x : ZMod 3)) hZ
  push_cast at h3
  have e3 : (3 : ZMod 3) = 0 := rfl
  have e9 : (9 : ZMod 3) = 0 := rfl
  have e4 : ((2 : ZMod 3) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
    have : (2 : ZMod 3) ^ 2 = 1 := rfl
    rw [this, one_pow]
  rw [e3, e9, e4] at h3
  simp only [zero_mul, zero_add, one_pow, mul_one] at h3
  exact absurd h3 (by decide)

/-- The spatial interpolation at an arbitrary dyadic radius. -/
def distributionCircleAtDyadic (n : ℕ) (k : ℤ) (H : LQGMetric.DistC) (z : ℂ) : ℝ :=
  FieldCircle.gridVersion (fun w d => LQGMetric.circleAvg d ((k : ℝ) / 2 ^ n) w) H z

theorem measurable_distributionCircleAtDyadic (n : ℕ) (k : ℤ) :
    Measurable (Function.uncurry (distributionCircleAtDyadic n k)) := by
  let X : ℂ → LQGMetric.DistC → ℝ := fun w d => LQGMetric.circleAvg d ((k : ℝ) / 2 ^ n) w
  have hm : ∀ w, Measurable (X w) := fun w => LQGMetric.measurable_circleAvg_left _ w
  change Measurable (Function.uncurry (FieldCircle.gridVersion X))
  exact FieldCircle.measurable_gridVersion X hm

theorem ae_distributionCircleAtDyadic_eq
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC}
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ n : ℕ, ∀ k : ℤ, 0 < k → ∀ z : ℂ,
      distributionCircleAtDyadic n k (H ω) z = S.hcirc ω ((k : ℝ) / 2 ^ n) z := by
  have hgrid : ∀ᵐ ω ∂S.P, ∀ n m : ℕ, ∀ k a b : ℤ, 0 < k →
      LQGMetric.circleAvg (H ω) ((k : ℝ) / 2 ^ n) (FieldCircle.gridPt m a b) =
        S.hcirc ω ((k : ℝ) / 2 ^ n) (FieldCircle.gridPt m a b) := by
    simp only [ae_all_iff]
    intro n m k a b hk
    apply ae_distribution_circleAvg_eq hS hH
      (div_pos (Int.cast_pos.mpr hk) (by positivity))
    exact norm_gridPt_ne_dyadic m n a b k
  filter_upwards [hgrid, hS.isQuantumCone.ae_continuousOn_circle] with ω hg hc n k hk z
  have hcont : Continuous fun w => S.hcirc ω ((k : ℝ) / 2 ^ n) w := by
    rw [← continuousOn_univ]
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
      fun w _ => ⟨mem_Ioi.2 (div_pos (Int.cast_pos.mpr hk) (by positivity)), mem_univ _⟩
  exact FieldCircle.gridVersion_eq hcont (fun m a b => hg n m k a b hk) z

/-- A distributional version of the positive-radius circle process. -/
def distributionCircleVersion (H : LQGMetric.DistC) (r : ℝ) (z : ℂ) : ℝ :=
  limsup (fun n : ℕ => if 0 < ⌈r * 2 ^ n⌉ then
    distributionCircleAtDyadic n ⌈r * 2 ^ n⌉ H z else 0) atTop

/-- The full circle version is jointly Borel measurable. -/
theorem measurable_distributionCircleVersion :
    Measurable fun p : LQGMetric.DistC × ℝ × ℂ => distributionCircleVersion p.1 p.2.1 p.2.2 := by
  apply Measurable.limsup
  intro n
  have hg : Measurable fun p : (LQGMetric.DistC × ℂ) × ℤ =>
      if 0 < p.2 then distributionCircleAtDyadic n p.2 p.1.1 p.1.2 else 0 := by
    apply measurable_from_prod_countable_left
    intro k
    by_cases hk : 0 < k
    · change Measurable fun p : LQGMetric.DistC × ℂ =>
        if 0 < k then distributionCircleAtDyadic n k p.1 p.2 else 0
      simp only [hk, ↓reduceIte]
      change Measurable (Function.uncurry (distributionCircleAtDyadic n k))
      exact measurable_distributionCircleAtDyadic n k
    · simpa only [hk, ↓reduceIte] using (measurable_const : Measurable fun _ : LQGMetric.DistC × ℂ => (0 : ℝ))
  exact hg.comp ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
    (Int.measurable_ceil.comp ((measurable_fst.comp measurable_snd).mul_const _)))

/-- On one event, the distributional version recovers every positive-radius
circle at every center. -/
theorem ae_distributionCircleVersion_eq
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC}
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      distributionCircleVersion (H ω) r z = S.hcirc ω r z := by
  filter_upwards [ae_distributionCircleAtDyadic_eq hS hH,
    hS.isQuantumCone.ae_continuousOn_circle] with ω hω hc r hr z
  have hpos : ∀ n : ℕ, 0 < ⌈r * 2 ^ n⌉ := fun n => Int.ceil_pos.2 (by positivity)
  have hcont : ContinuousOn (fun s : ℝ => S.hcirc ω s z) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn fun s hs => ⟨hs, mem_univ _⟩
  have ht : Tendsto (fun n : ℕ => if 0 < ⌈r * 2 ^ n⌉ then
      distributionCircleAtDyadic n ⌈r * 2 ^ n⌉ (H ω) z else 0) atTop (𝓝 (S.hcirc ω r z)) := by
    have ht' := (hcont.continuousAt (Ioi_mem_nhds hr)).tendsto.comp
      (CirclePairing.tendsto_dyadicCeil r)
    apply ht'.congr
    intro n
    simp only [hpos n, ↓reduceIte, CirclePairing.dyadicCeil, Function.comp_apply]
    exact (hω n _ (hpos n) z).symm
  exact ht.limsup_eq

/-- The countably decoded distribution is field-measurable and recovers both
the test pairings and the entire positive-radius circle process on one event. -/
theorem exists_fieldMeasurable_distribution_with_circles
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ H : Ω → LQGMetric.DistC, Measurable[S.fieldSigma] H ∧
      ∀ᵐ ω ∂S.P, (∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) ∧
        ∀ r : ℝ, 0 < r → ∀ z : ℂ,
          distributionCircleVersion (H ω) r z = S.hcirc ω r z := by
  obtain ⟨H, hHm, hH⟩ := exists_fieldMeasurable_coneDistribution hS
  refine ⟨H, hHm, ?_⟩
  filter_upwards [hH, ae_distributionCircleVersion_eq hS hH] with ω hpair hcircle
  exact ⟨hpair, hcircle⟩

/-- The positive-radius circle process recovered from a distribution, indexed
by positive radii and centers. -/
def distributionCircleCode (H : LQGMetric.DistC) : (Ioi (0 : ℝ) × ℂ) → ℝ :=
  fun p => distributionCircleVersion H p.1 p.2

/-- A fixed positive-radius circle evaluation is Borel. -/
theorem measurable_distributionCircleVersion_fixed (r : ℝ) (z : ℂ) :
    Measurable (fun H : LQGMetric.DistC => distributionCircleVersion H r z) := by
  have hp : Measurable (fun H : LQGMetric.DistC => (H, (r, z))) :=
    measurable_id.prodMk measurable_const
  have hm := measurable_distributionCircleVersion.comp hp
  simpa only [Function.comp_def] using hm

/-- The circle code is measurable for the cylinder sigma algebra. -/
theorem measurable_distributionCircleCode : Measurable distributionCircleCode := by
  refine (measurable_pi_iff (g := distributionCircleCode)).2 ?_
  intro p
  exact measurable_distributionCircleVersion_fixed p.1 p.2

/-- Equal distribution laws determine the joint laws of the distribution and
its recovered positive-radius circle process. -/
theorem map_distribution_circleCode_eq_of_map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {H : Ω → LQGMetric.DistC}
    {H' : Ω' → LQGMetric.DistC} (hH : Measurable H) (hH' : Measurable H')
    (hlaw : P.map H = P'.map H') :
    P.map (fun ω => (H ω, distributionCircleCode (H ω))) =
      P'.map (fun ω => (H' ω, distributionCircleCode (H' ω))) := by
  have hm : Measurable (fun h : LQGMetric.DistC => (h, distributionCircleCode h)) :=
    measurable_id.prodMk measurable_distributionCircleCode
  change P.map ((fun h : LQGMetric.DistC => (h, distributionCircleCode h)) ∘ H) =
    P'.map ((fun h : LQGMetric.DistC => (h, distributionCircleCode h)) ∘ H')
  rw [← Measure.map_map hm hH, ← Measure.map_map hm hH', hlaw]

/-- A represented field has the same joint law as any distribution with the
same law, paired with that distribution's recovered circle code. -/
theorem map_distribution_circles_eq_code_of_map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {S : MatedCRTEnv Ω} {P' : Measure Ω'}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC}
    (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hlaw : S.P.map H = P'.map H') :
    S.P.map (fun ω => (H ω, fun p : Ioi (0 : ℝ) × ℂ => S.hcirc ω p.1 p.2)) =
      P'.map (fun ω => (H' ω, distributionCircleCode (H' ω))) := by
  have hleft : (fun ω => (H ω, distributionCircleCode (H ω))) =ᵐ[S.P]
      fun ω => (H ω, fun p : Ioi (0 : ℝ) × ℂ => S.hcirc ω p.1 p.2) := by
    filter_upwards [ae_distributionCircleVersion_eq hS hrep] with ω hω
    congr 1
    funext p
    exact hω p.1 p.1.property p.2
  rw [← Measure.map_congr hleft]
  exact map_distribution_circleCode_eq_of_map_eq hH hH' hlaw

/-- For valid environments, equality of represented distribution laws gives
equality of their joint distribution and positive-radius circle laws. -/
theorem map_distribution_circles_eq_of_map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'}
    {𝒮 𝒮' : SpaceFillingSLEModel} {γ γ' : ℝ}
    (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ')
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC}
    (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂S'.P, ∀ φ : LQGMetric.TestC, S'.hC ω φ = H' ω φ)
    (hlaw : S.P.map H = S'.P.map H') :
    S.P.map (fun ω => (H ω, fun p : Ioi (0 : ℝ) × ℂ => S.hcirc ω p.1 p.2)) =
      S'.P.map (fun ω => (H' ω, fun p : Ioi (0 : ℝ) × ℂ => S'.hcirc ω p.1 p.2)) := by
  have hleft : (fun ω => (H ω, distributionCircleCode (H ω))) =ᵐ[S.P]
      fun ω => (H ω, fun p : Ioi (0 : ℝ) × ℂ => S.hcirc ω p.1 p.2) := by
    filter_upwards [ae_distributionCircleVersion_eq hS hrep] with ω hω
    congr 1
    funext p
    exact hω p.1 p.1.property p.2
  have hright : (fun ω => (H' ω, distributionCircleCode (H' ω))) =ᵐ[S'.P]
      fun ω => (H' ω, fun p : Ioi (0 : ℝ) × ℂ => S'.hcirc ω p.1 p.2) := by
    filter_upwards [ae_distributionCircleVersion_eq hS' hrep'] with ω hω
    congr 1
    funext p
    exact hω p.1 p.1.property p.2
  rw [← Measure.map_congr hleft, ← Measure.map_congr hright]
  exact map_distribution_circleCode_eq_of_map_eq hH hH' hlaw

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

