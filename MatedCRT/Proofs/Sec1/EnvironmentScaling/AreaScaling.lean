import MatedCRT.Defs.Setting
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime
import HarmonicBalls.Proofs.Sec9.LQGSpatialDilation
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.PartitionOfUnity

/-!
# Area measure at a random radius

Deterministic parts of `env-steps.tex`, Lemma `area-scale`, lines 693–747.
The all-scale convergence away from zero is an explicit hypothesis, not a
consequence of dyadic convergence. Under this hypothesis, the regularized
change of variables and nonatomicity identify the rescaled area measure even
at a sample-dependent radius. The Weyl scaling proof uses infrastructure of
Leonardo Bonanno through the LatticeProb.Bonanno dependency of the Harmonic
Balls Weyl-scaling module. A separate earlier bridge assumes the stronger
global radius-change limit; neither bridge proves the all-scale hypothesis.
-/

open MeasureTheory Filter Set
open HarmonicBalls
open scoped ENNReal Topology

namespace MatedCRT.Sec1

/-- A space-filling curve parametrized by area forces every singleton to be null. -/
theorem IsAreaParametrized.nullSingletonClass {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) : NullSingletonClass μ := by
  constructor
  intro z
  obtain ⟨t, rfl⟩ := h.2.2.1 z
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hεtop
  let u : ℝ := ε
  have hu : 0 < u := by exact_mod_cast hε
  have hsub : {η t} ⊆ η '' Icc t (t + u) := by
    intro x hx
    simp only [mem_singleton_iff] at hx
    exact ⟨t, ⟨le_rfl, le_add_of_nonneg_right hu.le⟩, hx.symm⟩
  have hm := (measure_mono hsub).trans_eq (h.2.2.2 t (t + u) (by linarith))
  simp only [add_sub_cancel_left] at hm
  simpa only [bot_eq_zero, zero_add, ENNReal.ofReal_coe_nnreal, u] using hm

/-- Measures equal off a null singleton agree everywhere. -/
theorem measure_eq_of_restrict_compl_singleton {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {x : α} (hμ : μ {x} = 0) (hν : ν {x} = 0)
    (h : μ.restrict ({x}ᶜ) = ν.restrict ({x}ᶜ)) : μ = ν := by
  have hμ' : μ.restrict ({x}ᶜ) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by simpa only [ae_iff, mem_compl_iff, not_not, ofPred_mem_eq] using hμ)
  have hν' : ν.restrict ({x}ᶜ) = ν :=
    Measure.restrict_eq_self_of_ae_mem (by simpa only [ae_iff, mem_compl_iff, not_not, ofPred_mem_eq] using hν)
  exact hμ'.symm.trans (h.trans hν')

/-- A radius-change limit at an arbitrary positive radius yields the exact
rescaled LQG measure. The hypothesis `hshift` is the normalized limit at
radii `R * 2⁻ⁿ`; it is not implied by dyadic convergence alone. -/
theorem isLQGLimit_rescaled_of_radius_shift {γ R b : ℝ} (hγ : γ ≠ 0)
    (hR : 0 < R) (hb : 0 < b) {h : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (hshift : IsLQGLimit γ (fun r z => h (R * r) z + γ / 2 * Real.log R) μ)
    (hc : ∀ n, Continuous (h (R * dyadicScale n))) :
    IsLQGLimit γ (rescaledCircle γ h R b) (rescaledMeasure μ R b) := by
  have hc' : ∀ n, Continuous (fun z => h (R * dyadicScale n) z + γ / 2 * Real.log R) :=
    fun n => (hc n).add continuous_const
  have hs := hshift.spatial_dilation hc' hR
  have ht := hs.add_const ((2 / γ) * Real.log R - γ⁻¹ * Real.log b)
  have he : Real.exp (γ * ((2 / γ) * Real.log R - γ⁻¹ * Real.log b)) = R ^ 2 * b⁻¹ := by
    have heq : γ * ((2 / γ) * Real.log R - γ⁻¹ * Real.log b) =
        (Real.log R + Real.log R) - Real.log b := by
      field_simp
      ring
    rw [heq, Real.exp_sub, Real.exp_add, Real.exp_log hR, Real.exp_log hb]
    ring
  have hscalar : ENNReal.ofReal (Real.exp (γ * ((2 / γ) * Real.log R - γ⁻¹ * Real.log b))) •
      (ENNReal.ofReal (R⁻¹ ^ 2) • μ.map (fun z : ℂ => R⁻¹ • z)) =
      rescaledMeasure μ R b := by
    rw [smul_smul, he, ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (inv_nonneg.2 hb.le))]
    have hfactor : R ^ 2 * b⁻¹ * R⁻¹ ^ 2 = b⁻¹ := by
      have : R ^ 2 * R⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hR.ne', one_pow]
      calc
        R ^ 2 * b⁻¹ * R⁻¹ ^ 2 = (R ^ 2 * R⁻¹ ^ 2) * b⁻¹ := by ring
        _ = b⁻¹ := by rw [this, one_mul]
    rw [hfactor]
    unfold rescaledMeasure
    congr 2
    funext z
    simp only [Complex.real_smul, Complex.ofReal_inv]
  rw [hscalar] at ht
  convert ht using 1
  funext r z
  simp only [rescaledCircle, Complex.real_smul]
  dsimp [lqgQ]
  ring

/-- The radius may depend arbitrarily on the sample: no independence or
measurability of the radius is needed once its pathwise limit is supplied. -/
theorem isLQGMeasure_rescaled_of_radius_shift {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ b : ℝ} (hγ : γ ≠ 0) (hb : 0 < b)
    {h : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (R : Ω → ℝ)
    (hgood : ∀ᵐ ω ∂P, 0 < R ω ∧
      IsLQGLimit γ (fun r z => h ω (R ω * r) z + γ / 2 * Real.log (R ω)) (μ ω) ∧
      ∀ n, Continuous (h ω (R ω * dyadicScale n))) :
    IsLQGMeasure P γ (fun ω => rescaledCircle γ (h ω) (R ω) b)
      (fun ω => rescaledMeasure (μ ω) (R ω) b) := by
  filter_upwards [hgood] with ω hω
  exact isLQGLimit_rescaled_of_radius_shift hγ hω.1 hb hω.2.1 hω.2.2

/-- Any separately constructed LQG limit of the rescaled circle averages
agrees with the normalized push-forward under the radius-shift hypothesis. -/
theorem ae_rescaled_measure_eq_of_radius_shift {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ b : ℝ} (hγ : γ ≠ 0) (hb : 0 < b)
    {h : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ} (R : Ω → ℝ)
    (hgood : ∀ᵐ ω ∂P, 0 < R ω ∧
      IsLQGLimit γ (fun r z => h ω (R ω * r) z + γ / 2 * Real.log (R ω)) (μ ω) ∧
      ∀ n, Continuous (h ω (R ω * dyadicScale n)))
    (hν : IsLQGMeasure P γ (fun ω => rescaledCircle γ (h ω) (R ω) b) ν) :
    ∀ᵐ ω ∂P, ν ω = rescaledMeasure (μ ω) (R ω) b := by
  exact hν.ae_eq (isLQGMeasure_rescaled_of_radius_shift hγ hb R hgood)

/-- An off-origin limit of the dyadic approximations identifies the global
LQG limit when both candidate measures have zero mass at the origin. This
uses no convergence of the approximations across the origin beyond the
already supplied dyadic LQG limit. -/
theorem isLQGLimit_eq_of_off_origin {γ : ℝ} {h : ℝ → ℂ → ℝ}
    {ν μ : Measure ℂ} (hν : IsLQGLimit γ h ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν0 : ν {0} = 0) (hμ0 : μ {0} = 0)
    (hoff : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ({0} : Set ℂ)ᶜ →
      Tendsto (fun n : ℕ => ∫ z, f z ∂(lqgApprox γ h (dyadicScale n)))
        atTop (𝓝 (∫ z, f z ∂μ))) : ν = μ := by
  have : IsLocallyFiniteMeasure ν := hν.isLocallyFiniteMeasure
  have : IsLocallyFiniteMeasure μ := hμ
  apply measure_eq_of_restrict_compl_singleton hν0 hμ0
  apply restrict_eq_of_integral_eq_of_tsupport_subset isClosed_singleton.isOpen_compl
  intro f hf hfc hs
  exact tendsto_nhds_unique (hν.tendsto_integral f hf hfc) (hoff f hf hfc hs)

/-- The planar Jacobian in a spatial dilation of one circle-average
approximation, at any positive regularization scale. -/
theorem integral_lqgApprox_spatial_dilation {γ r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) {h : ℝ → ℂ → ℝ}
    (hc : Continuous (h r)) (f : ℂ → ℝ) :
    (∫ z, f z ∂(lqgApprox γ (fun t z => h t (R • z)) r)) =
      R⁻¹ ^ 2 * ∫ z, f (R⁻¹ • z) ∂(lqgApprox γ h r) := by
  let w : ℂ → ℝ := fun z => r ^ (γ ^ 2 / 2) * Real.exp (γ * h r z)
  have hw : Continuous w := continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul hc))
  have hw0 : ∀ z, 0 ≤ w z := fun z => mul_nonneg
    (Real.rpow_nonneg hr.le _) (Real.exp_nonneg _)
  change (∫ z, f z ∂(volume.withDensity fun z => ENNReal.ofReal (w (R • z)))) =
    R⁻¹ ^ 2 * ∫ z, f (R⁻¹ • z) ∂(volume.withDensity fun z => ENNReal.ofReal (w z))
  rw [Section6.integral_withDensity_nonnegative volume (fun z => w (R • z)) f
      (hw.comp (continuous_const_smul R)) (fun z => hw0 (R • z)),
    Section6.integral_withDensity_nonnegative volume w (fun z => f (R⁻¹ • z)) hw hw0]
  have hcomp : (fun x : ℂ => f (R⁻¹ • (R • x)) * w (R • x)) =
      (fun x => f x * w (R • x)) := by
    funext x
    simp [hR.ne']
  have hs := Measure.integral_comp_smul volume (fun z : ℂ => f (R⁻¹ • z) * w z) R
  rw [hcomp] at hs
  rw [Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (pow_pos hR _)), ← inv_pow,
    smul_eq_mul] at hs
  exact hs

/-- The pointwise normalization in the regularized coordinate change.
The spatial Jacobian is handled separately by
`integral_lqgApprox_spatial_dilation`. -/
theorem lqgApprox_rescaled_normalization {γ R b ε : ℝ}
    (hγ : γ ≠ 0) (hR : 0 < R) (hb : 0 < b) (hε : 0 < ε)
    (h : ℝ → ℂ → ℝ) :
    lqgApprox γ (rescaledCircle γ h R b) ε =
      ENNReal.ofReal (R ^ 2 * b⁻¹) •
        lqgApprox γ (fun t z => h t (R • z)) (R * ε) := by
  have heq : γ * (lqgQ γ * Real.log R - γ⁻¹ * Real.log b) =
      (γ ^ 2 / 2) * Real.log R + (Real.log R + Real.log R) - Real.log b := by
    dsimp [lqgQ]
    field_simp
    ring
  have he : Real.exp (γ * (lqgQ γ * Real.log R - γ⁻¹ * Real.log b)) =
      R ^ (γ ^ 2 / 2) * (R ^ 2 * b⁻¹) := by
    rw [heq, Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hR,
      Real.exp_log hb, Real.rpow_def_of_pos hR]
    ring
  simp only [lqgApprox]
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg R) (inv_nonneg.2 hb.le))]
  congr 1
  simp only [rescaledCircle, Complex.real_smul]
  rw [show h (R * ε) ((R : ℂ) * z) + lqgQ γ * Real.log R - γ⁻¹ * Real.log b =
    h (R * ε) ((R : ℂ) * z) + (lqgQ γ * Real.log R - γ⁻¹ * Real.log b) by ring,
    mul_add, Real.exp_add, he, Real.mul_rpow hR.le hε.le]
  ring

/-- The regularized area scaling identity, tested against an arbitrary
function. This is equation `approxscale` in `env-steps.tex`, lines 733–739. -/
theorem integral_lqgApprox_rescaled {γ R b ε : ℝ}
    (hγ : γ ≠ 0) (hR : 0 < R) (hb : 0 < b) (hε : 0 < ε)
    {h : ℝ → ℂ → ℝ} (hc : Continuous (h (R * ε))) (f : ℂ → ℝ) :
    (∫ z, f z ∂(lqgApprox γ (rescaledCircle γ h R b) ε)) =
      b⁻¹ * ∫ z, f (R⁻¹ • z) ∂(lqgApprox γ h (R * ε)) := by
  rw [lqgApprox_rescaled_normalization hγ hR hb hε, integral_smul_measure,
    ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg R) (inv_nonneg.2 hb.le)), smul_eq_mul,
    integral_lqgApprox_spatial_dilation (mul_pos hR hε) hR hc]
  have hfactor : (R ^ 2 * b⁻¹) * R⁻¹ ^ 2 = b⁻¹ := by
    have : R ^ 2 * R⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hR.ne', one_pow]
    calc
      (R ^ 2 * b⁻¹) * R⁻¹ ^ 2 = (R ^ 2 * R⁻¹ ^ 2) * b⁻¹ := by ring
      _ = b⁻¹ := by rw [this, one_mul]
  rw [← mul_assoc, hfactor]

/-- All-scale convergence away from the origin transports to the dyadic
approximations of the field at any prescribed positive radius. The hypothesis
is pathwise and may be used simultaneously for a sample-dependent radius. -/
theorem tendsto_rescaled_off_origin {γ R b : ℝ} (hγ : γ ≠ 0)
    (hR : 0 < R) (hb : 0 < b) {h : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (hc : ∀ n, Continuous (h (R * dyadicScale n)))
    (hall : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ({0} : Set ℂ)ᶜ →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ h ε))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ))) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ({0} : Set ℂ)ᶜ →
      Tendsto (fun n : ℕ => ∫ z, f z ∂(lqgApprox γ (rescaledCircle γ h R b) (dyadicScale n)))
        atTop (𝓝 (∫ z, f z ∂(rescaledMeasure μ R b))) := by
  intro f hf hfc hf0
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne')
  let ψ : ℂ → ℝ := fun z => f (R⁻¹ • z)
  have hψ : Continuous ψ := hf.comp (continuous_const_smul _)
  have hψc : HasCompactSupport ψ := hfc.comp_homeomorph e
  have hψ0 : tsupport ψ ⊆ ({0} : Set ℂ)ᶜ := by
    change tsupport (f ∘ e) ⊆ ({0} : Set ℂ)ᶜ
    rw [tsupport_comp_eq_preimage]
    intro z hz
    have hz' := hf0 hz
    intro hz0
    have : z = 0 := by simpa only [mem_singleton_iff] using hz0
    subst z
    exact hz' (by simp [e])
  have hseq : Tendsto (fun n : ℕ => R * dyadicScale n) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using
        (tendsto_const_nhds.mul (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds))
    · exact Filter.Eventually.of_forall (fun n => mul_pos hR (dyadicScale_pos n))
  have hlim := ((hall ψ hψ hψc hψ0).comp hseq).const_mul b⁻¹
  have htarget : (∫ z, f z ∂(rescaledMeasure μ R b)) = b⁻¹ * ∫ z, ψ z ∂μ := by
    rw [rescaledMeasure, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hb.le),
      smul_eq_mul, integral_map (by fun_prop) hf.aestronglyMeasurable]
    simp only [ψ, Complex.real_smul, Complex.ofReal_inv]
  rw [htarget]
  convert hlim using 1
  funext n
  exact integral_lqgApprox_rescaled hγ hR hb (dyadicScale_pos n) (hc n) f

/-- The normalized spatial push-forward is locally finite and has no atom at
the origin when the original locally finite measure has no atom there. -/
theorem rescaledMeasure_local_and_origin_null {μ : Measure ℂ} {R b : ℝ}
    (hR : 0 < R) (hμ : IsLocallyFiniteMeasure μ) (hμ0 : μ {0} = 0) :
    IsLocallyFiniteMeasure (rescaledMeasure μ R b) ∧ rescaledMeasure μ R b {0} = 0 := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne')
  have : IsLocallyFiniteMeasure μ := hμ
  have : IsFiniteMeasureOnCompacts (μ.map e) := Measure.IsFiniteMeasureOnCompacts.map μ e
  have : IsFiniteMeasureOnCompacts (ENNReal.ofReal b⁻¹ • μ.map e) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  have he : (fun z : ℂ => (R : ℂ)⁻¹ * z) = e := by
    funext z
    simp only [e, Homeomorph.smulOfNeZero_apply, Complex.real_smul, Complex.ofReal_inv]
  constructor
  · rw [rescaledMeasure, he]
    infer_instance
  · rw [rescaledMeasure, Measure.smul_apply, Measure.map_apply
      (by fun_prop : Measurable (fun x : ℂ => (R : ℂ)⁻¹ * x)) (measurableSet_singleton 0)]
    have hs : (fun x : ℂ => (R : ℂ)⁻¹ * x) ⁻¹' ({0} : Set ℂ) = {0} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      rw [mul_eq_zero]
      have hne : (R : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hR.ne')
      simp only [hne, false_or]
    rw [hs, hμ0, smul_eq_mul, mul_zero]

/-- Identification of the rescaled area measure from all-scale convergence
away from zero, without a global all-scale convergence assumption. -/
theorem rescaled_measure_eq_of_allScale_off_origin {γ R b : ℝ}
    (hγ : γ ≠ 0) (hR : 0 < R) (hb : 0 < b)
    {h : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) (hμ0 : μ {0} = 0)
    (hν : IsLQGLimit γ (rescaledCircle γ h R b) ν) (hν0 : ν {0} = 0)
    (hc : ∀ n, Continuous (h (R * dyadicScale n)))
    (hall : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ({0} : Set ℂ)ᶜ →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ h ε))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ))) :
    ν = rescaledMeasure μ R b := by
  obtain ⟨hloc, hzero⟩ := rescaledMeasure_local_and_origin_null hR hμ hμ0
  exact isLQGLimit_eq_of_off_origin hν hloc hν0 hzero
    (tendsto_rescaled_off_origin hγ hR hb hc hall)

/-- The off-origin scaling argument also applies to a sample-dependent radius:
the all-scale convergence event is chosen before evaluating the radius. -/
theorem ae_rescaled_measure_eq_of_allScale_off_origin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ b : ℝ}
    (hγ : γ ≠ 0) (hb : 0 < b) {h : Ω → ℝ → ℂ → ℝ}
    {μ ν : Ω → Measure ℂ} (R : Ω → ℝ)
    (hgood : ∀ᵐ ω ∂P, 0 < R ω ∧ IsLocallyFiniteMeasure (μ ω) ∧ μ ω {0} = 0 ∧
      (∀ n, Continuous (h ω (R ω * dyadicScale n))) ∧
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
        tsupport f ⊆ ({0} : Set ℂ)ᶜ →
        Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (h ω) ε))
          (𝓝[>] 0) (𝓝 (∫ z, f z ∂(μ ω))))
    (hν : IsLQGMeasure P γ (fun ω => rescaledCircle γ (h ω) (R ω) b) ν)
    (hν0 : ∀ᵐ ω ∂P, ν ω {0} = 0) :
    ∀ᵐ ω ∂P, ν ω = rescaledMeasure (μ ω) (R ω) b := by
  filter_upwards [hgood, hν, hν0] with ω hg hv hv0
  exact rescaled_measure_eq_of_allScale_off_origin hγ hg.1 hb hg.2.1 hg.2.2.1
    hv hv0 hg.2.2.2.1 hg.2.2.2.2

/-- An all-scale limit on tests away from zero has the same test integrals as
an existing dyadic LQG limit. The two measures need not be known equal on the
whole plane. -/
theorem tendsto_off_origin_to_lqgLimit {γ : ℝ} {h : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμ : IsLQGLimit γ h μ)
    (hall : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ({0} : Set ℂ)ᶜ →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ h ε))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂ν))) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ({0} : Set ℂ)ᶜ →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ h ε))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ)) := by
  intro f hf hfc hf0
  have heq : (∫ z, f z ∂μ) = ∫ z, f z ∂ν :=
    tendsto_nhds_unique (hμ.tendsto_integral f hf hfc)
      ((hall f hf hfc hf0).comp tendsto_dyadicScale_nhdsGT)
  rw [heq]
  exact hall f hf hfc hf0

/-- Joint continuity of circle averages gives spatial continuity simultaneously
at every positive radius. -/
theorem continuous_circle_of_continuousOn {h : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Ioi 0 ×ˢ univ))
    {r : ℝ} (hr : 0 < r) : Continuous (h r) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hp : ContinuousAt (fun p : ℝ × ℂ => h p.1 p.2) (r, z) :=
    (isOpen_Ioi.prod isOpen_univ).continuousOn_iff.mp hc ⟨hr, mem_univ _⟩
  exact hp.comp ((continuous_const.prodMk continuous_id).continuousAt)

/-- In a valid environment the original LQG measure is locally finite and
nonatomic, and all positive-radius circle averages are continuous, on a single
event independent of the choice of radius. -/
theorem MatedCRTEnv.IsValid.ae_area_and_circle_regular {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) ∧ S.μ ω {0} = 0 ∧
      ∀ r : ℝ, 0 < r → Continuous (S.hcirc ω r) := by
  filter_upwards [hS.isLQGMeasure, hS.isAreaParametrized,
    hS.isQuantumCone.ae_continuousOn_circle] with ω hμ hη hc
  have hnull : NullSingletonClass (S.μ ω) := IsAreaParametrized.nullSingletonClass hη
  exact ⟨hμ.isLocallyFiniteMeasure, hnull.1 0, fun r hr => continuous_circle_of_continuousOn hc hr⟩

/-- In a valid environment an independently constructed all-scale limit away
from zero suffices for area scaling. The second area-parametrized curve supplies
nonatomicity of the separately constructed rescaled LQG measure. -/
theorem MatedCRTEnv.IsValid.ae_rescaled_measure_eq_of_off_origin_limit
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : γ ≠ 0) (hb : 0 < b) (R : Ω → ℝ) {ν m : Ω → Measure ℂ}
    {η' : Ω → ℝ → ℂ}
    (hR : ∀ᵐ ω ∂S.P, 0 < R ω)
    (hν : IsLQGMeasure S.P γ (fun ω => rescaledCircle γ (S.hcirc ω) (R ω) b) ν)
    (hη' : ∀ᵐ ω ∂S.P, IsAreaParametrized (ν ω) (η' ω))
    (hall : ∀ᵐ ω ∂S.P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ ({0} : Set ℂ)ᶜ →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (S.hcirc ω) ε))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂(m ω)))) :
    ∀ᵐ ω ∂S.P, ν ω = rescaledMeasure (S.μ ω) (R ω) b := by
  filter_upwards [MatedCRTEnv.IsValid.ae_area_and_circle_regular hS, hS.isLQGMeasure, hR, hν, hη', hall] with
    ω hreg hμ hRω hνω hηω hallω
  have hnull : NullSingletonClass (ν ω) := IsAreaParametrized.nullSingletonClass hηω
  exact rescaled_measure_eq_of_allScale_off_origin hγ hRω hb hreg.1 hreg.2.1
    hνω (hnull.1 0) (fun n => hreg.2.2 _ (mul_pos hRω (dyadicScale_pos n)))
    (tendsto_off_origin_to_lqgLimit hμ hallω)

/-- All-scale vague convergence is stable under adding a continuous function.
This deterministic form holds simultaneously for arbitrary continuous functions,
including functions depending on the same sample as the original field. -/
theorem tendsto_lqgApprox_addCircleAverage_allScale {γ : ℝ} {h : ℝ → ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    (hc : ∀ r : ℝ, 0 < r → Continuous (h r))
    (hall : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
      Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ h r))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ)))
    (v : ℂ → ℝ) (hv : Continuous v) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
      Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ (addCircleAverage h v) r))
        (𝓝[>] 0)
        (𝓝 (∫ z, f z ∂(μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * v z))))) := by
  intro f hf hfc hfD
  obtain ⟨χ, hχ1, hχc, hχD, hχ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hfc hD hfD
  have hχ : Continuous (χ : ℂ → ℝ) := χ.continuous
  have hχ0 : ∀ z, 0 ≤ χ z := fun z => (hχ01 z).1
  have hIntegrate (ρ : Measure ℂ) (φ : ℂ → ℝ) :
      (∫ z, φ z ∂(ρ.withDensity fun z => ENNReal.ofReal (χ z))) = ∫ z, φ z * χ z ∂ρ := by
    have hm : Measurable (fun z => ENNReal.ofReal (χ z)) := ENNReal.measurable_ofReal.comp hχ.measurable
    rw [integral_withDensity_eq_integral_toReal_smul hm (by filter_upwards [] with z; simp) φ]
    congr 1
    funext z
    simp [hχ0 z, mul_comm]
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro u hu
  have hupos : ∀ᶠ n in atTop, 0 < u n := hu.eventually self_mem_nhdsWithin
  let r : ℕ → ℝ := fun n => if 0 < u n then u n else 1
  have hre : ∀ᶠ n in atTop, r n = u n := by
    filter_upwards [hupos] with n hn
    simp [r, hn]
  have hr : Tendsto r atTop (𝓝[>] (0 : ℝ)) := hu.congr' (hre.mono fun _ hn => hn.symm)
  have hrpos (n : ℕ) : 0 < r n := by
    dsimp [r]
    split <;> positivity
  let ν : ℕ → Measure ℂ := fun n => lqgApprox γ h (r n)
  let : IsLocallyFiniteMeasure μ := hμ
  let : ∀ n, IsLocallyFiniteMeasure (ν n) := fun n =>
    isLocallyFiniteMeasure_lqgApprox_of_continuous γ h (r n) (hc (r n) (hrpos n))
  let νχ : ℕ → Measure ℂ := fun n => (ν n).withDensity (fun z => ENNReal.ofReal (χ z))
  let μχ : Measure ℂ := μ.withDensity (fun z => ENNReal.ofReal (χ z))
  let : IsLocallyFiniteMeasure μχ := IsLocallyFiniteMeasure.withDensity_ofReal hχ
  let : ∀ n, IsLocallyFiniteMeasure (νχ n) := fun n =>
    IsLocallyFiniteMeasure.withDensity_ofReal hχ
  let K : Set ℂ := tsupport f
  let g : ℕ → ℂ → ℝ := fun n z => f z * Real.exp (γ * Real.circleAverage v z (r n))
  let g₀ : ℂ → ℝ := fun z => f z * Real.exp (γ * v z)
  have hvague : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ x, φ x ∂(νχ n)) atTop (𝓝 (∫ x, φ x ∂μχ)) := by
    intro φ hφ hφc
    have hsupport : tsupport (fun x => φ x * χ x) ⊆ D :=
      tsupport_mul_subset_right.trans hχD
    have hv := (hall (fun x => φ x * χ x) (hφ.mul hχ) hφc.mul_right hsupport).comp hr
    change Tendsto (fun n => ∫ x, φ x * χ x ∂(ν n)) atTop (𝓝 (∫ x, φ x * χ x ∂μ)) at hv
    simpa only [νχ, μχ, hIntegrate] using hv
  have hg : ∀ n, Integrable (g n) (νχ n) := by
    intro n
    have hav : Continuous (fun z => Real.circleAverage v z (r n)) :=
      (Section6.continuous_circleAverage_radius_center hv).comp (continuous_const.prodMk continuous_id)
    have hgc : Continuous (g n) := hf.mul (Real.continuous_exp.comp (continuous_const.mul hav))
    exact hgc.integrable_of_hasCompactSupport hfc.mul_right
  have huni : TendstoUniformlyOn g g₀ atTop K := by
    let U : Set ℝ := Icc (-1) 1
    have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
    have hcont : Continuous (fun p : ℝ × ℂ => f p.2 * Real.exp (γ * Real.circleAverage v p.2 p.1)) :=
      (hf.comp continuous_snd).mul (Real.continuous_exp.comp
        (continuous_const.mul (Section6.continuous_circleAverage_radius_center hv)))
    have huc : UniformContinuousOn
        (fun p : ℝ × ℂ => f p.2 * Real.exp (γ * Real.circleAverage v p.2 p.1)) (U ×ˢ K) :=
      (isCompact_Icc.prod hfc).uniformContinuousOn_of_continuous hcont.continuousOn
    have ht := huc.tendstoUniformlyOn
      (F := fun q z => f z * Real.exp (γ * Real.circleAverage v z q)) (mem_of_mem_nhds hU)
    have ht' : TendstoUniformlyOn (fun q z => f z * Real.exp (γ * Real.circleAverage v z q))
        g₀ (𝓝 0) K := by
      simpa only [nhdsWithin_eq_nhds.mpr hU, Real.circleAverage_zero, g₀] using ht
    rw [Metric.tendstoUniformlyOn_iff] at ht' ⊢
    intro ε hε
    exact (hr.mono_right nhdsWithin_le_nhds).eventually (ht' ε hε)
  have hoff : ∀ n z, z ∉ K → g n z = g₀ z := by
    intro n z hz
    have hz' : f z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [g, g₀, hz']
  have hlim := Section6.tendsto_integral_of_uniformOn_compact νχ μχ hvague hfc
    (hf.mul (Real.continuous_exp.comp (continuous_const.mul hv))) hfc.mul_right hg huni hoff
  have hχmul (w : ℂ → ℝ) : (fun z => f z * w z * χ z) = fun z => f z * w z := by
    funext z
    by_cases hz : z ∈ K
    · simp [hχ1 hz]
    · have : f z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [this]
  have hχg (n : ℕ) : (∫ z, g n z ∂(νχ n)) = ∫ z, g n z ∂(ν n) := by
    change (∫ z, g n z ∂((ν n).withDensity fun z => ENNReal.ofReal (χ z))) = _
    rw [hIntegrate]
    simp only [g, hχmul]
  have hχg₀ : (∫ z, g₀ z ∂μχ) = ∫ z, g₀ z ∂μ := by
    change (∫ z, g₀ z ∂(μ.withDensity fun z => ENNReal.ofReal (χ z))) = _
    rw [hIntegrate]
    simp only [g₀, hχmul]
  change Tendsto (fun n => ∫ z, g n z ∂(νχ n)) atTop (𝓝 (∫ z, g₀ z ∂μχ)) at hlim
  simp_rw [hχg, hχg₀] at hlim
  have heq (n : ℕ) : (∫ z, f z ∂(lqgApprox γ (addCircleAverage h v) (r n))) =
      ∫ z, g n z ∂(ν n) := by
    rw [Section6.lqgApprox_addCircleAverage γ (r n) (hrpos n).le h (hc (r n) (hrpos n)) v hv]
    exact Section6.integral_withDensity_exp (ν n) γ (fun z => Real.circleAverage v z (r n)) f
      ((Section6.continuous_circleAverage_radius_center hv).comp (continuous_const.prodMk continuous_id))
  rw [Section6.integral_withDensity_exp μ γ v f hv]
  have hlim' : Tendsto (fun n => ∫ z, f z ∂(lqgApprox γ (addCircleAverage h v) (r n)))
      atTop (𝓝 (∫ z, g₀ z ∂μ)) := by simpa only [heq, g₀, Pi.mul_apply, Function.comp_apply] using hlim
  apply hlim'.congr'
  filter_upwards [hre] with n hn
  simp only [Function.comp_apply, hn]


/-- Local Weyl scaling for perturbations continuous on the domain. The test
function is supported in the domain, so the weighted integral only uses the
values of the perturbation there. -/
theorem tendsto_lqgApprox_addCircleAverage_allScale_local {γ : ℝ} {h : ℝ → ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    (hc : ∀ r : ℝ, 0 < r → Continuous (h r))
    (hall : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
      Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ h r))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ)))
    (v : ℂ → ℝ) (hv : ContinuousOn v D)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfD : tsupport f ⊆ D) :
    Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ (addCircleAverage h v) r))
      (𝓝[>] 0) (𝓝 (∫ z, f z * Real.exp (γ * v z) ∂μ)) := by
  obtain ⟨δ, hδ, hδD⟩ := hfc.exists_cthickening_subset_open hD hfD
  let K : Set ℂ := tsupport f
  let S : Set ℂ := Metric.cthickening δ K
  let vS : C(S, ℝ) := ⟨fun z => v z, (hv.mono hδD).domRestrict⟩
  obtain ⟨V, hV⟩ := vS.exists_restrict_eq Metric.isClosed_cthickening
  have hVeq : ∀ z ∈ S, V z = v z := by
    intro z hz
    exact congrArg (fun g : C(S, ℝ) => g ⟨z, hz⟩) hV
  have hVK : ∀ z ∈ K, V z = v z := fun z hz =>
    hVeq z (Metric.self_subset_cthickening K hz)
  have hlim := tendsto_lqgApprox_addCircleAverage_allScale hD hμ hc hall V V.continuous f hf hfc hfD
  rw [Section6.integral_withDensity_exp μ γ V f V.continuous] at hlim
  have htarget : (∫ z, f z * Real.exp (γ * V z) ∂μ) =
      ∫ z, f z * Real.exp (γ * v z) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ K
    · rw [hVK z hz]
    · have hz0 : f z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp only [hz0, zero_mul]
  rw [htarget] at hlim
  apply hlim.congr'
  filter_upwards [(nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0) (Iio_mem_nhds hδ),
    self_mem_nhdsWithin] with r hr hpos
  have havg : ∀ z ∈ K, Real.circleAverage v z r = Real.circleAverage V z r := by
    intro z hz
    apply Real.circleAverage_congr_sphere
    intro w hw
    apply (hVeq w ?_).symm
    apply Metric.mem_cthickening_of_dist_le w z δ K hz
    rw [Metric.mem_sphere] at hw
    rw [hw, abs_of_pos hpos]
    exact hr.le
  have hmeasure : (lqgApprox γ (addCircleAverage h v) r).restrict K =
      (lqgApprox γ (addCircleAverage h V) r).restrict K := by
    simp only [lqgApprox]
    rw [restrict_withDensity (show MeasurableSet K from hfc.isClosed.measurableSet),
      restrict_withDensity (show MeasurableSet K from hfc.isClosed.measurableSet)]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hfc.isClosed.measurableSet] with z hz
    simp only [addCircleAverage, havg z hz]
  calc
    (∫ z, f z ∂(lqgApprox γ (addCircleAverage h V) r)) =
        ∫ z in K, f z ∂(lqgApprox γ (addCircleAverage h V) r) := by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => image_eq_zero_of_notMem_tsupport hz)
    _ = ∫ z in K, f z ∂(lqgApprox γ (addCircleAverage h v) r) := by rw [hmeasure]
    _ = ∫ z, f z ∂(lqgApprox γ (addCircleAverage h v) r) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => image_eq_zero_of_notMem_tsupport hz)


/-- Vague convergence on an open cover glues to convergence for every compactly
supported test whose support is covered. This applies to countable disk covers,
but the deterministic gluing itself does not require countability. -/
theorem tendsto_integral_of_open_cover {ι α : Type*} {F : Filter α}
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (ν : α → Measure ℂ) (μ : Measure ℂ) (hμ : IsLocallyFiniteMeasure μ)
    (hν : ∀ᶠ a in F, IsLocallyFiniteMeasure (ν a))
    (hloc : ∀ (i : ι) (f : ℂ → ℝ), Continuous f → HasCompactSupport f → tsupport f ⊆ U i →
      Tendsto (fun a => ∫ z, f z ∂(ν a)) F (𝓝 (∫ z, f z ∂μ)))
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hcover : tsupport f ⊆ ⋃ i, U i) :
    Tendsto (fun a => ∫ z, f z ∂(ν a)) F (𝓝 (∫ z, f z ∂μ)) := by
  classical
  obtain ⟨I, hI⟩ := hfc.elim_finite_subcover U hU hcover
  let e : Fin (Fintype.card {i // i ∈ I}) ≃ {i // i ∈ I} := (Fintype.equivFin _).symm
  let V : Fin (Fintype.card {i // i ∈ I}) → Set ℂ := fun j => U (e j).1
  have hV : tsupport f ⊆ ⋃ j, V j := by
    intro z hz
    obtain ⟨i, hi, hzU⟩ := mem_iUnion₂.mp (hI hz)
    exact mem_iUnion.mpr ⟨e.symm ⟨i, hi⟩, by simpa [V] using hzU⟩
  obtain ⟨φ, hφsub, hφone, _, _⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact (fun j => hU (e j).1) hfc hV
  let g : Fin (Fintype.card {i // i ∈ I}) → ℂ → ℝ := fun j z => f z * φ j z
  have hgc (j) : Continuous (g j) := hf.mul (φ j).continuous
  have hgs (j) : HasCompactSupport (g j) := hfc.mul_right
  have hgl (j) : tsupport (g j) ⊆ U (e j).1 := tsupport_mul_subset_right.trans (hφsub j)
  have hsum (z : ℂ) : (∑ j, g j z) = f z := by
    simp only [g, ← Finset.mul_sum]
    by_cases hz : z ∈ tsupport f
    · have h := hφone hz
      simp only [Finset.sum_apply, Pi.one_apply] at h
      rw [h, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hint (ρ : Measure ℂ) (hρ : IsLocallyFiniteMeasure ρ) :
      (∫ z, f z ∂ρ) = ∑ j, ∫ z, g j z ∂ρ := by
    let : IsLocallyFiniteMeasure ρ := hρ
    calc
      (∫ z, f z ∂ρ) = ∫ z, ∑ j, g j z ∂ρ := by simp only [hsum]
      _ = ∑ j, ∫ z, g j z ∂ρ :=
        integral_finsetSum _ (fun j _ => (hgc j).integrable_of_hasCompactSupport (hgs j))
  have hlim := tendsto_finsetSum Finset.univ (fun j _ => hloc (e j).1 (g j) (hgc j) (hgs j) (hgl j))
  rw [← hint μ hμ] at hlim
  apply hlim.congr'
  filter_upwards [hν] with a ha
  exact (hint (ν a) ha).symm


/-- Countably many almost-sure local convergence events give one event on which
convergence holds for all compactly supported tests in the covered domain. -/
theorem ae_tendsto_integral_of_countable_open_cover {Ω ι α : Type*}
    [MeasurableSpace Ω] [Countable ι] (P : Measure Ω) {F : Filter α}
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) {D : Set ℂ} (hcover : D ⊆ ⋃ i, U i)
    (ν : Ω → α → Measure ℂ) (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hν : ∀ᵐ ω ∂P, ∀ᶠ a in F, IsLocallyFiniteMeasure (ν ω a))
    (hloc : ∀ i, ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ U i → Tendsto (fun a => ∫ z, f z ∂(ν ω a)) F (𝓝 (∫ z, f z ∂(μ ω)))) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
      Tendsto (fun a => ∫ z, f z ∂(ν ω a)) F (𝓝 (∫ z, f z ∂(μ ω))) := by
  filter_upwards [hμ, hν, ae_all_iff.mpr hloc] with ω hμω hνω hlocω
  intro f hf hfc hfD
  exact tendsto_integral_of_open_cover U hU (ν ω) (μ ω) hμω hνω hlocω f hf hfc
    (hfD.trans hcover)


/-- A valid environment has the random-radius area-scaling identity if each
member of a countable open cover of the punctured plane has an all-scale limit.
The local limits may initially differ: their test integrals are identified
with the environment's dyadic LQG limit by uniqueness of limits. -/
theorem MatedCRTEnv.IsValid.ae_rescaled_measure_eq_of_countable_local_limits
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : γ ≠ 0) (hb : 0 < b) (R : Ω → ℝ) {ν : Ω → Measure ℂ}
    {η' : Ω → ℝ → ℂ}
    (hR : ∀ᵐ ω ∂S.P, 0 < R ω)
    (hν : IsLQGMeasure S.P γ (fun ω => rescaledCircle γ (S.hcirc ω) (R ω) b) ν)
    (hη' : ∀ᵐ ω ∂S.P, IsAreaParametrized (ν ω) (η' ω))
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) (hcover : ({0} : Set ℂ)ᶜ ⊆ ⋃ i, U i)
    (hloc : ∀ i, ∀ᵐ ω ∂S.P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ U i → ∃ l : ℝ,
        Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (S.hcirc ω) ε)) (𝓝[>] 0) (𝓝 l)) :
    ∀ᵐ ω ∂S.P, ν ω = rescaledMeasure (S.μ ω) (R ω) b := by
  have hreg := MatedCRTEnv.IsValid.ae_area_and_circle_regular hS
  have hlocal : ∀ i, ∀ᵐ ω ∂S.P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ U i →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (S.hcirc ω) ε))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂(S.μ ω))) := by
    intro i
    filter_upwards [hS.isLQGMeasure, hloc i] with ω hμω hlocω
    intro f hf hfc hfU
    obtain ⟨l, hl⟩ := hlocω f hf hfc hfU
    have heq : l = ∫ z, f z ∂(S.μ ω) :=
      tendsto_nhds_unique (hl.comp tendsto_dyadicScale_nhdsGT) (hμω.tendsto_integral f hf hfc)
    simpa only [heq] using hl
  have hμ : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) := hreg.mono fun _ h => h.1
  have happrox : ∀ᵐ ω ∂S.P, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      IsLocallyFiniteMeasure (lqgApprox γ (S.hcirc ω) ε) := by
    filter_upwards [hreg] with ω hω
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact isLocallyFiniteMeasure_lqgApprox_of_continuous γ (S.hcirc ω) ε (hω.2.2 ε hε)
  have hall := ae_tendsto_integral_of_countable_open_cover S.P U hU hcover
    (fun ω ε => lqgApprox γ (S.hcirc ω) ε) S.μ hμ happrox hlocal
  exact MatedCRTEnv.IsValid.ae_rescaled_measure_eq_of_off_origin_limit hS hγ hb R hR hν hη' hall


/-- Circle-average approximations with the same values on the support of a test
have the same test integral. -/
theorem integral_lqgApprox_eq_of_eqOn_tsupport (γ r : ℝ) (h₁ h₂ : ℝ → ℂ → ℝ)
    (f : ℂ → ℝ) (hfc : HasCompactSupport f) (heq : EqOn (h₁ r) (h₂ r) (tsupport f)) :
    (∫ z, f z ∂(lqgApprox γ h₁ r)) = ∫ z, f z ∂(lqgApprox γ h₂ r) := by
  have hm : (lqgApprox γ h₁ r).restrict (tsupport f) =
      (lqgApprox γ h₂ r).restrict (tsupport f) := by
    simp only [lqgApprox]
    rw [restrict_withDensity hfc.isClosed.measurableSet, restrict_withDensity hfc.isClosed.measurableSet]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hfc.isClosed.measurableSet] with z hz
    rw [heq hz]
  calc
    (∫ z, f z ∂(lqgApprox γ h₁ r)) = ∫ z in tsupport f, f z ∂(lqgApprox γ h₁ r) := by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => image_eq_zero_of_notMem_tsupport hz)
    _ = ∫ z in tsupport f, f z ∂(lqgApprox γ h₂ r) := by rw [hm]
    _ = ∫ z, f z ∂(lqgApprox γ h₂ r) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => image_eq_zero_of_notMem_tsupport hz)

/-- Local Weyl scaling needs circle-average continuity only on compact subsets
of the domain and only eventually as the regularization radius tends to zero. -/
theorem tendsto_lqgApprox_addCircleAverage_allScale_local_profiles {γ : ℝ} {h : ℝ → ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    (hc : ∀ K : Set ℂ, IsCompact K → K ⊆ D →
      ∀ᶠ r : ℝ in 𝓝[>] 0, ContinuousOn (h r) K)
    (hall : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
      Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ h r))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ)))
    (v : ℂ → ℝ) (hv : ContinuousOn v D)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfD : tsupport f ⊆ D) :
    Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ (addCircleAverage h v) r))
      (𝓝[>] 0) (𝓝 (∫ z, f z * Real.exp (γ * v z) ∂μ)) := by
  classical
  obtain ⟨δ, hδ, hδD⟩ := hfc.exists_cthickening_subset_open hD hfD
  let K : Set ℂ := tsupport f
  let S : Set ℂ := Metric.cthickening δ K
  let W : Set ℂ := Metric.thickening δ K
  have hSW : W ⊆ S := Metric.thickening_subset_cthickening δ K
  have hWS : W ⊆ D := hSW.trans hδD
  have hKW : K ⊆ W := Metric.self_subset_thickening hδ K
  have hext (r : ℝ) (hr : ContinuousOn (h r) S) :
      ∃ H : C(ℂ, ℝ), ∀ z ∈ S, H z = h r z := by
    let hs : C(S, ℝ) := ⟨fun z => h r z, hr.domRestrict⟩
    obtain ⟨H, hH⟩ := hs.exists_restrict_eq Metric.isClosed_cthickening
    exact ⟨H, fun z hz => congrArg (fun g : C(S, ℝ) => g ⟨z, hz⟩) hH⟩
  let H : ℝ → C(ℂ, ℝ) := fun r =>
    if hr : ContinuousOn (h r) S then Classical.choose (hext r hr) else 0
  have hHeq (r : ℝ) (hr : ContinuousOn (h r) S) : ∀ z ∈ S, H r z = h r z := by
    simpa only [H, dite_eq_left hr] using Classical.choose_spec (hext r hr)
  let H' : ℝ → ℂ → ℝ := fun r => H r
  have hHc : ∀ r : ℝ, 0 < r → Continuous (H' r) := fun r _ => (H r).continuous
  have hce : ∀ᶠ r : ℝ in 𝓝[>] 0, ContinuousOn (h r) S := hc S hfc.cthickening hδD
  have hHall : ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ W →
      Tendsto (fun r : ℝ => ∫ z, φ z ∂(lqgApprox γ H' r))
        (𝓝[>] 0) (𝓝 (∫ z, φ z ∂μ)) := by
    intro φ hφ hφc hφW
    apply (hall φ hφ hφc (hφW.trans hWS)).congr'
    filter_upwards [hce] with r hr
    apply integral_lqgApprox_eq_of_eqOn_tsupport γ r h H' φ hφc
    intro z hz
    exact (hHeq r hr z (hSW (hφW hz))).symm
  have hlim := tendsto_lqgApprox_addCircleAverage_allScale_local Metric.isOpen_thickening
    hμ hHc hHall v (hv.mono hWS) f hf hfc hKW
  apply hlim.congr'
  filter_upwards [hce] with r hr
  apply integral_lqgApprox_eq_of_eqOn_tsupport γ r (addCircleAverage H' v) (addCircleAverage h v) f hfc
  intro z hz
  simp only [addCircleAverage, H', hHeq r hr z (hSW (hKW hz))]


/-- Joint continuity on admissible circles supplies the eventual local spatial
continuity required for compactly supported tests in an open domain. -/
theorem eventually_continuousOn_compact_of_admissible_circles {D : Set ℂ}
    (hD : IsOpen D) {h : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2)
      {p | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ D})
    (K : Set ℂ) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ContinuousOn (h r) K := by
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_cthickening_subset_open hD hKD
  filter_upwards [(nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0) (Iio_mem_nhds hδ),
    self_mem_nhdsWithin] with r hr hrpos
  apply hc.comp (continuous_const.prodMk continuous_id).continuousOn
  intro z hz
  refine ⟨hrpos, ?_⟩
  intro w hw
  apply hδD
  apply Metric.mem_cthickening_of_dist_le w z δ K hz
  exact (Metric.mem_closedBall.mp hw).trans hr.le


/-- A local circle-average decomposition transfers all-scale convergence to the
sum, using only admissible-circle continuity of the zero-boundary part. -/
theorem tendsto_lqgApprox_of_local_circle_decomposition {γ : ℝ}
    {h H : ℝ → ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D)
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    (hc : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2)
      {p | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ D})
    (hall : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
      Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ h r))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ)))
    (v : ℂ → ℝ) (hv : ContinuousOn v D)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfD : tsupport f ⊆ D)
    (heq : ∀ᶠ r : ℝ in 𝓝[>] 0,
      EqOn (H r) (addCircleAverage h v r) (tsupport f)) :
    Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ H r))
      (𝓝[>] 0) (𝓝 (∫ z, f z * Real.exp (γ * v z) ∂μ)) := by
  have hc' := eventually_continuousOn_compact_of_admissible_circles hD hc
  have hlim := tendsto_lqgApprox_addCircleAverage_allScale_local_profiles hD hμ hc' hall
    v hv f hf hfc hfD
  apply hlim.congr'
  filter_upwards [heq] with r hr
  exact (integral_lqgApprox_eq_of_eqOn_tsupport γ r H (addCircleAverage h v) f hfc hr).symm


/-- A compact subset of an open domain has all sufficiently small closed
circles contained in the domain. -/
theorem eventually_closedBall_subset_of_isCompact_subset_isOpen {K D : Set ℂ}
    (hK : IsCompact K) (hD : IsOpen D) (hKD : K ⊆ D) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ z ∈ K, Metric.closedBall z r ⊆ D := by
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_cthickening_subset_open hD hKD
  filter_upwards [(nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0) (Iio_mem_nhds hδ)] with r hr
  intro z hz w hw
  apply hδD
  exact Metric.mem_cthickening_of_dist_le w z δ K hz ((Metric.mem_closedBall.mp hw).trans hr.le)

/-- An identity of circle averages on all admissible circles gives the local
all-scale limit for every test supported in the domain. -/
theorem tendsto_lqgApprox_of_admissible_circle_decomposition {γ : ℝ}
    {h H : ℝ → ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D)
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    (hc : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2)
      {p | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ D})
    (hall : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ D →
      Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ h r))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ)))
    (v : ℂ → ℝ) (hv : ContinuousOn v D)
    (hdecomp : ∀ (r : ℝ) (z : ℂ), 0 < r → Metric.closedBall z r ⊆ D →
      H r z = addCircleAverage h v r z)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfD : tsupport f ⊆ D) :
    Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ H r))
      (𝓝[>] 0) (𝓝 (∫ z, f z * Real.exp (γ * v z) ∂μ)) := by
  apply tendsto_lqgApprox_of_local_circle_decomposition hD hμ hc hall v hv f hf hfc hfD
  filter_upwards [eventually_closedBall_subset_of_isCompact_subset_isOpen hfc hD hfD,
    self_mem_nhdsWithin] with r hr hrpos z hz
  exact hdecomp r z hrpos (hr z hz)

/-- Countable local decompositions and all-scale limits for their base fields
imply the random-radius area identity, on the original probability space. -/
theorem MatedCRTEnv.IsValid.ae_rescaled_measure_eq_of_countable_circle_decompositions
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : γ ≠ 0) (hb : 0 < b) (R : Ω → ℝ) {ν : Ω → Measure ℂ}
    {η' : Ω → ℝ → ℂ}
    (hR : ∀ᵐ ω ∂S.P, 0 < R ω)
    (hν : IsLQGMeasure S.P γ (fun ω => rescaledCircle γ (S.hcirc ω) (R ω) b) ν)
    (hη' : ∀ᵐ ω ∂S.P, IsAreaParametrized (ν ω) (η' ω))
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) (hcover : ({0} : Set ℂ)ᶜ ⊆ ⋃ i, U i)
    (hdecomp : ∀ i, ∀ᵐ ω ∂S.P,
      ∃ (h : ℝ → ℂ → ℝ) (v : ℂ → ℝ) (m : Measure ℂ),
        IsLocallyFiniteMeasure m ∧
        ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2)
          {p | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ U i} ∧
        (∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U i →
          Tendsto (fun r : ℝ => ∫ z, f z ∂(lqgApprox γ h r))
            (𝓝[>] 0) (𝓝 (∫ z, f z ∂m))) ∧
        ContinuousOn v (U i) ∧
        (∀ (r : ℝ) (z : ℂ), 0 < r → Metric.closedBall z r ⊆ U i →
          S.hcirc ω r z = addCircleAverage h v r z)) :
    ∀ᵐ ω ∂S.P, ν ω = rescaledMeasure (S.μ ω) (R ω) b := by
  apply MatedCRTEnv.IsValid.ae_rescaled_measure_eq_of_countable_local_limits
    hS hγ hb R hR hν hη' U hU hcover
  intro i
  filter_upwards [hdecomp i] with ω hω
  obtain ⟨h, v, m, hm, hc, hall, hv, heq⟩ := hω
  intro f hf hfc hfU
  exact ⟨∫ z, f z * Real.exp (γ * v z) ∂m,
    tendsto_lqgApprox_of_admissible_circle_decomposition (hU i) hm hc hall v hv heq f hf hfc hfU⟩

end MatedCRT.Sec1
