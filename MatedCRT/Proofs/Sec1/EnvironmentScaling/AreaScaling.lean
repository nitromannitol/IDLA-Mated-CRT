import MatedCRT.Defs.Setting
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime
import HarmonicBalls.Proofs.Sec9.LQGSpatialDilation

/-!
# Area measure at a random radius

Deterministic parts of `env-steps.tex`, Lemma `area-scale`, lines 693–747.
The radius-change limit below is an explicit hypothesis, not a consequence of
dyadic convergence. This global radius-change limit is stronger than the
off-origin convergence used in the written proof: that proof instead extends
the equality of the two limiting measures across the origin. The result here
therefore does not discharge that proof's remaining convergence step.
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

end MatedCRT.Sec1
