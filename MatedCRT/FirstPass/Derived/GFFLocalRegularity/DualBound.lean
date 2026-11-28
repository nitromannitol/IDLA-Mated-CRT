import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryVar
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine
import MatedCRT.FirstPass.Derived.LQGMeasureChartSmooth

/-!
# The variance of a zero-boundary Gaussian free field pairing is bounded by an `L^q` norm

For the disc `B(c, r)` and an exponent `1 < q < 2`, the variance of the pairing of the zero-boundary
Gaussian free field with a test function `φ` is at most a constant times `‖φ‖_{L^q}²`.

The standard facts used are:

* the variance formula of the zero-boundary Gaussian free field,
  `Var ⟨h, φ⟩ = sup_f (∫ f φ)² / (f, f)_∇` over test functions `f` with positive Dirichlet energy
  (Sheffield, *Gaussian free fields for mathematicians*, §2);
* Hölder's inequality `‖f φ‖_{L¹} ≤ ‖f‖_{L^{q'}} ‖φ‖_{L^q}` with `1/q + 1/q' = 1`;
* the Sobolev inequality `‖f‖_{L^{q'}} ≤ C ‖∇f‖_{L^p}` for `f ∈ C_c¹(ℝ²)` and `1/q' = 1/p - 1/2`
  (Gilbarg–Trudinger, *Elliptic partial differential equations of second order*, Theorem 7.10;
  in Mathlib, `eLpNorm_le_eLpNorm_fderiv_of_eq`);
* Hölder's inequality on a set of finite measure, `‖g‖_{L^p(B)} ≤ |B|^{1/p - 1/2} ‖g‖_{L²(B)}` for
  `p ≤ 2` (in Mathlib, `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`).
-/

set_option autoImplicit false

open MeasureTheory Metric
open scoped ENNReal NNReal

namespace MatedCRT.GFFLocalRegularity

/-- **Dirichlet-energy bound for the pairing with a test function.** On the disc `B(c, r)`, for
`1 < q < 2` there is a constant `K` such that for every `C¹` function `f` with compact support in
the disc and every `φ ∈ L^q`, `(∫ f φ)² ≤ K · ∫_{B(c, r)} ‖∇f‖² · ‖φ‖_{L^q}²`.
This is Hölder's inequality followed by the Sobolev inequality (Gilbarg–Trudinger, Theorem 7.10)
and Hölder's inequality on the disc. -/
theorem sq_integral_mul_le {c : ℂ} {r : ℝ} {q : ℝ≥0} (hq1 : 1 < q) (hq2 : q < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f φ : ℂ → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      tsupport f ⊆ ball c r → MemLp φ q volume →
      (∫ x, f x * φ x) ^ 2 ≤
        K * (∫ z in ball c r, ‖fderiv ℝ f z‖ ^ 2) * (eLpNorm φ q volume).toReal ^ 2 := by
  have hq1' : (1 : ℝ) < q := by exact_mod_cast hq1
  have hq2' : (q : ℝ) < 2 := by exact_mod_cast hq2
  have hqpos : (0 : ℝ) < q := by linarith
  have ha1 : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1'
  have ha2 : 1 / 2 < (q : ℝ)⁻¹ := by
    rw [one_div]; exact inv_strictAnti₀ hqpos hq2'
  have hpos' : 0 ≤ ((1 - (q : ℝ)⁻¹)⁻¹ : ℝ) := by
    have : 0 < 1 - (q : ℝ)⁻¹ := by linarith
    positivity
  have hpos : 0 ≤ ((3 / 2 - (q : ℝ)⁻¹)⁻¹ : ℝ) := by
    have : 0 < 3 / 2 - (q : ℝ)⁻¹ := by linarith
    positivity
  let p' : ℝ≥0 := ⟨(1 - (q : ℝ)⁻¹)⁻¹, hpos'⟩
  let p : ℝ≥0 := ⟨(3 / 2 - (q : ℝ)⁻¹)⁻¹, hpos⟩
  have hp'inv : (p' : ℝ)⁻¹ = 1 - (q : ℝ)⁻¹ := inv_inv _
  have hpinv : (p : ℝ)⁻¹ = 3 / 2 - (q : ℝ)⁻¹ := inv_inv _
  have hp'0 : p' ≠ 0 := by
    intro h
    have : (p' : ℝ)⁻¹ = 0 := by rw [h]; simp
    rw [hp'inv] at this; linarith
  have hp0 : p ≠ 0 := by
    intro h
    have : (p : ℝ)⁻¹ = 0 := by rw [h]; simp
    rw [hpinv] at this; linarith
  have hq0 : q ≠ 0 := by
    intro h; rw [h] at hq1; simp at hq1
  have hp1 : 1 ≤ p := by
    have hp0' : (0 : ℝ) < p := by exact_mod_cast pos_iff_ne_zero.2 hp0
    have : (p : ℝ)⁻¹ ≤ 1 := by rw [hpinv]; linarith
    have h2 : (1 : ℝ) ≤ p := by
      by_contra hlt
      have := (one_lt_inv₀ hp0').2 (not_le.1 hlt)
      linarith
    exact_mod_cast h2
  have hp2 : (p : ℝ≥0∞) ≤ 2 := by
    have hp0' : (0 : ℝ) < p := by exact_mod_cast pos_iff_ne_zero.2 hp0
    have h2 : (p : ℝ) ≤ 2 := by
      have : (1 / 2 : ℝ) ≤ (p : ℝ)⁻¹ := by rw [hpinv]; linarith
      rw [one_div] at this
      have := (inv_le_inv₀ (by norm_num) hp0').1 this
      exact this
    have h3 : p ≤ 2 := by exact_mod_cast h2
    exact_mod_cast h3
  have hGNS : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - ((Module.finrank ℝ ℂ : ℕ) : ℝ)⁻¹ := by
    rw [Complex.finrank_real_complex, hp'inv, hpinv]; push_cast; ring
  obtain ⟨Cs, hCs⟩ : ∃ Cs : ℝ≥0, ∀ u : ℂ → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u p' volume ≤ Cs * eLpNorm (fderiv ℝ u) p volume :=
    ⟨_, fun u hu h2u => eLpNorm_le_eLpNorm_fderiv_of_eq (volume : Measure ℂ) hu h2u hp1
      (by simp) hGNS⟩
  have hHT : (p' : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ = (1 : ℝ≥0∞)⁻¹ := by
    have : p'⁻¹ + q⁻¹ = (1 : ℝ≥0) := by
      apply NNReal.coe_injective
      push_cast
      rw [hp'inv]; ring
    rw [← ENNReal.coe_inv hp'0, ← ENNReal.coe_inv hq0, ← ENNReal.coe_add, this]; simp
  have : ENNReal.HolderTriple (p' : ℝ≥0∞) (q : ℝ≥0∞) 1 := ⟨hHT⟩
  have hexp : 0 ≤ 1 / (p : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal := by
    have : (p : ℝ) ≤ 2 := by
      have := ENNReal.toReal_mono (by simp) hp2
      simpa using this
    have hp0' : (0 : ℝ) < p := by exact_mod_cast pos_iff_ne_zero.2 hp0
    simp only [ENNReal.coe_toReal, ENNReal.toReal_ofNat]
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hp0' this
  set Vb : ℝ≥0∞ := volume (ball c r) ^ (1 / (p : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) with hVb
  have hVbtop : Vb ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hexp measure_ball_lt_top.ne
  refine ⟨((Cs : ℝ) * Vb.toReal) ^ 2, by positivity, ?_⟩
  intro f φ hf hfc hfs hφ
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hfdc : HasCompactSupport (fderiv ℝ f) := hfc.fderiv ℝ
  have hfdmem : ∀ s : ℝ≥0∞, MemLp (fderiv ℝ f) s volume := fun s =>
    hfd.memLp_of_hasCompactSupport hfdc
  have hsupp : Function.support (fderiv ℝ f) ⊆ ball c r := (support_fderiv_subset ℝ).trans hfs
  have hA : (eLpNorm (fderiv ℝ f) 2 volume).toReal ^ 2 = ∫ z in ball c r, ‖fderiv ℝ f z‖ ^ 2 := by
    have h := (hfdmem 2).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    have hnn : 0 ≤ ∫ z, ‖fderiv ℝ f z‖ ^ (2 : ℝ≥0∞).toReal := integral_nonneg fun _ => by positivity
    rw [h, ENNReal.toReal_ofReal (by positivity)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hnn ⊢
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
    norm_num
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
    have : fderiv ℝ f z = 0 := by
      by_contra h0
      exact hz (hsupp h0)
    simp [this]
  have hmeas : AEStronglyMeasurable (fun x => f x * φ x) volume :=
    hf.continuous.aestronglyMeasurable.mul hφ.aestronglyMeasurable
  have h1 : eLpNorm (fun x => f x * φ x) 1 volume ≤ eLpNorm f p' volume * eLpNorm φ q volume := by
    have := eLpNorm_smul_le_mul_eLpNorm (p := (p' : ℝ≥0∞)) (q := (q : ℝ≥0∞)) (r := 1)
      (μ := volume) hf.continuous.aestronglyMeasurable hφ.aestronglyMeasurable
    exact this
  have h2 : eLpNorm (fderiv ℝ f) p volume ≤ eLpNorm (fderiv ℝ f) 2 volume * Vb := by
    have ep := eLpNorm_restrict_eq_of_support_subset (p := (p : ℝ≥0∞)) (μ := volume)
      hfd.aestronglyMeasurable hsupp
    have e2 := eLpNorm_restrict_eq_of_support_subset (p := (2 : ℝ≥0∞)) (μ := volume)
      hfd.aestronglyMeasurable hsupp
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (ball c r))
      (p := (p : ℝ≥0∞)) (q := 2) hp2 hfd.aestronglyMeasurable
    rw [ep, e2, Measure.restrict_apply_univ] at this
    exact this
  have hN : eLpNorm φ q volume ≠ ∞ := hφ.eLpNorm_lt_top.ne
  have hA' : eLpNorm (fderiv ℝ f) 2 volume ≠ ∞ := (hfdmem 2).eLpNorm_lt_top.ne
  have hchain : eLpNorm (fun x => f x * φ x) 1 volume ≤
      (Cs : ℝ≥0∞) * (eLpNorm (fderiv ℝ f) 2 volume * Vb) * eLpNorm φ q volume := by
    calc _ ≤ _ := h1
      _ ≤ ((Cs : ℝ≥0∞) * eLpNorm (fderiv ℝ f) p volume) * eLpNorm φ q volume := by
        gcongr; exact hCs f hf hfc
      _ ≤ _ := by gcongr
  have htop : (Cs : ℝ≥0∞) * (eLpNorm (fderiv ℝ f) 2 volume * Vb) * eLpNorm φ q volume ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top hA' hVbtop)) hN
  have hreal : |∫ x, f x * φ x| ≤
      Cs * ((eLpNorm (fderiv ℝ f) 2 volume).toReal * Vb.toReal) * (eLpNorm φ q volume).toReal := by
    calc |∫ x, f x * φ x| = ‖∫ x, f x * φ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, ‖f x * φ x‖ := norm_integral_le_integral_norm _
      _ = (∫⁻ x, ‖f x * φ x‖ₑ).toReal := integral_norm_eq_lintegral_enorm hmeas
      _ = (eLpNorm (fun x => f x * φ x) 1 volume).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm]; exact hmeas
      _ ≤ ((Cs : ℝ≥0∞) * (eLpNorm (fderiv ℝ f) 2 volume * Vb) * eLpNorm φ q volume).toReal :=
        ENNReal.toReal_mono htop hchain
      _ = _ := by simp [ENNReal.toReal_mul]
  calc (∫ x, f x * φ x) ^ 2 = |∫ x, f x * φ x| ^ 2 := (sq_abs _).symm
    _ ≤ (Cs * ((eLpNorm (fderiv ℝ f) 2 volume).toReal * Vb.toReal) *
        (eLpNorm φ q volume).toReal) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hreal 2
    _ = ((Cs * Vb.toReal) ^ 2) * (eLpNorm (fderiv ℝ f) 2 volume).toReal ^ 2 *
        (eLpNorm φ q volume).toReal ^ 2 := by ring
    _ = _ := by rw [hA]

/-- **The `L^q` bound for the variance of a zero-boundary Gaussian free field pairing.** For the
disc `B(c, r)` and `1 < q < 2` there is a constant `C` such that for every test function `φ` supported
in the disc, `Var ⟨h, φ⟩ = zeroGFFTestCov φ φ ≤ C ‖φ‖_{L^q}²`. The proof bounds each term
`(∫ f φ)² / (f, f)_∇` of the variance formula (Sheffield, §2) by `sq_integral_mul_le`. -/
theorem zeroGFFTestCov_self_le_eLpNorm {c : ℂ} {r : ℝ} (_hr : 0 < r) {q : ℝ≥0} (hq1 : 1 < q)
    (hq2 : q < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : LQGMetric.TestOn (MatedCRT.LQGMeasureChart.disc c r),
      QuantumZipper.zeroGFFTestCov (MatedCRT.LQGMeasureChart.disc c r) φ φ ≤
        C * (eLpNorm (φ : ℂ → ℝ) q volume).toReal ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := sq_integral_mul_le (c := c) (r := r) hq1 hq2
  refine ⟨2 * Real.pi * K, by positivity, fun φ => ?_⟩
  have hadm : LQGMetric.ZBAdmissible (MatedCRT.LQGMeasureChart.disc c r) :=
    LQGMetric.zbAdmissible_of_isBounded (by
      change Bornology.IsBounded (ball c r)
      exact Metric.isBounded_ball)
  have hφ : MemLp (φ : ℂ → ℝ) q volume :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
    LQGMetric.ofReal_zeroGFFTestCov_self hadm φ]
  refine iSup₂_le fun f hf => ?_
  obtain ⟨⟨hfs, hfc, hft⟩, hE⟩ := hf
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ hE]
  have h := hK f φ (hfs.of_le (by exact_mod_cast le_top)) hfc hft hφ
  have hI : QuantumZipper.dirichletEnergyOn (MatedCRT.LQGMeasureChart.disc c r : Set ℂ) f =
      (2 * Real.pi)⁻¹ * ∫ z in ball c r, ‖fderiv ℝ f z‖ ^ 2 := rfl
  rw [hI]
  refine h.trans (le_of_eq ?_)
  field_simp

end MatedCRT.GFFLocalRegularity
