import MatedCRT.FirstPass.Derived.GFFLocalRegularity.DualBound
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGaussLim
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# The pairing with a zero-boundary Gaussian free field extends to `L^q`

For the disc `B(c, r)` and `1 < q < 2`, the map `φ ↦ ⟨h, φ⟩` from the test functions on the disc to
`L²(P)` is bounded for the `L^q` norm of `φ` (`zeroGFFTestCov_self_le_eLpNorm`), so it extends to a
bounded linear map `L^q(B(c, r)) → L²(P)` whose values are centred Gaussian variables.

The standard facts used are:

* the bounded linear transformation theorem: a bounded linear map on a dense subspace of a normed
  space with values in a Banach space extends to a bounded linear map (Reed–Simon, *Methods of
  modern mathematical physics I*, Theorem I.7; in Mathlib, `LinearMap.extendOfNorm`);
* the density of `C_c^∞(Ω)` in `L^p(Ω)` for an open set `Ω` and `1 ≤ p < ∞` (Brezis, *Functional
  analysis, Sobolev spaces and partial differential equations*, Corollary 4.23; in Mathlib the
  density of smooth compactly supported functions in `L^p(ℝⁿ)` is
  `MeasureTheory.MemLp.exist_eLpNorm_sub_le`, which is localised here by a smooth cut-off);
* the closure of centred Gaussian variables under limits in probability (Janson, *Gaussian Hilbert
  spaces*, Theorem 1.4; the argument by characteristic functions is
  `LQGMetric.exists_gaussianReal_of_ae_tendsto`), together with the passage from convergence in
  `L²` to almost sure convergence of a subsequence.
-/

set_option autoImplicit false

/-- Infinite differentiability, as a `WithTop ℕ∞` smoothness order. -/
local notation "𝒞∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace MatedCRT.GFFLocalRegularity

section Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A limit in `L²(P)` of centred real Gaussian variables is a centred real Gaussian variable. -/
theorem exists_hasLaw_gaussianReal_of_tendsto_lp {G : ℕ → Lp ℝ 2 P} {Z : Lp ℝ 2 P}
    (hG : ∀ n, ∃ v : ℝ≥0, HasLaw (G n : Ω → ℝ) (gaussianReal 0 v) P)
    (hlim : Tendsto G atTop (𝓝 Z)) : ∃ v : ℝ≥0, HasLaw (Z : Ω → ℝ) (gaussianReal 0 v) P := by
  choose v hv using hG
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  obtain ⟨V, -, hV⟩ := LQGMetric.exists_gaussianReal_of_ae_tendsto
    (Y := fun k => (G (ns k) : Ω → ℝ)) (Z := (Z : Ω → ℝ)) (v := fun k => v (ns k))
    (fun k => (hv _).aemeasurable) (Lp.aestronglyMeasurable Z).aemeasurable
    (fun k => (hv _).map_eq) hae
  exact ⟨V, ⟨(Lp.aestronglyMeasurable Z).aemeasurable, hV⟩⟩

end Gaussian

section Density

/-- **Density of smooth functions supported in a disc.** Every function in `L^q(B(c, r))`,
`1 ≤ q < ∞`, is the limit in `L^q(B(c, r))` of smooth functions with compact support in `B(c, r)`. -/
theorem exists_smooth_approx {c : ℂ} {r : ℝ} (hr : 0 < r) {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hqt : q ≠ ∞)
    {F : ℂ → ℝ} (hF : MemLp F q (volume.restrict (ball c r))) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℝ, ContDiff ℝ 𝒞∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ ball c r ∧
      eLpNorm (F - g) q (volume.restrict (ball c r)) ≤ ENNReal.ofReal ε := by
  set μ : Measure ℂ := volume.restrict (ball c r) with hμ
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, hδF⟩ := hF.eLpNorm_indicator_le hq1 hqt (ε := ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.2 hε2)
  -- a compact set `K` in the disc carries all but `δ` of its measure
  obtain ⟨K, hKsub, hKc, hK⟩ := (measurableSet_ball (x := c) (ε := r)).exists_isCompact_lt_add
    (μ := volume) measure_ball_lt_top.ne hδ.ne'
  obtain ⟨ρ, hρ, hKρ⟩ := exists_pos_lt_subset_ball hr hKc.isClosed hKsub
  have hann : volume (ball c r \ ball c ρ) ≤ δ := by
    have h1 : volume (ball c ρ) ≠ ∞ := measure_ball_lt_top.ne
    rw [measure_sdiff (ball_subset_ball hρ.2.le) measurableSet_ball.nullMeasurableSet h1,
      tsub_le_iff_right]
    exact (hK.le.trans (add_le_add_left (measure_mono hKρ) _)).trans_eq (add_comm _ _)
  have hAδ : eLpNorm ((ball c r \ ball c ρ).indicator F) q μ ≤ ENNReal.ofReal (ε / 2) :=
    hδF _ (measurableSet_ball.diff measurableSet_ball)
      ((Measure.le_iff'.1 Measure.restrict_le_self _).trans hann)
  obtain ⟨g0, hg0c, hg0, hg0F⟩ := hF.exist_eLpNorm_sub_le hqt hq1 hε2
  let χ : ContDiffBump c := ⟨ρ, (ρ + r) / 2, hρ.1, by linarith [hρ.2]⟩
  have hχr : closedBall c χ.rOut ⊆ ball c r :=
    closedBall_subset_ball (by show (ρ + r) / 2 < r; linarith [hρ.2])
  refine ⟨fun x => χ x * g0 x, χ.contDiff.mul hg0, hg0c.mul_left, ?_, ?_⟩
  · exact (tsupport_mul_subset_left (f := ⇑χ) (g := g0)).trans (χ.tsupport_eq ▸ hχr)
  have hsplit : F - (fun x => χ x * g0 x) =
      (fun x => (1 - χ x) * F x) + (fun x => χ x * (F x - g0 x)) := by
    ext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [hsplit]
  have hm1 : AEStronglyMeasurable (fun x => (1 - χ x) * F x) μ :=
    (continuous_const.sub χ.continuous).aestronglyMeasurable.mul hF.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x => χ x * (F x - g0 x)) μ :=
    χ.continuous.aestronglyMeasurable.mul
      (hF.aestronglyMeasurable.sub hg0.continuous.aestronglyMeasurable)
  refine (eLpNorm_add_le hq1).trans ?_
  have e1 : eLpNorm (fun x => (1 - χ x) * F x) q μ ≤ ENNReal.ofReal (ε / 2) := by
    refine le_trans (eLpNorm_mono_ae hm1 ?_) hAδ
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    by_cases hxρ : x ∈ ball c ρ
    · have : χ x = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hxρ)
      simp [this]
    · have hxA : x ∈ ball c r \ ball c ρ := ⟨hx, hxρ⟩
      rw [Set.indicator_of_mem hxA]
      have h1 : ‖1 - χ x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [χ.nonneg' x, χ.le_one (x := x)]
      calc ‖(1 - χ x) * F x‖ = ‖1 - χ x‖ * ‖F x‖ := norm_mul _ _
        _ ≤ 1 * ‖F x‖ := by gcongr
        _ = ‖F x‖ := one_mul _
  have e2 : eLpNorm (fun x => χ x * (F x - g0 x)) q μ ≤ ENNReal.ofReal (ε / 2) := by
    refine le_trans (eLpNorm_mono_ae (g := F - g0) hm2 (Eventually.of_forall fun x => ?_)) hg0F
    have h1 : ‖χ x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (χ.nonneg' x)]; exact χ.le_one
    calc ‖χ x * (F x - g0 x)‖ = ‖χ x‖ * ‖F x - g0 x‖ := norm_mul _ _
      _ ≤ 1 * ‖F x - g0 x‖ := by gcongr
      _ = ‖(F - g0) x‖ := one_mul _
  calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add e1 e2
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hε2.le hε2.le]; congr 1; ring

end Density

section Extension

/-- The `L²` norm squared of a square-integrable function is the integral of its square. -/
theorem sq_toReal_eLpNorm_two {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  have h := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hnn : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ≥0∞).toReal ∂μ := integral_nonneg fun _ => by positivity
  rw [h, ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hnn ⊢
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

/-- A function equal to the sum of two functions in `L^p` has `toLp` equal to the sum. -/
theorem toLp_eq_add {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f g k : α → ℝ} (hf : MemLp f p μ) (hg : MemLp g p μ) (hk : MemLp k p μ)
    (h : ∀ x, k x = f x + g x) : hk.toLp k = hf.toLp f + hg.toLp g := by
  have : k = f + g := funext h
  rw [MemLp.toLp_congr hk (hf.add hg) (Eventually.of_forall h), MemLp.toLp_add]

/-- A function equal to a scalar multiple of a function in `L^p` has `toLp` equal to the multiple. -/
theorem toLp_eq_smul {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f k : α → ℝ} (a : ℝ) (hf : MemLp f p μ) (hk : MemLp k p μ)
    (h : ∀ x, k x = a * f x) : hk.toLp k = a • hf.toLp f := by
  rw [← MemLp.toLp_const_smul a hf]
  exact MemLp.toLp_congr hk _ (Eventually.of_forall h)

/-- **The pairing with the zero-boundary Gaussian free field extends to `L^q`.** On the disc
`B(c, r)`, for `1 < q < 2`, the map sending a test function `φ` to the random variable `⟨h, φ⟩` extends
to a bounded linear map from `L^q(B(c, r))` to `L²(P)`, and every image is a centred Gaussian.
The instance `Fact (1 ≤ q)` is the usual one that makes `L^q` a normed space; it follows from `hq1`. -/
theorem exists_lpExtension {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {c : ℂ} {r : ℝ} (hr : 0 < r) {q : ℝ≥0}
    [Fact (1 ≤ (q : ℝ≥0∞))] (hq1 : 1 < q) (hq2 : q < 2)
    {h : Ω → LQGMetric.DistOn (MatedCRT.LQGMeasureChart.disc c r)}
    (hh : LQGMetric.IsZeroBoundaryGFF (MatedCRT.LQGMeasureChart.disc c r) h P) :
    ∃ T : Lp ℝ q (volume.restrict (Metric.ball c r)) →L[ℝ] Lp ℝ 2 P,
      (∀ φ : LQGMetric.TestOn (MatedCRT.LQGMeasureChart.disc c r),
        ∀ hφ : MemLp (φ : ℂ → ℝ) q (volume.restrict (Metric.ball c r)),
          ((T (hφ.toLp _) : Ω → ℝ)) =ᵐ[P] fun ω => h ω φ) ∧
      ∀ f, ∃ v : ℝ≥0, HasLaw (T f : Ω → ℝ) (gaussianReal 0 v) P := by
  have hq1' : 1 ≤ (q : ℝ≥0∞) := by exact_mod_cast hq1.le
  have hqt : (q : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  set μ : Measure ℂ := volume.restrict (ball c r) with hμ
  obtain ⟨C, hC0, hC⟩ := zeroGFFTestCov_self_le_eLpNorm (c := c) hr hq1 hq2
  have hmemφ : ∀ φ : LQGMetric.TestOn (LQGMeasureChart.disc c r),
      MemLp (φ : ℂ → ℝ) q μ := fun φ =>
    (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).restrict _
  have hmemX : ∀ φ : LQGMetric.TestOn (LQGMeasureChart.disc c r),
      MemLp (fun ω => h ω φ) 2 P := fun φ =>
    (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two
  let ι : LQGMetric.TestOn (LQGMeasureChart.disc c r) →ₗ[ℝ] Lp ℝ q μ :=
    { toFun := fun φ => (hmemφ φ).toLp _
      map_add' := fun φ ψ => toLp_eq_add (hmemφ φ) (hmemφ ψ) (hmemφ (φ + ψ)) fun x => rfl
      map_smul' := fun a φ => toLp_eq_smul a (hmemφ φ) (hmemφ (a • φ)) fun x => rfl }
  let Φ : LQGMetric.TestOn (LQGMeasureChart.disc c r) →ₗ[ℝ] Lp ℝ 2 P :=
    { toFun := fun φ => (hmemX φ).toLp _
      map_add' := fun φ ψ => toLp_eq_add (hmemX φ) (hmemX ψ) (hmemX (φ + ψ)) fun ω => by
        simp
      map_smul' := fun a φ => toLp_eq_smul a (hmemX φ) (hmemX (a • φ)) fun ω => by simp }
  have hdense : DenseRange ι := by
    rw [Metric.denseRange_iff]
    intro f ε hε
    obtain ⟨g, hg1, hg2, hg3, hg4⟩ := exists_smooth_approx hr hq1' hqt (Lp.memLp f)
      (ε := ε / 2) (by positivity)
    refine ⟨⟨g, hg1, hg2, hg3⟩, ?_⟩
    rw [dist_eq_norm, Lp.norm_def]
    have : eLpNorm (⇑(f - ι ⟨g, hg1, hg2, hg3⟩)) q μ ≤ ENNReal.ofReal (ε / 2) := by
      refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) hg4
      filter_upwards [Lp.coeFn_sub f (ι ⟨g, hg1, hg2, hg3⟩),
        MemLp.coeFn_toLp (hmemφ ⟨g, hg1, hg2, hg3⟩)] with x h1 h2
      rw [h1, Pi.sub_apply]
      exact congrArg _ h2
    have := ENNReal.toReal_le_of_le_ofReal (by positivity) this
    linarith
  have hbound : ∀ φ : LQGMetric.TestOn (LQGMeasureChart.disc c r), ‖Φ φ‖ ≤ Real.sqrt C * ‖ι φ‖ := by
    intro φ
    have hsupp : Function.support (φ : ℂ → ℝ) ⊆ ball c r :=
      (subset_tsupport _).trans φ.tsupport_subset
    have hnorm : ‖ι φ‖ = (eLpNorm (φ : ℂ → ℝ) q volume).toReal := by
      show ‖(hmemφ φ).toLp _‖ = _
      rw [Lp.norm_toLp, hμ, eLpNorm_restrict_eq_of_support_subset
        φ.continuous.aestronglyMeasurable hsupp]
    have hX := hmemX φ
    have hsq : ‖Φ φ‖ ^ 2 = QuantumZipper.zeroGFFTestCov (LQGMeasureChart.disc c r) φ φ := by
      show ‖hX.toLp _‖ ^ 2 = _
      have hcov := hh.process.covariance_eq φ φ
      rw [Lp.norm_toLp, sq_toReal_eLpNorm_two hX, ← hcov,
        covariance_self (hh.process.gaussian.aemeasurable φ),
        variance_of_integral_eq_zero (hh.process.gaussian.aemeasurable φ)
          (hh.process.centered φ)]
    rw [hnorm]
    have hsq' : ‖Φ φ‖ ^ 2 ≤ (Real.sqrt C * (eLpNorm (φ : ℂ → ℝ) q volume).toReal) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC0, hsq]
      exact hC φ
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq' (by positivity))
  have hT : ∀ φ, Φ.extendOfNorm ι (ι φ) = Φ φ := fun φ =>
    LinearMap.extendOfNorm_eq hdense ⟨Real.sqrt C, hbound⟩ φ
  have hgauss : ∀ φ : LQGMetric.TestOn (LQGMeasureChart.disc c r), ∃ v : ℝ≥0, HasLaw (Φ φ : Ω → ℝ) (gaussianReal 0 v) P := by
    intro φ
    have hX := hh.process.gaussian.hasGaussianLaw_eval φ
    refine ⟨Var[fun ω => h ω φ; P].toNNReal, ?_⟩
    have hmap := hX.map_eq_gaussianReal
    rw [hh.process.centered φ] at hmap
    exact ({ aemeasurable := hh.process.gaussian.aemeasurable φ, map_eq := hmap } :
      HasLaw (fun ω => h ω φ) _ P).congr (MemLp.coeFn_toLp (hmemX φ))
  refine ⟨Φ.extendOfNorm ι, fun φ hφ => ?_, fun f => ?_⟩
  · have e : hφ.toLp _ = ι φ := rfl
    rw [e, hT φ]
    exact MemLp.coeFn_toLp (hmemX φ)
  · have hf : f ∈ closure (Set.range ι) := by rw [hdense.closure_range]; trivial
    obtain ⟨x, hx, hxf⟩ := mem_closure_iff_seq_limit.1 hf
    choose φ hφ using hx
    refine exists_hasLaw_gaussianReal_of_tendsto_lp (G := fun n => Φ (φ n))
      (fun n => hgauss _) ?_
    refine (((Φ.extendOfNorm ι).continuous.tendsto f).comp hxf).congr fun n => ?_
    simp only [Function.comp, ← hφ n, hT]

end Extension

end MatedCRT.GFFLocalRegularity
