import MatedCRT.FirstPass.Derived.LQGMeasureChartInputs
import MatedCRT.FirstPass.Derived.GFFLocalRegularity.LpExtension
import MatedCRT.FirstPass.Derived.GFFLocalRegularity.HolderVersion
import MatedCRT.FirstPass.Derived.GFFLocalRegularity.IdentityFixed
import MatedCRT.FirstPass.Derived.GFFLocalRegularity.IdentityAll
import MatedCRT.FirstPass.Derived.GFFLocalRegularity.RescaledTest

/-!
# The local negative regularity of the zero-boundary GFF on a disc

This file proves `MatedCRT.ZeroBoundaryGFFLocalRegularity` (`zeroBoundaryGFFLocalRegularity`): for a zero-boundary
Gaussian free field `h` on a disc `D`, almost surely, for every `α < 0` and every compact `K ⊆ D`, the pairings of
`h` with the rescaled test functions `t⁻² η((· − x)/t)`, `x ∈ K`, `t` small, `η` smooth with `|η|, ‖Dη‖ ≤ 1` and
support in the unit disc, are at most `C t^α`. The printed source of the statement is De Nitti–Schweiger,
arXiv:2301.13781v4, Proposition 2.1 (local Besov regularity of the Gaussian free field), in its test-function form.

The proof writes the pairing through the gradient of the Newton potential of `h`. For `1 < q < 2` the pairing
`φ ↦ ⟨h, φ⟩` extends to a bounded map `T : L^q(D) → L²(P)` (`exists_lpExtension`, from Hölder's inequality and the
Sobolev inequality, Gilbarg–Trudinger, Theorem 7.10). With `kᵢ(x, y) = (2π)⁻¹ (y − x)ᵢ / |y − x|²`, Green's
representation formula (Gilbarg–Trudinger, (2.17)) gives `v = ∑ᵢ ∫ ∂ᵢ v(x) kᵢ(x, ·) dx` for a test function `v`, so
`⟨h, v⟩ = ∑ᵢ ∫ Xᵢ(x) ∂ᵢ v(x) dx` with the Gaussian field `Xᵢ(x) = T(kᵢ(x, ·))`. Its increments have variance at most
`C |x − x'|^{2θ}`, `θ = 2/q − 1`, so by the Kolmogorov–Chentsov theorem (as printed in Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, proof of Proposition 3.1) it has a version `Y` that is `β`-Hölder on compacts
for every `β < θ`. The identity holds almost surely for all test functions at once (`ae_forall_eq_sum_integral`),
and since `∫ ∇v = 0`, `|⟨h, v⟩| ≤ 2 π [Y]_β t^{β − 1}` for `v` at scale `t` (`abs_sum_integral_mul_fderiv_le`).
Taking `q` close to `1` gives every `β < 1`, hence every `α < 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped NNReal ENNReal

namespace MatedCRT.GFFLocalRegularity

/-- The exponent `q = 1 + 1/(m + 2) ∈ (1, 2)`. -/
def qSeq (m : ℕ) : ℝ≥0 := 1 + (m + 2 : ℝ≥0)⁻¹

lemma one_lt_qSeq (m : ℕ) : 1 < qSeq m := by
  unfold qSeq
  have : (0 : ℝ≥0) < (m + 2 : ℝ≥0)⁻¹ := inv_pos.2 (by positivity)
  exact lt_add_of_pos_right 1 this

lemma qSeq_lt_two (m : ℕ) : qSeq m < 2 := by
  unfold qSeq
  have h1 : (m + 2 : ℝ≥0)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by positivity)]
    have h0 : (0 : ℝ≥0) ≤ m := Nat.cast_nonneg m
    calc (1 : ℝ≥0) < 2 := by norm_num
      _ ≤ m + 2 := le_add_of_nonneg_left h0
  calc 1 + (m + 2 : ℝ≥0)⁻¹ < 1 + 1 := by gcongr
    _ = 2 := by norm_num

instance fact_one_le_qSeq (m : ℕ) : Fact (1 ≤ ((qSeq m : ℝ≥0) : ℝ≥0∞)) :=
  ⟨by exact_mod_cast (one_lt_qSeq m).le⟩

/-- The Hölder exponent `2/q − 1` at `q = qSeq m` tends to `1`. -/
lemma tendsto_two_div_qSeq_sub_one : Tendsto (fun m : ℕ => (2 : ℝ) / (qSeq m : ℝ) - 1) atTop (nhds 1) := by
  have hq : Tendsto (fun m : ℕ => ((qSeq m : ℝ≥0) : ℝ)) atTop (nhds 1) := by
    have h0 : Tendsto (fun m : ℕ => ((m : ℝ) + 2)⁻¹) atTop (nhds 0) :=
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    have : (fun m : ℕ => ((qSeq m : ℝ≥0) : ℝ)) = fun m : ℕ => 1 + ((m : ℝ) + 2)⁻¹ := by
      funext m
      simp [qSeq]
    rw [this]
    simpa using h0.const_add 1
  have h2 : Tendsto (fun m : ℕ => (2 : ℝ) / (qSeq m : ℝ)) atTop (nhds (2 / 1)) :=
    tendsto_const_nhds.div hq one_ne_zero
  have := h2.sub_const 1
  norm_num at this
  exact this

/-- A function that is `β`-Hölder on every compact set, `β > 0`, is continuous. -/
lemma continuous_of_forall_holderOnWith {f : ℂ → ℝ} {β : ℝ≥0} (hβ : 0 < β)
    (hf : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0, HolderOnWith C β f K) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨C, hC⟩ := hf (closedBall x 1) (isCompact_closedBall x 1)
  exact (hC.continuousOn hβ).continuousAt (closedBall_mem_nhds x one_pos)

/-- The integral of the square of an element of `L²(P)` is its squared norm. -/
lemma integral_sq_coeFn_eq_norm_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (f : Lp ℝ 2 P) :
    ∫ ω, (f ω) ^ 2 ∂P = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- **The Hölder field of a zero-boundary GFF for one exponent `q`.** For `1 < q < 2` there is a field
`Y = (Y₀, Y₁)`, `β`-Hölder on every compact set for every `β < 2/q − 1` and every `ω`, such that almost surely
`⟨h, φ⟩ = ∑ᵢ ∫ Yᵢ ∂_{eᵢ} φ` for every test function `φ` on the disc. -/
theorem exists_holderField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {c : ℂ} {r : ℝ} (hr : 0 < r) {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))] (hq1 : 1 < q) (hq2 : q < 2)
    {h : Ω → LQGMetric.DistOn (MatedCRT.LQGMeasureChart.disc c r)}
    (hh : LQGMetric.IsZeroBoundaryGFF (MatedCRT.LQGMeasureChart.disc c r) h P) :
    ∃ Y : Fin 2 → ℂ → Ω → ℝ,
      (∀ i ω, ∀ β : ℝ≥0, (β : ℝ) < 2 / q - 1 → ∀ K : Set ℂ, IsCompact K →
        ∃ C : ℝ≥0, HolderOnWith C β (fun x => Y i x ω) K) ∧
      ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestOn (MatedCRT.LQGMeasureChart.disc c r),
        h ω φ = ∑ i : Fin 2, ∫ x, Y i x ω * fderiv ℝ φ x (basis i) := by
  obtain ⟨T, hTφ, hTg⟩ := exists_lpExtension hr hq1 hq2 hh
  obtain ⟨C, hC0, hCb⟩ := eLpNorm_newtonGrad_sub_le hq1 hq2
  set θ : ℝ := 2 / q - 1 with hθ
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one (by exact_mod_cast hq1)
  have hθ0 : 0 < θ := by
    have h2 : (q : ℝ) < 2 := by exact_mod_cast hq2
    rw [hθ, sub_pos, lt_div_iff₀ hq0]
    linarith
  set K : Fin 2 → ℂ → Lp ℝ q (volume.restrict (ball c r)) := fun i x => newtonGradLp (c := c) (r := r) hq1 hq2 i x with hK
  have hKdist : ∀ i x y, ‖K i x - K i y‖ ≤ C * ‖x - y‖ ^ θ := by
    intro i x y
    have hae : ⇑(K i x - K i y) =ᵐ[volume.restrict (ball c r)] fun z => newtonGrad i x z - newtonGrad i y z := by
      filter_upwards [Lp.coeFn_sub (K i x) (K i y),
        (memLp_newtonGrad (c := c) (r := r) hq1 hq2 i x).coeFn_toLp,
        (memLp_newtonGrad (c := c) (r := r) hq1 hq2 i y).coeFn_toLp] with z h1 h2 h3
      rw [h1, Pi.sub_apply]
      simp only [hK, newtonGradLp] at h2 h3 ⊢
      rw [h2, h3]
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    have hle := (eLpNorm_mono_measure (fun z => newtonGrad i x z - newtonGrad i y z)
      (Measure.restrict_le_self (s := ball c r) (μ := volume))).trans (hCb i x y)
    have hpos : 0 ≤ C * ‖x - y‖ ^ θ := mul_nonneg hC0 (Real.rpow_nonneg (norm_nonneg _) _)
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
      ENNReal.ofReal_ne_top).2 hle |>.trans (ENNReal.toReal_ofReal hpos).le
  have hfield : ∀ i, ∃ Y : ℂ → Ω → ℝ, (∀ x, Measurable (Y x)) ∧
      (∀ x, Y x =ᵐ[P] (T (K i x) : Ω → ℝ)) ∧
      ∀ ω, ∀ β : ℝ≥0, (β : ℝ) < θ → ∀ K' : Set ℂ, IsCompact K' →
        ∃ C' : ℝ≥0, HolderOnWith C' β (fun x => Y x ω) K' := by
    intro i
    refine exists_holder_version_of_gaussian (X := fun x => (T (K i x) : Ω → ℝ))
      (fun x => (Lp.stronglyMeasurable _).measurable) ?_ hθ0 (C := (‖T‖ * C) ^ 2) ?_
    · intro x y
      obtain ⟨v, hv⟩ := hTg (K i x - K i y)
      refine ⟨v, hv.congr ?_⟩
      rw [map_sub]
      exact (Lp.coeFn_sub (T (K i x)) (T (K i y))).symm
    · intro x y
      have h1 : ∫ ω, ((T (K i x) : Ω → ℝ) ω - (T (K i y) : Ω → ℝ) ω) ^ 2 ∂P = ‖T (K i x - K i y)‖ ^ 2 := by
        rw [← integral_sq_coeFn_eq_norm_sq]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_sub (T (K i x)) (T (K i y))] with ω hω
        rw [map_sub, hω, Pi.sub_apply]
      have h3 : ‖T (K i x - K i y)‖ ≤ ‖T‖ * (C * ‖x - y‖ ^ θ) :=
        (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hKdist i x y) (norm_nonneg _))
      rw [h1]
      calc ‖T (K i x - K i y)‖ ^ 2 ≤ (‖T‖ * (C * ‖x - y‖ ^ θ)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ = (‖T‖ * C) ^ 2 * ‖x - y‖ ^ (2 * θ) := by
            rw [mul_comm 2 θ, Real.rpow_mul (norm_nonneg _), Real.rpow_two]
            ring
  choose Y hYm hYX hYH using hfield
  have hYc : ∀ i ω, Continuous fun x => Y i x ω := by
    intro i ω
    have hβ : (0 : ℝ≥0) < (θ / 2).toNNReal := Real.toNNReal_pos.2 (by positivity)
    have hβθ : (((θ / 2).toNNReal : ℝ≥0) : ℝ) < θ := by
      rw [Real.coe_toNNReal _ (by positivity)]
      linarith
    exact continuous_of_forall_holderOnWith hβ fun K' hK' => hYH i ω _ hβθ K' hK'
  refine ⟨Y, fun i ω β hβ K' hK' => hYH i ω β hβ K' hK', ?_⟩
  refine ae_forall_eq_sum_integral hYc fun φ => ?_
  have hv : ContDiff ℝ (⊤ : ℕ∞) (φ : ℂ → ℝ) := φ.contDiff
  have hvc : HasCompactSupport (φ : ℂ → ℝ) := φ.hasCompactSupport
  have hvm : MemLp (φ : ℂ → ℝ) q (volume.restrict (ball c r)) := (hv.continuous.memLp_of_hasCompactSupport hvc).restrict _
  set g : Fin 2 → ℂ → ℝ := fun i x => fderiv ℝ (φ : ℂ → ℝ) x (basis i) with hg
  have hgc : ∀ i, Continuous (g i) := fun i =>
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgs : ∀ i, HasCompactSupport (g i) := fun i => hvc.fderiv_apply (𝕜 := ℝ) (basis i)
  have hsum := sum_integral_smul_newtonGrad_toLp (c := c) (r := r) hq1 hq2 hv hvc hvm
  have hT : T (hvm.toLp (φ : ℂ → ℝ)) = ∑ i : Fin 2, ∫ x, g i x • T (K i x) := by
    rw [← hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← T.integral_comp_comm (integrable_smul_newtonGradLp hq1 hq2 i (hgc i) (hgs i))]
    simp only [map_smul, hg, hK]
  have hi : ∀ i, ((∫ x, g i x • T (K i x) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun ω => ∫ x, g i x * Y i x ω :=
    fun i => coeFn_integral_smul_ae_eq T (continuous_newtonGrad_toLp hq1 hq2 i c r) (hYm i) (hYX i)
      (hYc i) (hgc i) (hgs i)
  filter_upwards [hTφ φ hvm, hi 0, hi 1,
    Lp.coeFn_add (∫ x, g 0 x • T (K 0 x)) (∫ x, g 1 x • T (K 1 x))] with ω h1 h2 h3 h4
  rw [← h1, hT, Fin.sum_univ_two, h4, Pi.add_apply, h2, h3, Fin.sum_univ_two]
  congr 1 <;> refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_) <;> simp only [hg] <;> ring

/-- **The local negative regularity of the zero-boundary Gaussian free field on a disc**
(`MatedCRT.ZeroBoundaryGFFLocalRegularity`; De Nitti–Schweiger, arXiv:2301.13781v4, Proposition 2.1, with `s = 1`,
`d = 2`, `p = q = ∞`, in its test-function form): almost surely, for every `α < 0` and every compact `K` in the
disc, the pairings of `h` with `t⁻² η((· − x)/t)`, `x ∈ K`, `0 < t ≤ t₀`, are at most `C t^α`. -/
theorem zeroBoundaryGFFLocalRegularity : MatedCRT.ZeroBoundaryGFFLocalRegularity := by
  intro c r hr Ω _ P hP h hh
  have := hP
  have key : ∀ m : ℕ, ∃ Y : Fin 2 → ℂ → Ω → ℝ,
      (∀ i ω, ∀ β : ℝ≥0, (β : ℝ) < 2 / (qSeq m : ℝ) - 1 → ∀ K : Set ℂ, IsCompact K →
        ∃ C : ℝ≥0, HolderOnWith C β (fun x => Y i x ω) K) ∧
      ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestOn (MatedCRT.LQGMeasureChart.disc c r),
        h ω φ = ∑ i : Fin 2, ∫ x, Y i x ω * fderiv ℝ φ x (basis i) :=
    fun m => exists_holderField hr (one_lt_qSeq m) (qSeq_lt_two m) hh
  choose Y hYH hYid using key
  filter_upwards [ae_all_iff.2 hYid] with ω hω
  intro α hα K hK hKD
  set β : ℝ := max (1 + α) (1 / 2) with hβdef
  have hβ1 : β < 1 := max_lt (by linarith) (by norm_num)
  have hβpos : 0 < β := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨m, hm⟩ := (tendsto_two_div_qSeq_sub_one.eventually (lt_mem_nhds hβ1)).exists
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open isOpen_ball hKD
  have hK' : IsCompact (cthickening δ K) := hK.cthickening
  have hβn : ((β.toNNReal : ℝ≥0) : ℝ) = β := Real.coe_toNNReal _ hβpos.le
  have hβm : ((β.toNNReal : ℝ≥0) : ℝ) < 2 / (qSeq m : ℝ) - 1 := by rw [hβn]; exact hm
  obtain ⟨M0, hM0⟩ := hYH m 0 ω β.toNNReal hβm _ hK'
  obtain ⟨M1, hM1⟩ := hYH m 1 ω β.toNNReal hβm _ hK'
  have hM : ∀ i, HolderOnWith (max M0 M1) β.toNNReal (fun x => Y m i x ω) (cthickening δ K) := by
    intro i
    fin_cases i
    · exact hM0.mono_const (le_max_left _ _)
    · exact hM1.mono_const (le_max_right _ _)
  have hβn0 : (0 : ℝ≥0) < β.toNNReal := Real.toNNReal_pos.2 hβpos
  have hYc : ∀ i, Continuous fun x => Y m i x ω := fun i =>
    continuous_of_forall_holderOnWith hβn0 fun K'' hK'' => hYH m i ω β.toNNReal hβm K'' hK''
  refine ⟨2 * Real.pi * (max M0 M1 : ℝ≥0), min 1 δ, lt_min one_pos hδ, ?_⟩
  intro x hx t ht η hη hsupp hη1 hgrad
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2.trans (min_le_left _ _)
  have htδ : t ≤ δ := ht.2.trans (min_le_right _ _)
  have hball : closedBall x t ⊆ cthickening δ K :=
    (closedBall_subset_closedBall htδ).trans (closedBall_subset_cthickening hx δ)
  have hvs : tsupport (rescaledTest η x t) ⊆ ball x t := tsupport_rescaledTest_subset hsupp x ht0
  have hvD : tsupport (rescaledTest η x t) ⊆ (MatedCRT.LQGMeasureChart.disc c r : Set ℂ) :=
    hvs.trans (ball_subset_closedBall.trans (hball.trans hδK))
  have hvsmooth : ContDiff ℝ (⊤ : ℕ∞) (rescaledTest η x t) := contDiff_rescaledTest hη x t
  have hvc : HasCompactSupport (rescaledTest η x t) := hasCompactSupport_rescaledTest hsupp x ht0
  have hcond : ContDiff ℝ (⊤ : ℕ∞) (rescaledTest η x t) ∧ HasCompactSupport (rescaledTest η x t) ∧
      tsupport (rescaledTest η x t) ⊆ (MatedCRT.LQGMeasureChart.disc c r : Set ℂ) := ⟨hvsmooth, hvc, hvD⟩
  change |MatedCRT.LQGMeasureChart.pairFun (h ω) (rescaledTest η x t)| ≤ _
  have hpf : MatedCRT.LQGMeasureChart.pairFun (h ω) (rescaledTest η x t) =
      h ω ⟨rescaledTest η x t, hcond.1, hcond.2.1, hcond.2.2⟩ := by
    simp only [MatedCRT.LQGMeasureChart.pairFun, hcond, and_self, dite_true]
  rw [hpf, hω m]
  have hB := norm_fderiv_rescaledTest_le (hη.differentiable (by simp)) hgrad x ht0
  have he : ∀ i : Fin 2, ‖basis i‖ ≤ 1 := by
    intro i
    fin_cases i <;> simp [basis]
  have hbound := abs_sum_integral_mul_fderiv_le hM hYc (hvsmooth.of_le (by simp)) ht0 hvs hball hB he
  refine hbound.trans ?_
  rw [hβn]
  have hpow : t ^ β * (Real.pi * t ^ 2) * (t ^ 3)⁻¹ = Real.pi * t ^ (β - 1) := by
    rw [Real.rpow_sub_one ht0.ne']
    field_simp
  have hle : t ^ (β - 1) ≤ t ^ α :=
    Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith [le_max_left (1 + α) (1 / 2)])
  calc 2 * ((max M0 M1 : ℝ≥0) * t ^ β * (Real.pi * t ^ 2) * (t ^ 3)⁻¹)
      = 2 * Real.pi * (max M0 M1 : ℝ≥0) * t ^ (β - 1) := by
        linear_combination 2 * ((max M0 M1 : ℝ≥0) : ℝ) * hpow
    _ ≤ 2 * Real.pi * (max M0 M1 : ℝ≥0) * t ^ α :=
        mul_le_mul_of_nonneg_left hle (by positivity)

end MatedCRT.GFFLocalRegularity
