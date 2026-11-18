import MatedCRT.FirstPass.Derived.ConeReferenceData
import MatedCRT.FirstPass.Derived.ExitTimeFieldSplit

/-!
# Cone clock weights: splitting and uniform convergence away from the origin

Let `hcirc` be the circle averages of a whole-plane GFF `h^ℂ` and `w` a continuous path. The cone circle averages
`coneRefCircle γ hcirc w ε z` are those of `h^ℂ - γ log |·|` plus those of the continuous radial correction
`coneRefField hcirc w`. By Jensen's formula (`circleAverage_logBound`), at a positive radius `ε`,
`coneRefCircle γ hcirc w ε z = hcirc ε z + (-γ log max(|z|, ε) + ⨍_{∂B_ε(z)} coneRefField)`.

Hence the approximating LQG clock of the cone is the clock of the whole-plane field with the density
`ε^{γ²/2} e^{γ h^ℂ_ε(b_s)}` multiplied by the weight `exp(γ (-γ log max(|b_s|, ε) + ⨍_{∂B_ε(b_s)} coneRefField))`
(`lqgClockApprox_coneRefCircle`). On a compact set `K` at distance at least `δ > 0` from the origin, these weights
converge uniformly, as `ε → 0`, to `exp(γ (-γ log max(|z|, δ) + coneRefField z))`, a continuous function on the
plane which equals `exp(γ (-γ log |z| + coneRefField z))` on `K` (`tendstoUniformlyOn_coneClockWeight`); along a
path staying in `K` on `[0, h]`, the weights converge uniformly on `[0, h]`
(`tendstoUniformlyOn_coneClockWeight_path`).
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Filter HarmonicBalls MarkovProcess
open scoped NNReal Topology

/-- **Splitting of the cone circle averages** (Jensen's formula for `log |·|`): at a positive radius `r`,
`coneRefCircle γ hcirc w r z = hcirc r z + (-γ log max(|z|, r) + ⨍_{∂B_r(z)} coneRefField hcirc w)`. -/
theorem coneRefCircle_eq_add (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ) {r : ℝ} (hr : 0 < r)
    (z : ℂ) :
    coneRefCircle γ hcirc w r z =
      hcirc r z + (-γ * Real.log (max ‖z‖ r) + Real.circleAverage (coneRefField hcirc w) z r) := by
  have h := MatedCRT.FieldSplit.circleAverage_logBound (-1) 0 z hr
  have hf : (fun x : ℂ => -1 * -Real.log ‖x‖ + 0) = fun x => Real.log ‖x‖ := by
    funext x; ring
  rw [hf] at h
  simp only [coneRefCircle, HarmonicBalls.fieldCircleAverage, h]
  ring

/-- The approximating LQG clock of the cone at a positive scale `ε` is the integral of the whole-plane density
`ε^{γ²/2} e^{γ h^ℂ_ε(b_s)}` against the cone weight `exp(γ (-γ log max(|b_s|, ε) + ⨍_{∂B_ε(b_s)} coneRefField))`. -/
theorem lqgClockApprox_coneRefCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ) {ε : ℝ}
    (hε : 0 < ε) (b : ContinuousPath ℂ) (t : ℝ≥0) :
    lqgClockApprox γ (coneRefCircle γ hcirc w) ε b t =
      ∫ s in (0 : ℝ)..(t : ℝ), ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε (b s.toNNReal)) *
        Real.exp (γ * (-γ * Real.log (max ‖b s.toNNReal‖ ε) +
          Real.circleAverage (coneRefField hcirc w) (b s.toNNReal) ε)) := by
  unfold lqgClockApprox
  congr 1
  funext s
  rw [coneRefCircle_eq_add γ hcirc w hε, mul_add, Real.exp_add, mul_assoc]

/-- At a positive scale `ε`, the cone weight `z ↦ exp(γ (-γ log max(|z|, ε) + ⨍_{∂B_ε(z)} F))` of a continuous
`F` is continuous on the plane. -/
theorem continuous_coneClockWeight {F : ℂ → ℝ} (hF : Continuous F) (γ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun z : ℂ =>
      Real.exp (γ * (-γ * Real.log (max ‖z‖ ε) + Real.circleAverage F z ε)) := by
  have h1 : Continuous fun z : ℂ => Real.circleAverage F z ε :=
    (LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center hF).comp
      (continuous_const.prodMk continuous_id)
  have h2 : Continuous fun z : ℂ => Real.log (max ‖z‖ ε) :=
    (continuous_norm.max continuous_const).log fun z => (hε.trans_le (le_max_right _ _)).ne'
  exact Real.continuous_exp.comp (continuous_const.mul ((continuous_const.mul h2).add h1))

/-- For `δ > 0` and a continuous `F`, the limit weight `z ↦ exp(γ (-γ log max(|z|, δ) + F z))` is continuous on
the plane. -/
theorem continuous_coneClockWeightLimit {F : ℂ → ℝ} (hF : Continuous F) (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous fun z : ℂ => Real.exp (γ * (-γ * Real.log (max ‖z‖ δ) + F z)) := by
  have h2 : Continuous fun z : ℂ => Real.log (max ‖z‖ δ) :=
    (continuous_norm.max continuous_const).log fun z => (hδ.trans_le (le_max_right _ _)).ne'
  exact Real.continuous_exp.comp (continuous_const.mul ((continuous_const.mul h2).add hF))

/-- **Uniform convergence of the cone weights away from the origin.** Let `F` be continuous, `K` compact with
`δ ≤ |z|` on `K` for some `δ > 0`, and `ε k → 0`. Then
`exp(γ (-γ log max(|z|, ε k) + ⨍_{∂B_{ε k}(z)} F)) → exp(γ (-γ log max(|z|, δ) + F z))` uniformly on `K`. -/
theorem tendstoUniformlyOn_coneClockWeight {F : ℂ → ℝ} (hF : Continuous F) (γ : ℝ) {K : Set ℂ}
    (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) (hKδ : ∀ z ∈ K, δ ≤ ‖z‖) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformlyOn
      (fun k z => Real.exp (γ * (-γ * Real.log (max ‖z‖ (ε k)) + Real.circleAverage F z (ε k))))
      (fun z => Real.exp (γ * (-γ * Real.log (max ‖z‖ δ) + F z))) atTop K := by
  set G : ℝ → ℂ → ℝ := fun r z =>
    Real.exp (γ * (-γ * Real.log (max ‖z‖ δ) + Real.circleAverage F z r)) with hGdef
  have hGc : Continuous (Function.uncurry G) := by
    have h1 := LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center hF
    have h2 : Continuous fun p : ℝ × ℂ => Real.log (max ‖p.2‖ δ) :=
      ((continuous_norm.comp continuous_snd).max continuous_const).log
        fun p => (hδ.trans_le (le_max_right _ _)).ne'
    exact Real.continuous_exp.comp (continuous_const.mul ((continuous_const.mul h2).add h1))
  let U : Set ℝ := Icc (-1) 1
  have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hu : UniformContinuousOn (Function.uncurry G) (U ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hGc.continuousOn
  have ht : TendstoUniformlyOn G (G 0) (𝓝 0) K := by
    simpa only [nhdsWithin_eq_nhds.mpr hU] using hu.tendstoUniformlyOn (mem_of_mem_nhds hU)
  have hG0 : G 0 = fun z => Real.exp (γ * (-γ * Real.log (max ‖z‖ δ) + F z)) := by
    funext z
    simp only [hGdef, Real.circleAverage_zero]
  rw [hG0] at ht
  have hcomp : TendstoUniformlyOn (fun k => G (ε k))
      (fun z => Real.exp (γ * (-γ * Real.log (max ‖z‖ δ) + F z))) atTop K :=
    fun u hu => hε.eventually (ht u hu)
  refine hcomp.congr ?_
  filter_upwards [hε.eventually (eventually_le_nhds hδ)] with k hk z hz
  have hm : max ‖z‖ (ε k) = max ‖z‖ δ := by
    rw [max_eq_left (hk.trans (hKδ z hz)), max_eq_left (hKδ z hz)]
  simp only [hGdef, hm]

/-- **Along a path avoiding the origin.** If `b_t ∈ closedBall a r` for `t ∈ [0, h]` with `r < |a|`, then the cone
weights along `b` converge uniformly on `[0, h]` to the continuous limit weight with `δ = |a| - r`. -/
theorem tendstoUniformlyOn_coneClockWeight_path {F : ℂ → ℝ} (hF : Continuous F) (γ : ℝ) {a : ℂ} {r : ℝ}
    (hr : r < ‖a‖) {h : ℝ≥0} {b : ContinuousPath ℂ}
    (hb : ∀ t ∈ Icc (0 : ℝ≥0) h, b t ∈ Metric.closedBall a r) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformlyOn
      (fun k (s : ℝ) => Real.exp (γ * (-γ * Real.log (max ‖b s.toNNReal‖ (ε k)) +
        Real.circleAverage F (b s.toNNReal) (ε k))))
      (fun s => Real.exp (γ * (-γ * Real.log (max ‖b s.toNNReal‖ (‖a‖ - r)) + F (b s.toNNReal))))
      atTop (Icc 0 (h : ℝ)) := by
  have hKδ : ∀ z ∈ Metric.closedBall a r, ‖a‖ - r ≤ ‖z‖ := by
    intro z hz
    have h1 : ‖a - z‖ ≤ r := by rw [← dist_eq_norm, dist_comm]; exact hz
    have h2 := norm_sub_norm_le a z
    linarith
  have hmain := (tendstoUniformlyOn_coneClockWeight hF γ (isCompact_closedBall a r)
    (sub_pos.2 hr) hKδ hε).comp (fun s : ℝ => b s.toNNReal)
  refine hmain.mono fun s hs => ?_
  refine hb s.toNNReal ⟨zero_le, ?_⟩
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
  exact hs.2

/-! ### Time-index transfer and the whole-plane density along a path -/

/-- **Time-index transfer.** For `G : ℕ → ℝ → ℝ`, the uniform Cauchy property on `[0, h]` of the restrictions to
`ℝ≥0` is the uniform Cauchy property on the real interval `[0, h]`. -/
theorem uniformCauchySeqOn_nnreal_Icc_iff {G : ℕ → ℝ → ℝ} {h : ℝ≥0} :
    UniformCauchySeqOn (fun k (t : ℝ≥0) => G k t) atTop (Icc 0 h) ↔
      UniformCauchySeqOn G atTop (Icc 0 (h : ℝ)) := by
  constructor
  · intro hG u hu
    filter_upwards [hG u hu] with m hm x hx
    have hx' : x.toNNReal ∈ Icc 0 h := by
      refine ⟨zero_le, ?_⟩
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx.1]
      exact hx.2
    simpa only [Real.coe_toNNReal _ hx.1] using hm x.toNNReal hx'
  · intro hG u hu
    filter_upwards [hG u hu] with m hm t ht
    exact hm t ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht.2⟩

/-- Along a continuous path `b`, the whole-plane clock density `s ↦ ε^{γ²/2} e^{γ hcirc ε (b_s)}` at a positive
scale `ε` is continuous when the circle averages are jointly continuous at positive radii. -/
theorem continuous_lqgClockDensity_path (γ : ℝ) {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) {ε : ℝ} (hε : 0 < ε)
    (b : ContinuousPath ℂ) :
    Continuous fun s : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε (b s.toNNReal)) := by
  have h1 : Continuous fun z : ℂ => hcirc ε z :=
    hc.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hε, mem_univ _⟩
  have hb : Continuous fun s : ℝ => b s.toNNReal := b.continuous.comp continuous_real_toNNReal
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (h1.comp hb)))

/-- The whole-plane clock density at a positive scale is nonnegative. -/
theorem lqgClockDensity_nonneg (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε z) :=
  mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le

/-- Along a continuous path, the cone weight at a positive scale and the limit weight (for `δ > 0`) are continuous
functions of time. -/
theorem continuous_coneClockWeight_path {F : ℂ → ℝ} (hF : Continuous F) (γ : ℝ) (b : ContinuousPath ℂ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (Continuous fun s : ℝ => Real.exp (γ * (-γ * Real.log (max ‖b s.toNNReal‖ ε) +
        Real.circleAverage F (b s.toNNReal) ε))) ∧
      Continuous fun s : ℝ =>
        Real.exp (γ * (-γ * Real.log (max ‖b s.toNNReal‖ δ) + F (b s.toNNReal))) := by
  have hb : Continuous fun s : ℝ => b s.toNNReal := b.continuous.comp continuous_real_toNNReal
  exact ⟨(continuous_coneClockWeight hF γ hε).comp hb, (continuous_coneClockWeightLimit hF γ hδ).comp hb⟩

end MatedCRT.FirstPass.Derived
