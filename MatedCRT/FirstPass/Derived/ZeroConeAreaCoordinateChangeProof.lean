import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main
import LatticeProb.Analysis.CircleLogIntegrals
import LatticeProb.Prob.RadialCircleIntegrable
import LatticeProb.LQG.AreaCurveMassMeasurable
import LatticeProb.Analysis.VagueLimitSequence
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeZero
import LatticeProb.LQG.AreaReparamMeasurable
import MatedCRT.FirstPass.Derived.ZeroConeQuantumCurveCovarianceProof

/-!
# The simultaneous coordinate change of the area measure of the `0`-quantum cone

We prove `ZeroConeAreaCoordinateChange γ hγ` for every `0 < γ < 2`
(`MatedCRT.zeroConeAreaCoordinateChange`): there is a Borel map `M` from fields to measures on `ℂ`
such that, for the circle-average embedding `h` of the `0`-quantum cone, almost surely `M h` is the
vague limit of the dyadic area approximations of `h` and, for all `C > 0` and `z ∈ ℂ` simultaneously,
`M(h(C · + z) + Q log C) = M h ∘ ψ`, `ψ(w) = C w + z` (Sheffield–Wang, arXiv:1605.06171,
Theorems 1.1, 1.2 and 1.4; Duplantier–Sheffield 2011).

* **The Borel map.** A field is *scale regular* (`ScaleRegular`) if its mollified circle averages
  `(s, w, ρ) ↦ h_s(w, ρ)` extend continuously to the closed scale `s = 0`; on the good set
  `goodSet γ` of scale-regular fields whose dyadic area approximations converge vaguely, the area map
  `areaMap γ` is the limit area measure, and `0` elsewhere. Scale regularity is a countable uniform
  continuity condition and the vague convergence a countable Cauchy condition on a determining
  family, so `goodSet γ` is Borel and `areaMap γ` is measurable. The good set is invariant under the
  LQG coordinate change, and on it the deterministic coordinate change of the area measure
  (`lqgArea_affine_eq`) gives the identity for every similarity at once.
* **The cone lies in the good set.** The whole-plane GFF part is scale regular by the Kolmogorov
  continuity theorem for its mollified circle-average process. The radial parts (the radial average
  of the GFF and the cone profile built from the Brownian motions) are radial, continuous off `0`
  and have a logarithmic singularity at `0`; their circle averages are continuous in the center and
  the radius (dominated convergence with the bound `-log |cos (θ / 2)|`), so their mollified circle
  averages extend continuously to `s = 0`. The dyadic area approximations of the cone converge
  (`hasAreaLimitS_cone`).
-/

set_option autoImplicit false

noncomputable section

section CircleAveragesOfRadialFunctions

open MeasureTheory Filter Topology Set Metric
open scoped Real NNReal ENNReal Interval

namespace MatedCRT.ConeAreaCovariance

open LQGMetric LQGMetric.CircleAvg LQGMetric.TestIntegral MatedCRTHarmonic.CellScaling
open MatedCRTHarmonic.LQGCoord

/-- A function on `ℂ` is radial if its value depends only on the modulus. -/
def IsRadial (g : ℂ → ℝ) : Prop := ∀ u v : ℂ, ‖u‖ = ‖v‖ → g u = g v

/-- A logarithmic bound at the origin: `|g y| ≤ C (1 - log |y|)` on the punctured unit disc. -/
def HasLogBound (g : ℂ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℂ, y ≠ 0 → ‖y‖ < 1 → |g y| ≤ C * (1 - Real.log ‖y‖)

/-! ## Rotation to a real centre -/

lemma circleMap_eq_exp_mul (w : ℂ) (ρ θ : ℝ) :
    circleMap w ρ θ = Complex.exp (Complex.arg w * Complex.I) *
      circleMap (‖w‖ : ℂ) ρ (θ - Complex.arg w) := by
  have h1 : Complex.exp (Complex.arg w * Complex.I) * (‖w‖ : ℂ) = w := by
    rw [mul_comm]; exact Complex.norm_mul_exp_arg_mul_I w
  have h2 : Complex.exp (Complex.arg w * Complex.I) *
      ((ρ : ℂ) * Complex.exp (((θ - Complex.arg w : ℝ) : ℂ) * Complex.I)) =
      (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp only [circleMap, mul_add, h1, h2]

/-- **Rotation invariance**: the circle average of a radial function over `∂B(w, ρ)` is its circle
average over `∂B(|w|, ρ)`. -/
theorem circleAverage_radial {g : ℂ → ℝ} (hg : IsRadial g) (w : ℂ) (ρ : ℝ) :
    Real.circleAverage g w ρ = Real.circleAverage g (‖w‖ : ℂ) ρ := by
  have hpt : ∀ θ : ℝ, g (circleMap w ρ θ) = g (circleMap (‖w‖ : ℂ) ρ (θ - Complex.arg w)) := by
    intro θ
    apply hg
    rw [circleMap_eq_exp_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simp only [Real.circleAverage_def]
  congr 1
  simp_rw [hpt]
  rw [intervalIntegral.integral_comp_sub_right (fun θ => g (circleMap (‖w‖ : ℂ) ρ θ))]
  have hper : Function.Periodic (fun θ => g (circleMap (‖w‖ : ℂ) ρ θ)) (2 * π) := by
    intro θ
    simp only [periodic_circleMap _ _ θ]
  have h := hper.intervalIntegral_add_eq (-Complex.arg w) 0
  rw [zero_add] at h
  rw [show (0 : ℝ) - Complex.arg w = -Complex.arg w by ring,
    show 2 * π - Complex.arg w = -Complex.arg w + 2 * π by ring]
  exact h

/-- On a circle `∂B(r, ρ)` with real centre `r ≥ 0`, `|r + ρ e^{iθ}| ≥ (ρ/2) |cos(θ/2)|`. -/
lemma norm_circleMap_ofReal_ge {r ρ : ℝ} (hr : 0 ≤ r) (hρ : 0 < ρ) (θ : ℝ) :
    ρ / 2 * |Real.cos (θ / 2)| ≤ ‖circleMap (r : ℂ) ρ θ‖ := by
  have hre : (circleMap (r : ℂ) ρ θ).re = r + ρ * Real.cos θ := by
    simp [circleMap, Complex.exp_ofReal_mul_I_re]
  have him : (circleMap (r : ℂ) ρ θ).im = ρ * Real.sin θ := by
    simp [circleMap, Complex.exp_ofReal_mul_I_im]
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; congr 1; ring
  have hsq : ‖circleMap (r : ℂ) ρ θ‖ ^ 2 = (r - ρ) ^ 2 + 4 * r * ρ * Real.cos (θ / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    linear_combination (ρ ^ 2) * Real.sin_sq_add_cos_sq θ + (2 * r * ρ) * hc
  have hC1 : Real.cos (θ / 2) ^ 2 ≤ 1 := Real.cos_sq_le_one _
  have hC0 : 0 ≤ Real.cos (θ / 2) ^ 2 := sq_nonneg _
  have key : (ρ / 2 * |Real.cos (θ / 2)|) ^ 2 ≤ ‖circleMap (r : ℂ) ρ θ‖ ^ 2 := by
    rw [hsq, mul_pow, sq_abs]
    rcases le_or_gt (ρ / 4) r with h | h
    · nlinarith [mul_le_mul_of_nonneg_right h (mul_nonneg hρ.le hC0), sq_nonneg (r - ρ)]
    · nlinarith [mul_nonneg (mul_nonneg hr hρ.le) hC0, mul_le_mul_of_nonneg_left hC1 (sq_nonneg ρ),
        mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 3 * ρ / 4) (by linarith : 3 * ρ / 4 ≤ ρ - r)]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 key

/-- The angles at which `cos (θ/2)` vanishes form a Lebesgue-null set. -/
lemma ae_cos_half_ne_zero : ∀ᵐ θ : ℝ, Real.cos (θ / 2) ≠ 0 := by
  have h0 := LatticeProb.RadialCircle.volume_setOf_circleMap_eq (1 : ℂ) 0 one_ne_zero
  rw [ae_iff]
  refine measure_mono_null (fun θ hθ => ?_) h0
  have hθ' : Real.cos (θ / 2) = 0 := not_not.1 hθ
  show circleMap 1 1 θ = 0
  have hn := LatticeProb.CircleLogIntegrals.norm_exp_add_exp_mul_I 0 θ
  rw [sub_zero, hθ', abs_zero, mul_zero] at hn
  rw [← norm_eq_zero]
  simpa [circleMap] using hn

/-! ## Continuity of the circle averages -/

/-- **Continuity at a real centre.** For `g` measurable, continuous off `0` and with a logarithmic
bound at `0`, `(r, ρ) ↦ ⨍_{∂B(r, ρ)} g` is continuous on `[0, ∞) × (0, ∞)`: dominated convergence
with the bound `K + C (1 + |log (4/ρ₀)| + |log |cos(θ/2)||)`. -/
theorem continuousWithinAt_circleAverage_ofReal {g : ℂ → ℝ} (hgm : Measurable g)
    (hgc : ContinuousOn g {0}ᶜ) (hgb : HasLogBound g) {r₀ ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ContinuousWithinAt (fun p : ℝ × ℝ => Real.circleAverage g (p.1 : ℂ) p.2)
      (Ici 0 ×ˢ Ioi 0) (r₀, ρ₀) := by
  obtain ⟨C, hC0, hC⟩ := hgb
  set R : ℝ := |r₀| + 1 + 2 * ρ₀ with hR
  set A : Set ℂ := {y | 1 ≤ ‖y‖} ∩ closedBall 0 R with hA
  have hAc : IsCompact A :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const continuous_norm)
  have hA0 : A ⊆ {0}ᶜ := by
    intro y hy h0
    rw [mem_singleton_iff] at h0
    have h1 : (1 : ℝ) ≤ ‖y‖ := hy.1
    rw [h0, norm_zero] at h1
    linarith
  obtain ⟨K, hK⟩ := hAc.exists_bound_of_continuousOn (hgc.mono hA0)
  have h1A : (1 : ℂ) ∈ A := by
    refine ⟨by simp, ?_⟩
    rw [mem_closedBall_zero_iff, norm_one]
    have := abs_nonneg r₀
    linarith
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 1 h1A)
  set L : ℝ := |Real.log (4 / ρ₀)| with hL
  set bound : ℝ → ℝ := fun θ => K + C * (1 + L + |Real.log (Real.cos (θ / 2))|) with hbound
  have hbi : IntervalIntegrable bound volume 0 (2 * π) := by
    have h1 := (LatticeProb.CircleLogIntegrals.intervalIntegrable_log_cos_affine 0).abs
    simp only [sub_zero] at h1
    exact intervalIntegrable_const.add ((intervalIntegrable_const.add h1).const_mul C)
  have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝[Ici 0 ×ˢ Ioi 0] (r₀, ρ₀),
      0 ≤ p.1 ∧ p.1 < |r₀| + 1 ∧ ρ₀ / 2 < p.2 ∧ p.2 < 2 * ρ₀ := by
    have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, ρ₀), p.1 < |r₀| + 1 :=
      (continuous_fst.tendsto (r₀, ρ₀)).eventually
        (gt_mem_nhds (by linarith [le_abs_self r₀] : r₀ < |r₀| + 1))
    have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, ρ₀), ρ₀ / 2 < p.2 :=
      (continuous_snd.tendsto (r₀, ρ₀)).eventually (lt_mem_nhds (by linarith : ρ₀ / 2 < ρ₀))
    have h3 : ∀ᶠ p : ℝ × ℝ in 𝓝 (r₀, ρ₀), p.2 < 2 * ρ₀ :=
      (continuous_snd.tendsto (r₀, ρ₀)).eventually (gt_mem_nhds (by linarith : ρ₀ < 2 * ρ₀))
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3,
      self_mem_nhdsWithin] with p hp1 hp2 hp3 hp
    exact ⟨hp.1, hp1, hp2, hp3⟩
  have hbd : ∀ᶠ p : ℝ × ℝ in 𝓝[Ici 0 ×ˢ Ioi 0] (r₀, ρ₀), ∀ᵐ θ : ℝ, θ ∈ Ι 0 (2 * π) →
      ‖g (circleMap (p.1 : ℂ) p.2 θ)‖ ≤ bound θ := by
    filter_upwards [hnear] with p hp
    obtain ⟨hp0, hp1, hp2, hp3⟩ := hp
    filter_upwards [ae_cos_half_ne_zero] with θ hθ _
    have hρ : 0 < p.2 := by linarith
    have hy : p.2 / 2 * |Real.cos (θ / 2)| ≤ ‖circleMap (p.1 : ℂ) p.2 θ‖ :=
      norm_circleMap_ofReal_ge hp0 hρ θ
    have hpos : 0 < p.2 / 2 * |Real.cos (θ / 2)| := mul_pos (by linarith) (abs_pos.2 hθ)
    have hy0 : circleMap (p.1 : ℂ) p.2 θ ≠ 0 := norm_pos_iff.1 (hpos.trans_le hy)
    have hyR : ‖circleMap (p.1 : ℂ) p.2 θ‖ ≤ R := by
      have h := LatticeProb.CircleLogIntegrals.norm_circleMap_le_add (p.1 : ℂ) hρ θ
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0] at h
      linarith
    have hL0 : 0 ≤ L := abs_nonneg _
    have hlc : 0 ≤ |Real.log (Real.cos (θ / 2))| := abs_nonneg _
    have hmain : 0 ≤ C * (1 + L + |Real.log (Real.cos (θ / 2))|) := by positivity
    rw [Real.norm_eq_abs]
    rcases le_or_gt 1 ‖circleMap (p.1 : ℂ) p.2 θ‖ with h1 | h1
    · have hk := hK _ ⟨h1, mem_closedBall_zero_iff.2 hyR⟩
      rw [Real.norm_eq_abs] at hk
      simp only [hbound]
      linarith
    · have hb := hC _ hy0 h1
      have hlog : -Real.log ‖circleMap (p.1 : ℂ) p.2 θ‖ ≤ L + |Real.log (Real.cos (θ / 2))| := by
        have h1' := Real.log_le_log hpos hy
        rw [Real.log_mul (by linarith) (abs_ne_zero.2 hθ), Real.log_abs] at h1'
        have h2' : Real.log (ρ₀ / 4) ≤ Real.log (p.2 / 2) :=
          Real.log_le_log (by positivity) (by linarith)
        have h3' : -Real.log (ρ₀ / 4) = Real.log (4 / ρ₀) := by
          rw [← Real.log_inv, inv_div]
        have h4' : Real.log (4 / ρ₀) ≤ L := le_abs_self _
        have h5' : -Real.log (Real.cos (θ / 2)) ≤ |Real.log (Real.cos (θ / 2))| := neg_le_abs _
        linarith
      have h6 : C * (1 - Real.log ‖circleMap (p.1 : ℂ) p.2 θ‖) ≤
          C * (1 + L + |Real.log (Real.cos (θ / 2))|) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0
      simp only [hbound]
      linarith
  have hmeas : ∀ᶠ p : ℝ × ℝ in 𝓝[Ici 0 ×ˢ Ioi 0] (r₀, ρ₀),
      AEStronglyMeasurable (fun θ => g (circleMap (p.1 : ℂ) p.2 θ)) (volume.restrict (Ι 0 (2 * π))) :=
    Eventually.of_forall fun p =>
      (hgm.comp (continuous_circleMap _ _).measurable).aestronglyMeasurable
  have hcont : ∀ᵐ θ : ℝ, θ ∈ Ι 0 (2 * π) →
      ContinuousWithinAt (fun p : ℝ × ℝ => g (circleMap (p.1 : ℂ) p.2 θ)) (Ici 0 ×ˢ Ioi 0)
        (r₀, ρ₀) := by
    have hnull := LatticeProb.RadialCircle.volume_setOf_circleMap_eq (r₀ : ℂ) 0 hρ₀.ne'
    have hae : ∀ᵐ θ : ℝ, circleMap (r₀ : ℂ) ρ₀ θ ≠ 0 := by
      rw [ae_iff]; simpa using hnull
    filter_upwards [hae] with θ hθ _
    have hcm : Continuous fun p : ℝ × ℝ => circleMap (p.1 : ℂ) p.2 θ := by
      simp only [circleMap]; fun_prop
    have hθ' : circleMap ((r₀, ρ₀).1 : ℂ) (r₀, ρ₀).2 θ ∈ ({0}ᶜ : Set ℂ) := hθ
    exact (ContinuousAt.comp (f := fun p : ℝ × ℝ => circleMap (p.1 : ℂ) p.2 θ) (x := (r₀, ρ₀))
      (hgc.continuousAt (isOpen_compl_singleton.mem_nhds hθ')) hcm.continuousAt).continuousWithinAt
  have hmain := intervalIntegral.continuousWithinAt_of_dominated_interval hmeas hbd hbi hcont
  simp only [Real.circleAverage_def, smul_eq_mul]
  exact continuousWithinAt_const.mul hmain

/-- **Continuity of the circle averages of a radial function** with a logarithmic singularity at `0`:
`(w, ρ) ↦ ⨍_{∂B(w, ρ)} g` is continuous on `ℂ × (0, ∞)`, including the circles through `0`. -/
theorem continuousOn_circleAverage_radial {g : ℂ → ℝ} (hg : IsRadial g) (hgm : Measurable g)
    (hgc : ContinuousOn g {0}ᶜ) (hgb : HasLogBound g) :
    ContinuousOn (fun p : ℂ × ℝ => Real.circleAverage g p.1 p.2) (univ ×ˢ Ioi 0) := by
  intro p hp
  have hf : ContinuousWithinAt (fun q : ℂ × ℝ => ((‖q.1‖ : ℝ), q.2)) (univ ×ˢ Ioi 0) p :=
    ((continuous_norm.comp continuous_fst).prodMk continuous_snd).continuousWithinAt
  have hmaps : MapsTo (fun q : ℂ × ℝ => ((‖q.1‖ : ℝ), q.2)) (univ ×ˢ Ioi 0) (Ici 0 ×ˢ Ioi 0) :=
    fun q hq => ⟨norm_nonneg _, hq.2⟩
  have h := ContinuousWithinAt.comp (f := fun q : ℂ × ℝ => ((‖q.1‖ : ℝ), q.2)) (x := p)
    (continuousWithinAt_circleAverage_ofReal hgm hgc hgb (r₀ := ‖p.1‖) hp.2) hf hmaps
  exact h.congr (fun q _ => circleAverage_radial hg q.1 q.2) (circleAverage_radial hg p.1 p.2)

/-! ## The mollified circle averages as mollified circle averages of `g` -/

/-- **Fubini**: the scale-`s` mollified circle average of `ofFunC g` is the mollification of the
circle averages of `g`: `⨍_{∂B(w,ρ)} ⟨g, ψ_{s,x}⟩ = ∫ ψ_s(v) ⨍_{∂B(w + v, ρ)} g dv`. -/
theorem mollAvgS_ofFunC_eq {g : ℂ → ℝ} (hgm : Measurable g) (hgl : LocallyIntegrable g volume)
    (s : ℝ) (w : ℂ) (ρ : ℝ) :
    mollAvgS (ofFunC g) s w ρ = ∫ v, bumpS s 0 v * Real.circleAverage g (w + v) ρ := by
  set F : ℝ → ℂ → ℝ := fun θ y => g y * bumpS s 0 (y - circleMap w ρ θ) with hF
  set G : ℝ → ℂ → ℝ := fun θ t => bumpS s 0 t * g (circleMap w ρ θ + t) with hG
  have hGF : ∀ θ t, G θ t = F θ (t + circleMap w ρ θ) := by
    intro θ t
    simp only [hF, hG, add_sub_cancel_right]
    rw [mul_comm, add_comm]
  have hFm : Measurable (Function.uncurry F) := by
    have h1 : Continuous (bumpS s 0 : ℂ → ℝ) := (bumpS s 0).continuous
    have h2 : Continuous fun p : ℝ × ℂ => p.2 - circleMap w ρ p.1 :=
      continuous_snd.sub ((continuous_circleMap w ρ).comp continuous_fst)
    exact (hgm.comp measurable_snd).mul (h1.comp h2).measurable
  have hGm : Measurable (Function.uncurry G) := by
    have h1 : Continuous (bumpS s 0 : ℂ → ℝ) := (bumpS s 0).continuous
    have h2 : Continuous fun p : ℝ × ℂ => circleMap w ρ p.1 + p.2 :=
      ((continuous_circleMap w ρ).comp continuous_fst).add continuous_snd
    exact (h1.comp continuous_snd).measurable.mul (hgm.comp h2.measurable)
  have hFi : Integrable (Function.uncurry F) (μθS.prod volume) := by
    obtain ⟨M, hM⟩ := (bumpS s 0).continuous.bounded_above_of_compact_support
      (bumpS s 0).hasCompactSupport
    set B := closedBall w (|ρ| + |s|)
    have hb : Integrable (fun y => M * B.indicator (fun y => |g y|) y) := by
      refine Integrable.const_mul ?_ M
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact (hgl.integrableOn_isCompact (isCompact_closedBall _ _)).abs
    refine Integrable.mono' (hb.comp_snd μθS) hFm.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    simp only [Function.uncurry, hF, norm_mul]
    by_cases hp : ‖p.2 - circleMap w ρ p.1‖ < |s|
    · have hpB : p.2 ∈ B := by
        have h2 : dist (circleMap w ρ p.1) w = |ρ| := by
          simp [dist_eq_norm, circleMap_sub_center]
        have h3 : dist p.2 (circleMap w ρ p.1) < |s| := by rw [dist_eq_norm]; exact hp
        rw [mem_closedBall]
        linarith [dist_triangle p.2 (circleMap w ρ p.1) w]
      rw [indicator_of_mem hpB, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
    · rw [bumpS_eq_zero s (by rw [dist_zero_right]; linarith), norm_zero, mul_zero]
      exact mul_nonneg hM0 (indicator_nonneg (fun _ _ => abs_nonneg _) _)
  have hGi : Integrable (Function.uncurry G) (μθS.prod volume) := by
    rw [integrable_prod_iff hGm.aestronglyMeasurable]
    constructor
    · filter_upwards [hFi.prod_right_ae] with θ hθ
      exact (hθ.comp_add_right (circleMap w ρ θ)).congr
        (Eventually.of_forall fun t => (hGF θ t).symm)
    · refine hFi.integral_norm_prod_left.congr (Eventually.of_forall fun θ => ?_)
      simp only [Function.uncurry]
      rw [← integral_add_right_eq_self (fun y => ‖F θ y‖) (circleMap w ρ θ)]
      simp only [hGF]
  have hL : mollAvgS (ofFunC g) s w ρ = (2 * π)⁻¹ * ∫ θ, ∫ t, G θ t ∂volume ∂μθS := by
    rw [mollAvgS, Real.circleAverage_def, smul_eq_mul,
      intervalIntegral.integral_of_le (by positivity)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hG]
    rw [ofFunC_apply_li hgl,
      ← integral_add_left_eq_self (fun y => bumpS s (circleMap w ρ θ) y * g y) (circleMap w ρ θ)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [bumpS_eq_sub, add_sub_cancel_left]
  have hR : ∫ v, bumpS s 0 v * Real.circleAverage g (w + v) ρ =
      (2 * π)⁻¹ * ∫ t, ∫ θ, G θ t ∂μθS := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hG]
    rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le (by positivity),
      integral_const_mul]
    have e : ∀ θ, circleMap (w + t) ρ θ = circleMap w ρ θ + t := fun θ => by
      simp only [circleMap]; ring
    simp_rw [e]
    ring
  rw [hL, hR, integral_integral_swap hGi]

/-- `|∫ ψ_s(v) c(v) dv − c₀| ≤ η` when `|c v − c₀| ≤ η` for `|v| ≤ s`. -/
lemma abs_integral_bumpS_mul_sub_le {c : ℂ → ℝ} (hc : Continuous c) {s : ℝ} (hs : 0 < s)
    {c₀ η : ℝ} (hη : ∀ v ∈ closedBall (0 : ℂ) s, |c v - c₀| ≤ η) :
    |(∫ v, bumpS s 0 v * c v) - c₀| ≤ η := by
  have hi : Integrable fun v => bumpS s 0 v * c v :=
    ((bumpS s 0).continuous.mul hc).integrable_of_hasCompactSupport
      (bumpS s 0).hasCompactSupport.mul_right
  have hib : Integrable fun v => bumpS s 0 v := integrable_testC _
  have e : (∫ v, bumpS s 0 v * c v) - c₀ = ∫ v, bumpS s 0 v * (c v - c₀) := by
    simp_rw [mul_sub]
    rw [integral_sub hi (hib.mul_const _), integral_mul_const, integral_bumpS hs, one_mul]
  rw [e, ← Real.norm_eq_abs]
  have hb : ∀ v, ‖bumpS s 0 v * (c v - c₀)‖ ≤ bumpS s 0 v * η := by
    intro v
    rw [norm_mul, Real.norm_of_nonneg (bumpS_nonneg s 0 v)]
    by_cases hv : dist v 0 < s
    · exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hη v hv.le)
        (bumpS_nonneg s 0 v)
    · rw [bumpS_eq_zero s (by rw [abs_of_pos hs]; exact not_lt.mp hv), zero_mul, zero_mul]
  refine (norm_integral_le_of_norm_le (hib.mul_const _) (Eventually.of_forall hb)).trans
    (le_of_eq ?_)
  rw [integral_mul_const, integral_bumpS hs, one_mul]

/-! ## The continuous extension to scale `0` -/

/-- The mollified circle averages of `ofFunC g` in the parametrization `q = (s, Re w, Im w, log ρ)` of
`ScaleKolm`, extended at scale `0` by the circle averages of `g`. -/
def radialExt (g : ℂ → ℝ) (q : Fin 4 → ℝ) : ℝ :=
  if q 0 = 0 then Real.circleAverage g (kW q) (kR q) else mollAvgS (ofFunC g) (kS q) (kW q) (kR q)

/-- **The mollified circle averages of `ofFunC g` extend continuously to scale `0`** for a radial `g`,
measurable, locally integrable, continuous off `0` and with a logarithmic bound at `0`. -/
theorem continuous_radialExt {g : ℂ → ℝ} (hg : IsRadial g) (hgm : Measurable g)
    (hgl : LocallyIntegrable g volume) (hgc : ContinuousOn g {0}ᶜ) (hgb : HasLogBound g) :
    Continuous (radialExt g) := by
  have hcA := continuousOn_circleAverage_radial hg hgm hgc hgb
  have continuous_kW : Continuous kW := by
    have e : kW = fun q : Fin 4 → ℝ => (q 1 : ℂ) + (q 2 : ℂ) * Complex.I := by
      funext q; exact Complex.mk_eq_add_mul_I _ _
    rw [e]; fun_prop
  have continuous_kR : Continuous kR := Real.continuous_exp.comp (continuous_apply 3)
  have continuous_kS : Continuous kS := (continuous_apply 0).abs
  rw [continuous_iff_continuousAt]
  intro q₀
  by_cases hq₀ : q₀ 0 = 0
  · set c₀ := Real.circleAverage g (kW q₀) (kR q₀) with hc₀
    have hval : radialExt g q₀ = c₀ := by simp only [radialExt, hq₀, ↓reduceIte, hc₀]
    have hcont : ContinuousAt (fun p : ℂ × ℝ => Real.circleAverage g p.1 p.2) (kW q₀, kR q₀) :=
      hcA.continuousAt (prod_mem_nhds univ_mem (Ioi_mem_nhds (kR_pos q₀)))
    show Tendsto (radialExt g) (𝓝 q₀) (𝓝 (radialExt g q₀))
    rw [hval, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (half_pos hε)
    have h1 : ∀ᶠ q in 𝓝 q₀, dist (kW q, kR q) (kW q₀, kR q₀) < δ / 2 :=
      ((continuous_kW.prodMk continuous_kR).tendsto q₀).eventually
        (Metric.ball_mem_nhds _ (half_pos hδ))
    have hkS0 : kS q₀ = 0 := by simp [kS, hq₀]
    have h2 : ∀ᶠ q in 𝓝 q₀, kS q < δ / 2 :=
      (continuous_kS.tendsto q₀).eventually (gt_mem_nhds (by rw [hkS0]; exact half_pos hδ))
    filter_upwards [h1, h2] with q hq1 hq2
    by_cases hq : q 0 = 0
    · simp only [radialExt, hq, ↓reduceIte]
      exact (hδc (hq1.trans (half_lt_self hδ))).trans (half_lt_self hε)
    · simp only [radialExt, hq, ↓reduceIte]
      have hs : 0 < kS q := kS_pos hq
      rw [mollAvgS_ofFunC_eq hgm hgl, Real.dist_eq]
      have hcv : Continuous fun v : ℂ => Real.circleAverage g (kW q + v) (kR q) :=
        hcA.comp_continuous (f := fun v : ℂ => (kW q + v, kR q)) (by fun_prop)
          (fun _ => ⟨mem_univ _, kR_pos q⟩)
      refine (abs_integral_bumpS_mul_sub_le hcv hs (η := ε / 2) fun v hv => ?_).trans_lt
        (half_lt_self hε)
      rw [← Real.dist_eq]
      refine (@hδc (kW q + v, kR q) ?_).le
      have hv' : ‖v‖ ≤ kS q := mem_closedBall_zero_iff.1 hv
      rw [Prod.dist_eq] at hq1 ⊢
      have hw : dist (kW q) (kW q₀) < δ / 2 := (le_max_left _ _).trans_lt hq1
      have hr : dist (kR q) (kR q₀) < δ / 2 := (le_max_right _ _).trans_lt hq1
      have hwv : dist (kW q + v) (kW q₀) < δ := by
        calc dist (kW q + v) (kW q₀) ≤ dist (kW q + v) (kW q) + dist (kW q) (kW q₀) :=
              dist_triangle _ _ _
          _ < δ := by rw [dist_eq_norm, add_sub_cancel_left]; linarith
      exact max_lt hwv (hr.trans (half_lt_self hδ))
  · have hopen : IsOpen {q : Fin 4 → ℝ | q 0 ≠ 0} :=
      isOpen_ne_fun (continuous_apply 0) continuous_const
    have hmaps : MapsTo (fun q : Fin 4 → ℝ => (kS q, kW q, kR q)) {q : Fin 4 → ℝ | q 0 ≠ 0}
        (Ioi 0 ×ˢ univ) := fun q hq => mk_mem_prod (kS_pos hq) (mem_univ _)
    have hcm := (continuousOn_mollAvgS (ofFunC g)).comp
      (continuous_kS.prodMk (continuous_kW.prodMk continuous_kR)).continuousOn hmaps
    simp only [Function.comp_def] at hcm
    refine (hcm.continuousAt (hopen.mem_nhds hq₀)).congr ?_
    filter_upwards [hopen.mem_nhds hq₀] with q hq
    have hq' : ¬ q 0 = 0 := hq
    simp only [radialExt, hq', ↓reduceIte]

end MatedCRT.ConeAreaCovariance

end CircleAveragesOfRadialFunctions

section ScaleRegularity

open MeasureTheory Filter Topology Set Metric
open scoped Real NNReal ENNReal

namespace MatedCRT.ConeAreaCovariance

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord

/-- The mollified circle averages of a field in the parametrization `q = (s, Re w, Im w, log ρ)` of
`ScaleKolm`: `q ↦ ⨍_{∂B(w, ρ)} h(ψ_{|s|, ·})`. -/
def mollProc (h : DistC) (q : Fin 4 → ℝ) : ℝ := mollAvgS h (kS q) (kW q) (kR q)

/-- **Scale regularity**: the mollified circle averages of `h` extend continuously from the positive
scales to scale `0`. -/
def ScaleRegular (h : DistC) : Prop :=
  ∃ F : (Fin 4 → ℝ) → ℝ, Continuous F ∧ ∀ q : Fin 4 → ℝ, q 0 ≠ 0 → F q = mollProc h q

lemma continuous_kW : Continuous kW := by
  have e : kW = fun q : Fin 4 → ℝ => (q 1 : ℂ) + (q 2 : ℂ) * Complex.I := by
    funext q; exact Complex.mk_eq_add_mul_I _ _
  rw [e]; fun_prop

lemma continuous_kR : Continuous kR := Real.continuous_exp.comp (continuous_apply 3)

lemma continuous_kS : Continuous kS := (continuous_apply 0).abs

lemma continuousOn_mollProc (h : DistC) :
    ContinuousOn (mollProc h) {q : Fin 4 → ℝ | q 0 ≠ 0} := by
  refine (continuousOn_kProc (X := fun _ : Unit => h) ()).congr fun q hq => ?_
  have hq' : ¬ q 0 = 0 := hq
  simp only [kProc, hq', ↓reduceIte, mollProc]

lemma measurable_mollProc (q : Fin 4 → ℝ) : Measurable fun h : DistC => mollProc h q := by
  simp only [mollProc, mollAvgS_eq]
  exact measurable_distOn_apply _

/-- The scales `s ≠ 0` are dense in the parameter space. -/
lemma dense_scaleNonzero : Dense {q : Fin 4 → ℝ | q 0 ≠ 0} := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_cases hx : x 0 = 0
  · refine ⟨Function.update x 0 (ε / 2), ?_, ?_⟩
    · show Function.update x 0 (ε / 2) 0 ≠ 0
      rw [Function.update_self]
      exact (half_pos hε).ne'
    · refine lt_of_le_of_lt ((dist_pi_le_iff (half_pos hε).le).2 fun i => ?_) (half_lt_self hε)
      by_cases hi : i = 0
      · subst hi
        rw [Function.update_self, hx, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (half_pos hε)]
      · rw [Function.update_of_ne hi, dist_self]
        exact (half_pos hε).le
  · exact ⟨x, hx, by rw [dist_self]; exact hε⟩

/-! ## A countable description -/

/-- Pairs of rational parameter points of norm `< N` at distance `< 1/(m+1)`. -/
def ratPairs (N m : ℕ) : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)) :=
  {p | p.1 ∈ kDense ∧ p.2 ∈ kDense ∧ ‖p.1‖ < N ∧ ‖p.2‖ < N ∧ dist p.1 p.2 < 1 / ((m : ℝ) + 1)}

lemma ratPairs_countable (N m : ℕ) : (ratPairs N m).Countable := by
  refine (kDense_countable.prod kDense_countable).mono ?_
  intro p hp
  obtain ⟨h1, h2, -⟩ := hp
  exact mk_mem_prod h1 h2

/-- The countable uniform continuity condition on the rational parameter points. -/
def ScaleRegularRat (h : DistC) : Prop :=
  ∀ N n : ℕ, ∃ m : ℕ, ∀ p ∈ ratPairs N m, |mollProc h p.1 - mollProc h p.2| ≤ 1 / ((n : ℝ) + 1)

lemma measurableSet_scaleRegularRat : MeasurableSet {h : DistC | ScaleRegularRat h} := by
  have e : {h : DistC | ScaleRegularRat h} = ⋂ N : ℕ, ⋂ n : ℕ, ⋃ m : ℕ, ⋂ p ∈ ratPairs N m,
      {h : DistC | |mollProc h p.1 - mollProc h p.2| ≤ 1 / ((n : ℝ) + 1)} := by
    ext h
    simp only [ScaleRegularRat, mem_iInter, mem_iUnion, mem_ofPred_eq]
  rw [e]
  refine MeasurableSet.iInter fun N => MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m => ?_
  refine MeasurableSet.biInter (ratPairs_countable N m) fun p _ => ?_
  exact measurableSet_le (continuous_abs.measurable.comp
    ((measurable_mollProc p.1).sub (measurable_mollProc p.2))) measurable_const

lemma scaleRegularRat_of_scaleRegular {h : DistC} (hh : ScaleRegular h) : ScaleRegularRat h := by
  obtain ⟨F, hFc, hF⟩ := hh
  intro N n
  have huc := (isCompact_closedBall (0 : Fin 4 → ℝ) N).uniformContinuousOn_of_continuous
    hFc.continuousOn
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.1 huc (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m, fun p hp => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  rw [← hF _ h1.1, ← hF _ h2.1, ← Real.dist_eq]
  exact (hδF _ (mem_closedBall_zero_iff.2 h3.le) _ (mem_closedBall_zero_iff.2 h4.le)
    (h5.trans hm)).le

lemma uniformContinuousOn_mollProc_of_rat {h : DistC} (hh : ScaleRegularRat h) (N : ℕ) :
    UniformContinuousOn (mollProc h) ({q : Fin 4 → ℝ | q 0 ≠ 0} ∩ ball 0 N) := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨m, hm⟩ := hh N n
  refine ⟨1 / ((m : ℝ) + 1), by positivity, fun x hx y hy hxy => ?_⟩
  have hopen : IsOpen {q : Fin 4 → ℝ | q 0 ≠ 0} :=
    isOpen_ne_fun (continuous_apply 0) continuous_const
  have key : |mollProc h x - mollProc h y| ≤ 1 / ((n : ℝ) + 1) := by
    refine le_of_forall_pos_lt_add fun η hη => ?_
    set d := 1 / ((m : ℝ) + 1) - dist x y with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    have approx : ∀ z ∈ {q : Fin 4 → ℝ | q 0 ≠ 0} ∩ ball 0 N, ∃ z' ∈ kDense,
        ‖z'‖ < N ∧ dist z' z < d / 2 ∧ |mollProc h z' - mollProc h z| < η / 2 := by
      intro z hz
      have hcz : ContinuousAt (mollProc h) z :=
        (continuousOn_mollProc h).continuousAt (hopen.mem_nhds hz.1)
      have e1 : ∀ᶠ z' in 𝓝 z, ‖z'‖ < N :=
        (continuous_norm.tendsto z).eventually (gt_mem_nhds (mem_ball_zero_iff.1 hz.2))
      have e2 : ∀ᶠ z' in 𝓝 z, dist z' z < d / 2 := Metric.ball_mem_nhds z (half_pos hd0)
      have e3 : ∀ᶠ z' in 𝓝 z, |mollProc h z' - mollProc h z| < η / 2 := by
        filter_upwards [Metric.tendsto_nhds.1 hcz (η / 2) (half_pos hη)] with z' hz'
        rwa [Real.dist_eq] at hz'
      have hev : ∀ᶠ z' in 𝓝 z,
          ‖z'‖ < N ∧ dist z' z < d / 2 ∧ |mollProc h z' - mollProc h z| < η / 2 := by
        filter_upwards [e1, e2, e3] with z' a b c
        exact ⟨a, b, c⟩
      have hcl : z ∈ closure kDense := subset_closure_kDense hz.1
      obtain ⟨z', hz'D, hz'P⟩ := ((mem_closure_iff_frequently.1 hcl).and_eventually hev).exists
      exact ⟨z', hz'D, hz'P⟩
    obtain ⟨x', hx'D, hx'N, hx'd, hx'v⟩ := approx x hx
    obtain ⟨y', hy'D, hy'N, hy'd, hy'v⟩ := approx y hy
    have hpair : (x', y') ∈ ratPairs N m := by
      refine ⟨hx'D, hy'D, hx'N, hy'N, ?_⟩
      show dist x' y' < 1 / ((m : ℝ) + 1)
      have h4 := dist_triangle4 x' x y y'
      rw [dist_comm y y'] at h4
      linarith
    have hpv : |mollProc h x' - mollProc h y'| ≤ 1 / ((n : ℝ) + 1) := hm (x', y') hpair
    have t1 := abs_sub_le (mollProc h x) (mollProc h x') (mollProc h y)
    have t2 := abs_sub_le (mollProc h x') (mollProc h y') (mollProc h y)
    rw [abs_sub_comm] at hx'v
    linarith
  rw [Real.dist_eq]
  exact key.trans_lt hn

theorem scaleRegular_of_rat {h : DistC} (hh : ScaleRegularRat h) : ScaleRegular h := by
  set S := {q : Fin 4 → ℝ | q 0 ≠ 0} with hS
  have hlim : ∀ x : Fin 4 → ℝ, ∃ y, Tendsto (mollProc h) (𝓝[S] x) (𝓝 y) := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    have huc := uniformContinuousOn_mollProc_of_rat hh N
    have hball : ball (0 : Fin 4 → ℝ) N ∈ 𝓝 x := isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hN)
    have heq : 𝓝[S ∩ ball 0 N] x = 𝓝[S] x := by
      rw [inter_comm]
      exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hball)
    have hne : (𝓝[S ∩ ball 0 N] x).NeBot := by
      rw [heq]; exact mem_closure_iff_nhdsWithin_neBot.1 (dense_scaleNonzero x)
    have hcF : Cauchy (𝓝[S ∩ ball 0 N] x) := cauchy_nhds.mono nhdsWithin_le_nhds
    have hc : Cauchy (map (mollProc h) (𝓝[S ∩ ball 0 N] x)) :=
      hcF.map_of_le huc inf_le_right
    obtain ⟨y, hy⟩ := CompleteSpace.complete hc
    exact ⟨y, by rw [← heq]; exact hy⟩
  refine ⟨extendFrom S (mollProc h), ?_,
    fun q hq => extendFrom_extends (continuousOn_mollProc h) q hq⟩
  rw [← continuousOn_univ]
  exact continuousOn_extendFrom (fun x _ => dense_scaleNonzero x) fun x _ => hlim x

theorem scaleRegular_iff_rat (h : DistC) : ScaleRegular h ↔ ScaleRegularRat h :=
  ⟨scaleRegularRat_of_scaleRegular, scaleRegular_of_rat⟩

/-- **The scale-regular fields form a measurable set.** -/
theorem measurableSet_scaleRegular : MeasurableSet {h : DistC | ScaleRegular h} := by
  have e : {h : DistC | ScaleRegular h} = {h : DistC | ScaleRegularRat h} := by
    ext h; exact scaleRegular_iff_rat h
  rw [e]
  exact measurableSet_scaleRegularRat

/-! ## Circle averages of scale-regular fields -/

/-- The parameter point of scale `s`, centre `w` and radius `ρ`. -/
def scalePt (s : ℝ) (w : ℂ) (ρ : ℝ) : Fin 4 → ℝ := ![s, w.re, w.im, Real.log ρ]

lemma mollProc_scalePt (h : DistC) {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (w : ℂ) :
    mollProc h (scalePt s w ρ) = mollAvgS h s w ρ := by
  have e1 : kS (scalePt s w ρ) = s := by show |s| = s; exact abs_of_pos hs
  have e2 : kW (scalePt s w ρ) = w := Complex.eta w
  have e3 : kR (scalePt s w ρ) = ρ := by show Real.exp (Real.log ρ) = ρ; exact Real.exp_log hρ
  rw [mollProc, e1, e2, e3]

lemma continuous_scalePt (w : ℂ) (ρ : ℝ) : Continuous fun s => scalePt s w ρ := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [scalePt] <;> fun_prop

lemma tendsto_mollAvgS_of_scaleRegular {h : DistC} {F : (Fin 4 → ℝ) → ℝ} (hFc : Continuous F)
    (hF : ∀ q : Fin 4 → ℝ, q 0 ≠ 0 → F q = mollProc h q) {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) :
    Tendsto (fun s => mollAvgS h s w ρ) (𝓝[>] 0) (𝓝 (F (scalePt 0 w ρ))) := by
  have ht : Tendsto (fun s => F (scalePt s w ρ)) (𝓝[>] 0) (𝓝 (F (scalePt 0 w ρ))) :=
    ((hFc.comp (continuous_scalePt w ρ)).tendsto 0).mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (0 : ℝ) < s := hs
  have hne : scalePt s w ρ 0 ≠ 0 := by show s ≠ 0; exact hs'.ne'
  rw [hF _ hne, mollProc_scalePt h hs' hρ]

lemma circleAvg_eq_of_scaleRegular {h : DistC} {F : (Fin 4 → ℝ) → ℝ} (hFc : Continuous F)
    (hF : ∀ q : Fin 4 → ℝ, q 0 ≠ 0 → F q = mollProc h q) {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) :
    circleAvg h ρ w = F (scalePt 0 w ρ) :=
  circleAvg_eq_of_tendsto_mollAvgS (tendsto_mollAvgS_of_scaleRegular hFc hF hρ w)

/-- A scale-regular field has circle averages along every mollifier scale, at every centre. -/
theorem tendsto_mollAvgS_circleAvg_of_scaleRegular {h : DistC} (hh : ScaleRegular h) {ρ : ℝ}
    (hρ : 0 < ρ) (w : ℂ) :
    Tendsto (fun s => mollAvgS h s w ρ) (𝓝[>] 0) (𝓝 (circleAvg h ρ w)) := by
  obtain ⟨F, hFc, hF⟩ := hh
  rw [circleAvg_eq_of_scaleRegular hFc hF hρ w]
  exact tendsto_mollAvgS_of_scaleRegular hFc hF hρ w

theorem hasScaleCircleAvgs_of_scaleRegular {h : DistC} (hh : ScaleRegular h) :
    HasScaleCircleAvgs h :=
  fun _ hρ => Eventually.of_forall fun w => tendsto_mollAvgS_circleAvg_of_scaleRegular hh hρ w

/-- The circle averages of a scale-regular field are continuous on `(0, ∞) × ℂ`. -/
theorem continuousOn_circleAvg_of_scaleRegular {h : DistC} (hh : ScaleRegular h) :
    ContinuousOn (fun p : ℝ × ℂ => circleAvg h p.1 p.2) (Ioi 0 ×ˢ univ) := by
  obtain ⟨F, hFc, hF⟩ := hh
  have hc0 : ContinuousOn (fun p : ℝ × ℂ => scalePt 0 p.2 p.1) (Ioi 0 ×ˢ univ) := by
    refine continuousOn_pi.2 fun i => ?_
    fin_cases i
    · exact continuousOn_const
    · exact (Complex.continuous_re.comp continuous_snd).continuousOn
    · exact (Complex.continuous_im.comp continuous_snd).continuousOn
    · exact (Real.continuousOn_log.comp continuous_fst.continuousOn fun p hp =>
        (ne_of_gt (show (0 : ℝ) < p.1 from hp.1))).congr fun p _ => rfl
  refine (hFc.comp_continuousOn hc0).congr fun p hp => ?_
  exact circleAvg_eq_of_scaleRegular hFc hF hp.1 p.2

/-! ## Similarities -/

lemma mollAvgS_addConst (h : DistC) (c : ℝ) {s : ℝ} (hs : 0 < s) (w : ℂ) (ρ : ℝ) :
    mollAvgS (addConst h c) s w ρ = mollAvgS h s w ρ + c := by
  rw [mollAvgS_eq, mollAvgS_eq, addConst, addFun, _root_.add_apply, ofCont_apply]
  simp only [ContinuousMap.const_apply]
  rw [integral_mul_const, integral_circBumpS hs, one_mul]

lemma mollAvgS_affineComp (h : DistC) {r : ℝ} (hr : 0 < r) (z : ℂ) {s : ℝ} (hs : 0 < s) (w : ℂ)
    (ρ : ℝ) :
    mollAvgS (affineComp r z h) s w ρ = mollAvgS h (r * s) ((r : ℂ) * w + z) (r * ρ) := by
  simp only [mollAvgS, Real.circleAverage_def]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [affineComp_bumpS h hr hs]
  congr 2
  simp only [circleMap]
  push_cast
  ring

/-- The parameter map of the similarity `w ↦ r w + z`. -/
def affQ (r : ℝ) (z : ℂ) (q : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![r * q 0, ((r : ℂ) * kW q + z).re, ((r : ℂ) * kW q + z).im, q 3 + Real.log r]

lemma continuous_affQ (r : ℝ) (z : ℂ) : Continuous (affQ r z) := by
  have hw : Continuous fun q : Fin 4 → ℝ => (r : ℂ) * kW q + z :=
    (continuous_const.mul continuous_kW).add continuous_const
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_const.mul (continuous_apply 0)
  · exact Complex.continuous_re.comp hw
  · exact Complex.continuous_im.comp hw
  · exact (continuous_apply 3).add continuous_const

lemma mollProc_simField (h : DistC) {r : ℝ} (hr : 0 < r) (z : ℂ) (c : ℝ) {q : Fin 4 → ℝ}
    (hq : q 0 ≠ 0) :
    mollProc (addConst (affineComp r z h) c) q = mollProc h (affQ r z q) + c := by
  have hs : 0 < kS q := kS_pos hq
  have e1 : kS (affQ r z q) = r * kS q := by
    show |r * q 0| = r * |q 0|
    rw [abs_mul, abs_of_pos hr]
  have e2 : kW (affQ r z q) = (r : ℂ) * kW q + z := Complex.eta _
  have e3 : kR (affQ r z q) = r * kR q := by
    show Real.exp (q 3 + Real.log r) = r * Real.exp (q 3)
    rw [Real.exp_add, Real.exp_log hr, mul_comm]
  simp only [mollProc]
  rw [mollAvgS_addConst _ c hs, mollAvgS_affineComp h hr z hs, e1, e2, e3]

/-- **Scale regularity is invariant under the LQG coordinate changes** `h ↦ h(r · + z) + c`. -/
theorem scaleRegular_simField {h : DistC} (hh : ScaleRegular h) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (c : ℝ) : ScaleRegular (addConst (affineComp r z h) c) := by
  obtain ⟨F, hFc, hF⟩ := hh
  refine ⟨fun q => F (affQ r z q) + c, (hFc.comp (continuous_affQ r z)).add continuous_const,
    fun q hq => ?_⟩
  have hq' : affQ r z q 0 ≠ 0 := by
    show r * q 0 ≠ 0
    exact mul_ne_zero hr.ne' hq
  show F (affQ r z q) + c = _
  rw [hF _ hq', mollProc_simField h hr z c hq]

end MatedCRT.ConeAreaCovariance

end ScaleRegularity

section AreaLimitCondition

open MeasureTheory Filter Topology Set Metric
open scoped Real NNReal ENNReal

namespace MatedCRT.ConeAreaCovariance

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord

/-! ## Measurability and continuity in the radius -/

lemma measurable_integral_areaS (γ : ℝ) {s : ℝ} (hs : 0 ≤ s) {g : ℂ → ℝ} (hg : Measurable g) :
    Measurable fun h : DistC => ∫ z, g z ∂areaS γ h s := by
  have hd : Measurable (Function.uncurry fun (h : DistC) (z : ℂ) => densR γ h s z) := by
    have h1 : Measurable fun p : DistC × ℂ => circleAvg p.1 s p.2 :=
      measurable_circleAvg.comp (f := fun p : DistC × ℂ => (p.1, s, p.2))
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    exact measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul h1))
  exact LatticeProb.LQG.measurable_integral_withDensity_ofReal_uncurry_param hd
    (fun h z => densR_nonneg γ h hs z) (f := fun _ z => g z) (hg.comp measurable_snd)

variable {γ : ℝ} {h : DistC}

lemma continuousOn_densR
    (hc : ContinuousOn (fun p : ℝ × ℂ => circleAvg h p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × ℂ => densR γ h p.1 p.2) (Ioi 0 ×ˢ univ) := by
  have h1 : ContinuousOn (fun p : ℝ × ℂ => p.1 ^ (γ ^ 2 / 2)) (Ioi 0 ×ˢ univ) :=
    continuous_fst.continuousOn.rpow_const fun p hp => Or.inl (ne_of_gt hp.1)
  have h2 : ContinuousOn (fun p : ℝ × ℂ => Real.exp (γ * circleAvg h p.1 p.2)) (Ioi 0 ×ˢ univ) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hc)
  exact h1.mul h2

lemma continuous_densR
    (hc : ContinuousOn (fun p : ℝ × ℂ => circleAvg h p.1 p.2) (Ioi 0 ×ˢ univ)) {s : ℝ}
    (hs : 0 < s) : Continuous fun z => densR γ h s z :=
  (continuousOn_densR hc).comp_continuous (f := fun z : ℂ => (s, z))
    (continuous_const.prodMk continuous_id) fun _ => ⟨hs, mem_univ _⟩

lemma isFiniteMeasureOnCompacts_areaS
    (hc : ContinuousOn (fun p : ℝ × ℂ => circleAvg h p.1 p.2) (Ioi 0 ×ˢ univ)) {s : ℝ}
    (hs : 0 < s) : IsFiniteMeasureOnCompacts (areaS γ h s) := by
  refine ⟨fun K hK => ?_⟩
  show (volume.withDensity fun z => ENNReal.ofReal (densR γ h s z)) K < ⊤
  rw [withDensity_apply' _ K]
  exact ((continuous_densR hc hs).continuousOn.integrableOn_compact hK).lintegral_lt_top

/-- The continuum area approximations against a continuous compactly supported test function are
continuous in the radius when the circle averages are continuous. -/
lemma continuousOn_integral_areaS
    (hc : ContinuousOn (fun p : ℝ × ℂ => circleAvg h p.1 p.2) (Ioi 0 ×ˢ univ)) {g : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ContinuousOn (fun s => ∫ z, g z ∂areaS γ h s) (Ioi 0) := by
  have hD := continuousOn_densR (γ := γ) hc
  have hF : ContinuousOn (fun p : ℝ × ℂ => densR γ h p.1 p.2 * g p.2) (Ioi 0 ×ˢ univ) :=
    hD.mul (hg.comp continuous_snd).continuousOn
  intro s₀ hs₀
  have hs₀' : (0 : ℝ) < s₀ := hs₀
  set I := Icc (s₀ / 2) (2 * s₀) with hI
  have hIsub : I ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le (half_pos hs₀') hs.1
  set K := tsupport g with hK
  have hKc : IsCompact K := hgc.isCompact
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hKc).exists_bound_of_continuousOn
    (hF.mono fun p hp => ⟨hIsub hp.1, mem_univ _⟩)
  have hcont : ContinuousOn (fun s => ∫ z, densR γ h s z * g z) I := by
    refine continuousOn_of_dominated (bound := K.indicator fun _ => M) (fun s hs => ?_)
      (fun s hs => Eventually.of_forall fun z => ?_) ?_ (Eventually.of_forall fun z => ?_)
    · exact ((continuous_densR hc (hIsub hs)).mul hg).aestronglyMeasurable
    · by_cases hz : z ∈ K
      · rw [indicator_of_mem hz]
        exact hM (s, z) ⟨hs, hz⟩
      · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz, mul_zero, norm_zero]
    · exact (integrable_indicator_iff hKc.measurableSet).2
        (integrableOn_const hKc.measure_lt_top.ne)
    · exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
        fun s hs => ⟨hIsub hs, mem_univ _⟩
  have hI0 : I ∈ 𝓝 s₀ := Icc_mem_nhds (by linarith) (by linarith)
  refine ((hcont.continuousAt hI0).congr ?_).continuousWithinAt
  filter_upwards [hI0] with s hs
  exact (integral_areaS_eq γ h (hIsub hs).le g).symm

/-! ## Cauchy criteria along the rational radii -/

/-- The Cauchy condition of `f` at `0⁺` along the positive rationals. -/
def CauchyRat (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, ∀ s ∈ {q : ℚ | 0 < (q : ℝ) ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)},
    ∀ t ∈ {q : ℚ | 0 < (q : ℝ) ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)},
      |f s - f t| ≤ 1 / ((n : ℝ) + 1)

lemma measurableSet_cauchyRat {F : DistC → ℝ → ℝ}
    (hF : ∀ s : ℚ, 0 < (s : ℝ) → Measurable fun h => F h s) :
    MeasurableSet {h : DistC | CauchyRat (F h)} := by
  have e : {h : DistC | CauchyRat (F h)} = ⋂ n : ℕ, ⋃ m : ℕ,
      ⋂ s ∈ {q : ℚ | 0 < (q : ℝ) ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)},
      ⋂ t ∈ {q : ℚ | 0 < (q : ℝ) ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)},
        {h : DistC | |F h s - F h t| ≤ 1 / ((n : ℝ) + 1)} := by
    ext h
    simp only [CauchyRat, mem_iInter, mem_iUnion, mem_ofPred_eq]
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m => ?_
  refine MeasurableSet.biInter (to_countable _) fun s hs => MeasurableSet.biInter (to_countable _)
    fun t ht => ?_
  exact measurableSet_le (continuous_abs.measurable.comp ((hF s hs.1).sub (hF t ht.1)))
    measurable_const

lemma cauchyRat_of_tendsto {f : ℝ → ℝ} {ℓ : ℝ} (hf : Tendsto f (𝓝[>] 0) (𝓝 ℓ)) : CauchyRat f := by
  intro n
  obtain ⟨δ, hδ, hδf⟩ := Metric.tendsto_nhdsWithin_nhds.1 hf (1 / ((n : ℝ) + 1) / 2) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m, fun s hs t ht => ?_⟩
  have h1 := hδf (x := (s : ℝ)) hs.1 (by rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]; linarith [hs.2])
  have h2 := hδf (x := (t : ℝ)) ht.1 (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; linarith [ht.2])
  rw [Real.dist_eq] at h1 h2
  have := abs_sub_le (f s) ℓ (f t)
  rw [abs_sub_comm ℓ (f t)] at this
  linarith

lemma exists_tendsto_of_cauchyRat {f : ℝ → ℝ} (hfc : ContinuousOn f (Ioi 0)) (hf : CauchyRat f) :
    ∃ ℓ, Tendsto f (𝓝[>] 0) (𝓝 ℓ) := by
  -- the Cauchy bound along all real radii
  have hreal : ∀ n : ℕ, ∃ m : ℕ, ∀ s t : ℝ, 0 < s → s < 1 / ((m : ℝ) + 1) → 0 < t →
      t < 1 / ((m : ℝ) + 1) → |f s - f t| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨m, hm⟩ := hf n
    refine ⟨m, fun s t hs0 hs1 ht0 ht1 => ?_⟩
    refine le_of_forall_pos_lt_add fun η hη => ?_
    have approx : ∀ u : ℝ, 0 < u → u < 1 / ((m : ℝ) + 1) →
        ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < 1 / ((m : ℝ) + 1) ∧ |f q - f u| < η / 2 := by
      intro u hu0 hu1
      have hcu : ContinuousAt f u := hfc.continuousAt (Ioi_mem_nhds hu0)
      obtain ⟨ε, hε, hεf⟩ := Metric.continuousAt_iff.1 hcu (η / 2) (half_pos hη)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        (show max 0 (u - ε) < min (1 / ((m : ℝ) + 1)) (u + ε) from
          max_lt (lt_min (by positivity) (by linarith)) (lt_min (by linarith) (by linarith)))
      refine ⟨q, (le_max_left _ _).trans_lt hq1, hq2.trans_le (min_le_left _ _), ?_⟩
      rw [← Real.dist_eq]
      refine hεf ?_
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor
      · linarith [hq2.trans_le (min_le_right _ _)]
      · linarith [(le_max_right _ _).trans_lt hq1]
    obtain ⟨q, hq0, hq1, hqv⟩ := approx s hs0 hs1
    obtain ⟨q', hq'0, hq'1, hq'v⟩ := approx t ht0 ht1
    have hqq := hm q ⟨hq0, hq1⟩ q' ⟨hq'0, hq'1⟩
    have t1 := abs_sub_le (f s) (f q) (f t)
    have t2 := abs_sub_le (f q) (f q') (f t)
    rw [abs_sub_comm] at hqv
    linarith
  have hc : Cauchy (map f (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨m, hm⟩ := hreal n
    refine ⟨f '' Ioo 0 (1 / ((m : ℝ) + 1)),
      image_mem_map (Ioo_mem_nhdsGT (by positivity)), ?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [Real.dist_eq]
    exact (hm s t hs.1 hs.2 ht.1 ht.2).trans_lt hn
  exact cauchy_map_iff_exists_tendsto.1 hc

/-! ## The continuum area limit -/

/-- A fixed countable family of continuous compactly supported functions which determines vague
limits (`exists_countable_determining_vague_limit`). -/
def vagueD : Set (ℂ → ℝ) := (LatticeProb.VagueLimit.exists_countable_determining_vague_limit (X := ℂ)).choose

lemma vagueD_spec : vagueD.Countable ∧ (∀ g ∈ vagueD, Continuous g ∧ HasCompactSupport g) ∧
    ∀ m : ℕ → Measure ℂ, (∀ k, IsFiniteMeasureOnCompacts (m k)) →
      (∀ g ∈ vagueD, ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, g x ∂(m k)) atTop (𝓝 ℓ)) →
      ∃ μ : Measure ℂ, IsLocallyFiniteMeasure μ ∧ ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
        Tendsto (fun k => ∫ x, f x ∂(m k)) atTop (𝓝 (∫ x, f x ∂μ)) :=
  (LatticeProb.VagueLimit.exists_countable_determining_vague_limit (X := ℂ)).choose_spec

/-- Two locally finite measures with the same integrals on `vagueD` have the same integrals against
every continuous compactly supported function. -/
lemma integral_eq_of_vagueD {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (hμν : ∀ g ∈ vagueD, ∫ x, g x ∂μ = ∫ x, g x ∂ν) {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) : ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  classical
  set alt : ℕ → Measure ℂ := fun k => if Even k then μ else ν with halt
  have hfin : ∀ k, IsFiniteMeasureOnCompacts (alt k) := by
    intro k
    by_cases hk : Even k
    · simp only [halt, hk, ↓reduceIte]; infer_instance
    · simp only [halt, hk, ↓reduceIte]; infer_instance
  have hconv : ∀ g ∈ vagueD, ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, g x ∂(alt k)) atTop (𝓝 ℓ) := by
    intro g hg
    refine ⟨∫ x, g x ∂μ, tendsto_const_nhds.congr fun k => ?_⟩
    by_cases hk : Even k
    · simp only [halt, hk, ↓reduceIte]
    · simp only [halt, hk, ↓reduceIte]; exact hμν g hg
  obtain ⟨ρ, -, hρ⟩ := vagueD_spec.2.2 alt hfin hconv
  have hlim := hρ f hf hfc
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => show k ≤ 2 * k by omega) tendsto_id
  have h21 : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => show k ≤ 2 * k + 1 by omega) tendsto_id
  have e1 : ∫ x, f x ∂μ = ∫ x, f x ∂ρ := by
    refine tendsto_nhds_unique tendsto_const_nhds ((hlim.comp h2).congr fun k => ?_)
    simp only [Function.comp_apply, halt, even_two_mul, ↓reduceIte]
  have e2 : ∫ x, f x ∂ν = ∫ x, f x ∂ρ := by
    refine tendsto_nhds_unique tendsto_const_nhds ((hlim.comp h21).congr fun k => ?_)
    simp only [Function.comp_apply, halt, Nat.not_even_two_mul_add_one, ↓reduceIte]
  rw [e1, e2]

/-- **Existence of the continuum area limit from the Cauchy criteria on `vagueD`.** -/
theorem exists_hasAreaLimitS_of_cauchyRat
    (hc : ContinuousOn (fun p : ℝ × ℂ => circleAvg h p.1 p.2) (Ioi 0 ×ˢ univ))
    (hcau : ∀ g ∈ vagueD, CauchyRat (fun s => ∫ z, g z ∂areaS γ h s)) :
    ∃ μ, HasAreaLimitS γ h μ := by
  have hlimD : ∀ g ∈ vagueD, ∃ ℓ, Tendsto (fun s => ∫ z, g z ∂areaS γ h s) (𝓝[>] 0) (𝓝 ℓ) :=
    fun g hg => exists_tendsto_of_cauchyRat
      (continuousOn_integral_areaS hc (vagueD_spec.2.1 g hg).1 (vagueD_spec.2.1 g hg).2) (hcau g hg)
  -- the vague limit along any sequence of radii tending to `0`
  have hseq : ∀ u : ℕ → ℝ, Tendsto u atTop (𝓝[>] 0) → ∃ μ : Measure ℂ, IsLocallyFiniteMeasure μ ∧
      (∀ g ∈ vagueD, Tendsto (fun s => ∫ z, g z ∂areaS γ h s) (𝓝[>] 0) (𝓝 (∫ z, g z ∂μ))) ∧
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
        Tendsto (fun k => ∫ z, f z ∂areaS γ h (u k)) atTop (𝓝 (∫ z, f z ∂μ)) := by
    intro u hu
    have hpos : ∀ᶠ k in atTop, 0 < u k := (tendsto_nhdsWithin_iff.1 hu).2
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hpos
    set v : ℕ → ℝ := fun k => u (k + k₀) with hv
    have hv0 : ∀ k, 0 < v k := fun k => hk₀ _ (by omega)
    have hvt : Tendsto v atTop (𝓝[>] 0) := hu.comp (tendsto_add_atTop_nat k₀)
    have hfin : ∀ k, IsFiniteMeasureOnCompacts (areaS γ h (v k)) :=
      fun k => isFiniteMeasureOnCompacts_areaS hc (hv0 k)
    have hconv : ∀ g ∈ vagueD, ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, g x ∂(areaS γ h (v k))) atTop (𝓝 ℓ) :=
      fun g hg => by
        obtain ⟨ℓ, hℓ⟩ := hlimD g hg
        exact ⟨ℓ, hℓ.comp hvt⟩
    obtain ⟨μ, hμ, hμlim⟩ := vagueD_spec.2.2 (fun k => areaS γ h (v k)) hfin hconv
    refine ⟨μ, hμ, fun g hg => ?_, fun f hf hfc => ?_⟩
    · obtain ⟨ℓ, hℓ⟩ := hlimD g hg
      have hgv := hμlim g (vagueD_spec.2.1 g hg).1 (vagueD_spec.2.1 g hg).2
      rwa [tendsto_nhds_unique (hℓ.comp hvt) hgv] at hℓ
    · have := hμlim f hf hfc
      exact (this.comp (tendsto_sub_atTop_nat k₀)).congr' (eventually_atTop.2 ⟨k₀, fun k hk => by
        simp only [Function.comp_apply, hv, Nat.sub_add_cancel hk]⟩)
  obtain ⟨μ, hμ, hμD, hμlim⟩ := hseq dyadicScale tendsto_dyadicScale
  refine ⟨μ, fun K hK => hK.measure_lt_top, fun f hf hfc => ?_⟩
  refine tendsto_of_seq_tendsto fun u hu => ?_
  obtain ⟨ν, hν, hνD, hνlim⟩ := hseq u hu
  have heq : ∫ z, f z ∂ν = ∫ z, f z ∂μ :=
    integral_eq_of_vagueD (fun g hg => tendsto_nhds_unique (hνD g hg) (hμD g hg)) hf hfc
  rw [← heq]
  exact hνlim f hf hfc

/-- **The continuum area limit exists iff the countable Cauchy criteria hold** (for fields with
continuous circle averages). -/
theorem exists_hasAreaLimitS_iff
    (hc : ContinuousOn (fun p : ℝ × ℂ => circleAvg h p.1 p.2) (Ioi 0 ×ˢ univ)) :
    (∃ μ, HasAreaLimitS γ h μ) ↔ ∀ g ∈ vagueD, CauchyRat (fun s => ∫ z, g z ∂areaS γ h s) := by
  constructor
  · rintro ⟨μ, hμ⟩ g hg
    exact cauchyRat_of_tendsto (hμ.2 g (vagueD_spec.2.1 g hg).1 (vagueD_spec.2.1 g hg).2)
  · exact exists_hasAreaLimitS_of_cauchyRat hc

lemma measurableSet_cauchyRat_vagueD (γ : ℝ) :
    MeasurableSet {h : DistC | ∀ g ∈ vagueD, CauchyRat (fun s => ∫ z, g z ∂areaS γ h s)} := by
  have e : {h : DistC | ∀ g ∈ vagueD, CauchyRat (fun s => ∫ z, g z ∂areaS γ h s)} =
      ⋂ g ∈ vagueD, {h : DistC | CauchyRat (fun s => ∫ z, g z ∂areaS γ h s)} := by
    ext h
    simp only [mem_iInter, mem_ofPred_eq]
  rw [e]
  exact MeasurableSet.biInter vagueD_spec.1 fun g hg => measurableSet_cauchyRat fun s hs =>
    measurable_integral_areaS γ hs.le (vagueD_spec.2.1 g hg).1.measurable

/-! ## Similarities -/

/-- The continuum approximations of the transformed field, pushed forward by `w ↦ r w + z`, are
`e^{γc}` times the radius-`r s` approximations of `h`. -/
theorem map_areaS_simField (hγ : γ ≠ 0)
    (htr : ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      Tendsto (fun s => mollAvgS h s w ρ) (𝓝[>] 0) (𝓝 (circleAvg h ρ w)))
    {r : ℝ} (hr : 0 < r) (z : ℂ) (c : ℝ) {s : ℝ} (hs : 0 < s) :
    (areaS γ (addConst (affineComp r z h) (lqgQ γ * Real.log r + c)) s).map (affT hr z) =
      ENNReal.ofReal (Real.exp (γ * c)) • areaS γ h (r * s) := by
  have hrs : 0 < r * s := mul_pos hr hs
  have e1 : areaS γ (addConst (affineComp r z h) (lqgQ γ * Real.log r + c)) s =
      volume.withDensity fun w => ENNReal.ofReal (Real.exp (γ * c) * r ^ 2) *
        densS γ h (r * s) (DG.affineC r z w) := by
    unfold areaS
    refine withDensity_congr_ae ?_
    filter_upwards with w
    have hw := circleAvg_addConst_affineComp_of_tendsto hr (lqgQ γ * Real.log r + c)
      (htr (r * s) hrs ((r : ℂ) * w + z))
    rw [hw, densS, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hA : DG.affineC r z w = (r : ℂ) * w + z := rfl
    rw [hA, Real.mul_rpow hr.le hs.le]
    have hQ : Real.exp (γ * (lqgQ γ * Real.log r)) = r ^ (2 : ℝ) * r ^ (γ ^ 2 / 2) := by
      rw [← mul_assoc, gamma_mul_lqgQ hγ, ← Real.rpow_add hr, Real.rpow_def_of_pos hr]
      congr 1; ring
    have h2 : (r : ℝ) ^ 2 = r ^ (2 : ℝ) := by norm_cast
    rw [mul_add, mul_add, Real.exp_add, Real.exp_add, hQ, h2]
    ring
  rw [e1, show ⇑(affT hr z) = DG.affineC r z from rfl,
    map_withDensity_affineC' hr z (measurable_densS γ h (r * s))]
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- **The continuum area limit of the transformed field.** -/
theorem hasAreaLimitS_simField (hγ : γ ≠ 0)
    (htr : ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      Tendsto (fun s => mollAvgS h s w ρ) (𝓝[>] 0) (𝓝 (circleAvg h ρ w)))
    {μ : Measure ℂ} (hμ : HasAreaLimitS γ h μ) {r : ℝ} (hr : 0 < r) (z : ℂ) (c : ℝ) :
    HasAreaLimitS γ (addConst (affineComp r z h) (lqgQ γ * Real.log r + c))
      (ENNReal.ofReal (Real.exp (γ * c)) • μ.map (affT hr z).symm) := by
  set h' := addConst (affineComp r z h) (lqgQ γ * Real.log r + c)
  set T := affT hr z
  set e := ENNReal.ofReal (Real.exp (γ * c))
  have hmaps : ∀ s, 0 < s → areaS γ h' s = (e • areaS γ h (r * s)).map T.symm := by
    intro s hs
    rw [← map_areaS_simField hγ htr hr z c hs,
      Measure.map_map T.symm.measurable T.measurable, T.symm_comp_self, Measure.map_id]
  have hrs : Tendsto (fun s => r * s) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun s : ℝ => r * s) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul r
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hr hs
  constructor
  · intro K hK
    rw [Measure.smul_apply, smul_eq_mul, MeasurableEquiv.map_apply,
      ← MeasurableEquiv.image_eq_preimage_symm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμ.1 _ (hK.image (continuous_affT hr z)))
  · intro f hf hfc
    have hg : Continuous (f ∘ T.symm) := hf.comp (continuous_affT_symm hr z)
    have hgc : HasCompactSupport (f ∘ T.symm) := by
      have := hfc.comp_homeomorph ((Homeomorph.mulLeft₀ (r : ℂ) (by exact_mod_cast hr.ne')).trans
        (Homeomorph.addRight z)).symm
      simpa only [T, affT, DG.affineEquivC, Homeomorph.toMeasurableEquiv_symm_coe] using this
    have hlim := ((hμ.2 _ hg hgc).comp hrs).const_smul e.toReal
    have hval' : ∫ w, f w ∂(e • μ.map T.symm) = e.toReal • ∫ w, (f ∘ T.symm) w ∂μ := by
      rw [integral_smul_measure, integral_map_equiv]
      rfl
    rw [hval']
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Function.comp_apply, hmaps s hs, integral_map_equiv, integral_smul_measure]
    rfl

end MatedCRT.ConeAreaCovariance

end AreaLimitCondition

section AreaMap

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real NNReal ENNReal

namespace MatedCRT.ConeAreaCovariance

open LQGMetric LQGMetric.CircleAvg LQGMetric.TestIntegral MatedCRTHarmonic.CellScaling
open MatedCRTHarmonic.LQGCoord

/-! ## Scale regularity of sums and of radial functions -/

lemma mollProc_add (h₁ h₂ : DistC) (q : Fin 4 → ℝ) :
    mollProc (h₁ + h₂) q = mollProc h₁ q + mollProc h₂ q := by
  have e : ∀ T : DistC, mollProc T q = T (circBumpS (kS q) (kW q) (kR q)) :=
    fun T => mollAvgS_eq T (kS q) (kW q) (kR q)
  have hs : (h₁ + h₂) (circBumpS (kS q) (kW q) (kR q)) =
      h₁ (circBumpS (kS q) (kW q) (kR q)) + h₂ (circBumpS (kS q) (kW q) (kR q)) := rfl
  rw [e, e, e, hs]

lemma mollProc_sub (h₁ h₂ : DistC) (q : Fin 4 → ℝ) :
    mollProc (h₁ - h₂) q = mollProc h₁ q - mollProc h₂ q := by
  have e : ∀ T : DistC, mollProc T q = T (circBumpS (kS q) (kW q) (kR q)) :=
    fun T => mollAvgS_eq T (kS q) (kW q) (kR q)
  have hs : (h₁ - h₂) (circBumpS (kS q) (kW q) (kR q)) =
      h₁ (circBumpS (kS q) (kW q) (kR q)) - h₂ (circBumpS (kS q) (kW q) (kR q)) := rfl
  rw [e, e, e, hs]

lemma ScaleRegular.add {h₁ h₂ : DistC} (hh₁ : ScaleRegular h₁) (hh₂ : ScaleRegular h₂) :
    ScaleRegular (h₁ + h₂) := by
  obtain ⟨F₁, hF₁c, hF₁⟩ := hh₁
  obtain ⟨F₂, hF₂c, hF₂⟩ := hh₂
  refine ⟨fun q => F₁ q + F₂ q, hF₁c.add hF₂c, fun q hq => ?_⟩
  show F₁ q + F₂ q = _
  rw [mollProc_add, hF₁ q hq, hF₂ q hq]

lemma ScaleRegular.sub {h₁ h₂ : DistC} (hh₁ : ScaleRegular h₁) (hh₂ : ScaleRegular h₂) :
    ScaleRegular (h₁ - h₂) := by
  obtain ⟨F₁, hF₁c, hF₁⟩ := hh₁
  obtain ⟨F₂, hF₂c, hF₂⟩ := hh₂
  refine ⟨fun q => F₁ q - F₂ q, hF₁c.sub hF₂c, fun q hq => ?_⟩
  show F₁ q - F₂ q = _
  rw [mollProc_sub, hF₁ q hq, hF₂ q hq]

/-- A radial function, continuous off `0` and with a logarithmic singularity at `0`, defines a
scale-regular field. -/
theorem scaleRegular_ofFunC {g : ℂ → ℝ} (hg : IsRadial g) (hgm : Measurable g)
    (hgl : LocallyIntegrable g volume) (hgc : ContinuousOn g {0}ᶜ) (hgb : HasLogBound g) :
    ScaleRegular (ofFunC g) := by
  refine ⟨radialExt g, continuous_radialExt hg hgm hgl hgc hgb, fun q hq => ?_⟩
  have hq' : ¬ q 0 = 0 := hq
  simp only [radialExt, hq', ↓reduceIte, mollProc]

lemma hasLogBound_of {g : ℂ → ℝ} {a C : ℝ} (ha : 0 ≤ a)
    (hb : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → |g w| ≤ a * -Real.log ‖w‖ + C) : HasLogBound g := by
  refine ⟨a + |C|, by positivity, fun y hy0 hy1 => ?_⟩
  have hl := neg_log_pos hy0 hy1
  have h1 := hb y hy0 hy1
  nlinarith [mul_nonneg (abs_nonneg C) hl.le, le_abs_self C]

/-- **The cone field is scale regular** on the regularity event of its radial data, when the
whole-plane GFF is. -/
theorem scaleRegular_coneField {γ α : ℝ} {X : DistC} {b b' : ℝ≥0 → ℝ}
    (hr : RadialGood γ α X b b') (hX : ScaleRegular X) :
    ScaleRegular (MatedCRTHarmonic.CellScaling.coneField X (coneRadial γ α b b')) := by
  rw [coneField_eq_cone]
  have hc₁ := continuousOn_radialAvg hr.good
  have hc₂ := continuousOn_coneProfile hr
  obtain ⟨C₁, hC₁⟩ := abs_radialAvg_le hr one_pos
  obtain ⟨C₂, hC₂⟩ := abs_coneProfile_le hr one_pos
  have hm₂ := measurable_coneProfile hr
  have hrad₁ : IsRadial (radialAvg X) := fun u v huv => by
    show circleAvg X ‖u‖ 0 = circleAvg X ‖v‖ 0
    rw [huv]
  have hrad₂ : IsRadial (coneProfile γ α b b') := fun u v huv => by
    show coneRadial γ α b b' (-Real.log ‖u‖) = coneRadial γ α b b' (-Real.log ‖v‖)
    rw [huv]
  have h₁ : ScaleRegular (ofFunC (radialAvg X)) :=
    scaleRegular_ofFunC hrad₁ (measurable_radialAvg X)
      (locallyIntegrable_of_logBound (measurable_radialAvg X) hc₁ hC₁) hc₁
      (hasLogBound_of zero_le_one hC₁)
  have h₂ : ScaleRegular (ofFunC (coneProfile γ α b b')) :=
    scaleRegular_ofFunC hrad₂ hm₂
      (locallyIntegrable_of_logBound hm₂ hc₂ fun w h0 h1 => (hC₂ w h0 h1).1) hc₂
      (hasLogBound_of (by positivity) fun w h0 h1 => (hC₂ w h0 h1).1)
  exact (hX.sub h₁).add h₂

/-- **The whole-plane GFF is almost surely scale regular** (Kolmogorov–Čentsov in four parameters,
`ScaleKolm`). -/
theorem ae_scaleRegular_wp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) : ∀ᵐ ω ∂P, ScaleRegular (X ω) := by
  have := hX.gaussian.isProbabilityMeasure
  obtain ⟨Y, hYc, hYZ, -⟩ := QuantumZipper.KolmN.exists_continuous_modification_N
    (Z := kProc X) (fun q => (measurable_kProc hX q).aemeasurable) (p := 2 * 5)
    (by norm_num) (a := 5) (by norm_num) (momentBound_kProc hX)
  have hcount : Countable kDense := kDense_countable.to_subtype
  have hagree : ∀ᵐ ω ∂P, ∀ q : kDense, Y q ω = kProc X q ω :=
    ae_all_iff.2 fun q => hYZ q
  filter_upwards [hagree] with ω hω
  have heq : EqOn (fun q => Y q ω) (fun q => kProc X q ω) {q : Fin 4 → ℝ | q 0 ≠ 0} :=
    EqOn.of_subset_closure (s := kDense) (fun q hq => hω ⟨q, hq⟩)
      (hYc ω).continuousOn (continuousOn_kProc ω) (fun q hq => hq.1) subset_closure_kDense
  refine ⟨fun q => Y q ω, hYc ω, fun q hq => ?_⟩
  have hq' : ¬ q 0 = 0 := hq
  show Y q ω = mollProc (X ω) q
  rw [show Y q ω = kProc X q ω from heq hq]
  simp only [kProc, hq', ↓reduceIte, mollProc]

/-! ## The good set and the area map -/

/-- The fields whose mollified circle averages extend continuously to scale `0` and whose area
approximations `areaS γ h s` converge vaguely as `s → 0⁺`. -/
def goodSet (γ : ℝ) : Set DistC := {h | ScaleRegular h ∧ ∃ μ, HasAreaLimitS γ h μ}

theorem measurableSet_goodSet (γ : ℝ) : MeasurableSet (goodSet γ) := by
  have e : goodSet γ = {h : DistC | ScaleRegular h} ∩
      {h : DistC | ∀ g ∈ vagueD, CauchyRat (fun s => ∫ z, g z ∂areaS γ h s)} := by
    ext h
    constructor
    · rintro ⟨hh, hμ⟩
      exact ⟨hh, (exists_hasAreaLimitS_iff (γ := γ) (continuousOn_circleAvg_of_scaleRegular hh)).1 hμ⟩
    · rintro ⟨hh, hc⟩
      exact ⟨hh, (exists_hasAreaLimitS_iff (γ := γ) (continuousOn_circleAvg_of_scaleRegular hh)).2 hc⟩
  rw [e]
  exact measurableSet_scaleRegular.inter (measurableSet_cauchyRat_vagueD γ)

open Classical in
/-- **The area map**: the γ-LQG area measure on the good set, `0` elsewhere. -/
def areaMap (γ : ℝ) (h : DistC) : Measure ℂ :=
  if h ∈ goodSet γ then MatedCRTHarmonic.CellScaling.lqgArea γ h else 0

lemma areaMap_of_mem {γ : ℝ} {h : DistC} (hh : h ∈ goodSet γ) :
    areaMap γ h = MatedCRTHarmonic.CellScaling.lqgArea γ h := by
  unfold areaMap
  exact ite_eq_left hh

lemma areaMap_of_not_mem {γ : ℝ} {h : DistC} (hh : h ∉ goodSet γ) : areaMap γ h = 0 := by
  unfold areaMap
  exact ite_eq_right hh

lemma isVagueLimitC_of_hasAreaLimitS {γ : ℝ} {h : DistC} {μ : Measure ℂ}
    (hμ : HasAreaLimitS γ h μ) :
    MatedCRTHarmonic.CellScaling.IsVagueLimitC
      (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h) μ :=
  ⟨hμ.1, fun f hf hfc => (hμ.2 f hf hfc).comp MatedCRTHarmonic.LQGCoord.tendsto_dyadicScale⟩

/-- **The area map is Borel.** -/
theorem measurable_areaMap (γ : ℝ) : Measurable (areaMap γ) := by
  refine measurable_of_restrict_of_restrict_compl (measurableSet_goodSet γ) ?_ ?_
  · have hlim : ∀ h : goodSet γ, ∃ μ, MatedCRTHarmonic.CellScaling.IsVagueLimitC
        (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h.1) μ := by
      intro h
      obtain ⟨μ, hμ⟩ := h.2.2
      exact ⟨μ, isVagueLimitC_of_hasAreaLimitS hμ⟩
    have hinc : Measurable fun h : goodSet γ => (⟨h.1, hlim h⟩ :
        {h : DistC | ∃ μ, MatedCRTHarmonic.CellScaling.IsVagueLimitC
          (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h) μ}) :=
      measurable_subtype_coe.subtype_mk
    convert (LatticeProb.LQG.measurable_lqgArea_subtype γ).comp hinc using 1
    funext h
    simp only [Set.domRestrict_apply, Function.comp_apply]
    exact areaMap_of_mem h.2
  · convert (measurable_const : Measurable fun _ : ((goodSet γ)ᶜ : Set DistC) => (0 : Measure ℂ))
      using 1
    funext h
    simp only [Set.domRestrict_apply]
    exact areaMap_of_not_mem h.2

lemma affT_symm_apply {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    (affT hr z).symm w = ((r⁻¹ : ℝ) : ℂ) * (w - z) := by
  apply (affT hr z).injective
  rw [MeasurableEquiv.apply_symm_apply, affT_apply]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hr', one_mul, sub_add_cancel]

/-- **The deterministic coordinate change on the good set**: the area map is the dyadic vague limit,
and for every similarity `T w = C w + z` it maps `h(C · + z) + Q log C` to `(T⁻¹)_* (areaMap h)`. -/
theorem areaMap_spec {γ : ℝ} (hγ : γ ≠ 0) {h : DistC} (hh : h ∈ goodSet γ) :
    MatedCRTHarmonic.CellScaling.IsVagueLimitC (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h)
        (areaMap γ h) ∧
      ∀ C : ℝ, 0 < C → ∀ z : ℂ,
        areaMap γ (addConst (affineComp C z h) (lqgQ γ * Real.log C)) =
          (areaMap γ h).map fun w => ((C⁻¹ : ℝ) : ℂ) * (w - z) := by
  obtain ⟨hsr, μ, hμ⟩ := hh
  have hM : areaMap γ h = μ :=
    (areaMap_of_mem ⟨hsr, μ, hμ⟩).trans (lqgArea_eq_of_hasAreaLimitS hμ)
  refine ⟨?_, fun C hC z => ?_⟩
  · rw [hM]
    exact isVagueLimitC_of_hasAreaLimitS hμ
  · have htr : ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
        Tendsto (fun s => mollAvgS h s w ρ) (𝓝[>] 0) (𝓝 (circleAvg h ρ w)) :=
      fun ρ hρ w => tendsto_mollAvgS_circleAvg_of_scaleRegular hsr hρ w
    have hlim := hasAreaLimitS_simField hγ htr hμ hC z 0
    rw [add_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_smul] at hlim
    have hmem : addConst (affineComp C z h) (lqgQ γ * Real.log C) ∈ goodSet γ :=
      ⟨scaleRegular_simField hsr hC z _, _, hlim⟩
    rw [areaMap_of_mem hmem, lqgArea_eq_of_hasAreaLimitS hlim, hM]
    congr 1
    funext w
    exact affT_symm_apply hC z w

/-! ## The cone field lies in the good set almost surely -/

/-- The α-cone field is almost everywhere measurable (through the measurable continuous versions of
the Brownian motions and the measurable radial path `ConeScaling.radMap`). -/
theorem aemeasurable_coneField_alpha {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} {γ α : ℝ}
    (hαQ : α < MatedCRTHarmonic.CellScaling.lqgQ γ) (hX : IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P) :
    AEMeasurable (fun ω => MatedCRTHarmonic.CellScaling.coneField (X ω)
      (MatedCRTHarmonic.CellScaling.coneRadial γ α (fun t => B t ω) (fun t => B' t ω))) P := by
  obtain ⟨Bc, hBcm, hBc⟩ := MatedCRTHarmonic.ConeScaling.exists_continuousMap_version hB
  obtain ⟨Bc', hBc'm, hBc'⟩ := MatedCRTHarmonic.ConeScaling.exists_continuousMap_version hB'
  let W : Ω → C(ℝ, ℝ) := fun ω => MatedCRTHarmonic.ConeScaling.radMap γ α (Bc ω, Bc' ω)
  have hWm : Measurable W :=
    (MatedCRTHarmonic.ConeScaling.measurable_radMap γ α).comp (hBcm.prodMk hBc'm)
  have hW : ∀ᵐ ω ∂P, ∀ t, W ω t =
      MatedCRTHarmonic.CellScaling.coneRadial γ α (fun s => B s ω) (fun s => B' s ω) t := by
    filter_upwards [hBc, hBc', hB.eval_zero_ae_eq_zero, hB'.eval_zero_ae_eq_zero,
      MatedCRTHarmonic.CellScaling.ae_goodDrift hB' (sub_pos.2 hαQ)] with ω h1 h2 h3 h4 hdrift t
    have e1 : (⇑(Bc ω) : ℝ≥0 → ℝ) = fun s => B s ω := funext h1
    have e2 : (⇑(Bc' ω) : ℝ≥0 → ℝ) = fun s => B' s ω := funext h2
    have hmem : (Bc ω, Bc' ω) ∈ MatedCRTHarmonic.ConeScaling.radGood γ α := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h1]; exact h3
      · rw [h2]; exact h4
      · show BddAbove {s : ℝ | 0 ≤ s ∧ MatedCRTHarmonic.CellScaling.coneDrift γ α (⇑(Bc' ω)) s = 0}
        rw [e2]; exact hdrift.bddAbove_zeroSet
    show MatedCRTHarmonic.ConeScaling.radMap γ α (Bc ω, Bc' ω) t = _
    rw [MatedCRTHarmonic.ConeScaling.radMap_apply, ite_eq_left hmem]
    simp only [e1, e2]
  have hF : Measurable fun ω => MatedCRTHarmonic.ConeScaling.fieldOf
      (MatedCRTHarmonic.CellScaling.lateralPart (X ω)) (W ω) :=
    MatedCRTHarmonic.ConeScaling.measurable_fieldOf.comp
      ((MatedCRTHarmonic.ConeScaling.measurable_lateralPart.comp hX.measurable).prodMk hWm)
  refine hF.aemeasurable.congr ?_
  filter_upwards [hW] with ω hω
  exact (MatedCRTHarmonic.IGLaw.coneField_eq_fieldOf_alpha γ α (X ω) hω).symm

/-- **The α-cone field lies in the good set almost surely** (`0 < γ < 2`, `α < Q`). -/
theorem ae_coneField_mem_goodSet {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hαQ : α < MatedCRTHarmonic.CellScaling.lqgQ γ) (hX : IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, MatedCRTHarmonic.CellScaling.coneField (X ω)
      (MatedCRTHarmonic.CellScaling.coneRadial γ α (fun t => B t ω) (fun t => B' t ω)) ∈
        goodSet γ := by
  filter_upwards [ae_radialGood hX hB hB' hαQ, ae_hasScaleCircleAvgs_wp hX,
    ae_hasAreaLimitS_wp hX hγ hγ2,
    ae_tight_wp hX hγ hγ2 (le_max_left _ _) (coneExp_lt hγ hαQ), ae_scaleRegular_wp hX] with
    ω hr hs ha ht hsr
  have hc := coneGood_of hαQ hr hs ha ht
  refine ⟨scaleRegular_coneField hr hsr, ?_⟩
  rw [coneField_eq_cone]
  exact ⟨_, hasAreaLimitS_cone hγ hc⟩

end MatedCRT.ConeAreaCovariance

namespace MatedCRT

/-- **The simultaneous LQG coordinate change of the area measure of the `0`-quantum cone.** -/
theorem zeroConeAreaCoordinateChange (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ZeroConeAreaCoordinateChange γ hγ := by
  refine ⟨ConeAreaCovariance.areaMap γ, ConeAreaCovariance.measurable_areaMap γ, ?_⟩
  intro Ω' _ P' X₀' b b' _ hX hb hb' _ _
  have hQ : (0 : ℝ) < MatedCRTHarmonic.CellScaling.lqgQ γ :=
    MatedCRTHarmonic.LQGCoord.lqgQ_pos hγ.1
  have hfm : AEMeasurable (zeroConeFieldOf γ X₀' b b') P' :=
    ConeAreaCovariance.aemeasurable_coneField_alpha hQ hX hb hb'
  have hae : ∀ᵐ ω ∂P', zeroConeFieldOf γ X₀' b b' ω ∈ ConeAreaCovariance.goodSet γ :=
    ConeAreaCovariance.ae_coneField_mem_goodSet hγ.1 hγ.2 hQ hX hb hb'
  have hgood : ∀ᵐ h ∂P'.map (zeroConeFieldOf γ X₀' b b'), h ∈ ConeAreaCovariance.goodSet γ :=
    (ae_map_iff hfm (ConeAreaCovariance.measurableSet_goodSet γ)).2 hae
  filter_upwards [hgood] with h hh
  exact ConeAreaCovariance.areaMap_spec hγ.1.ne' hh

end MatedCRT

end AreaMap
