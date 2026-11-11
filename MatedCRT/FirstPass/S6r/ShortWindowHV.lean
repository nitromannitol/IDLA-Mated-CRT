import MatedCRT.FirstPass.S6r.ShortWindowDerived
import MatedCRT.FirstPass.S6r.ShortWindowH0
import MatedCRT.FirstPass.S2VG.Literature
import MatedCRT.Steps.Sec6.AnnulusHit
import HarmonicBalls.Proofs.GFF.CircleAverageLognormalMoments

/-!
# `hV = WholePlaneUpperVolumeTailStep`, derived from the ball-mass input

The upper volume tail
of the whole-plane LQG measure follows from three inputs:
* `LitWholePlaneBallMass` (Ding-Gwynne, arXiv:1807.01072, Lemma 3.8, eq. (3.14)): the ball masses of the unit square
  are at most `ε` with polynomially high probability, for the normalized whole-plane field;
* `LitCoordChange` (Duplantier-Sheffield 2011, Prop. 2.1), through its explicit affine form
  `sdw_affineCoordChange_explicit`: for `T x = (x - z)/r`, `(μ.map T) = e^{γκ} • μ''` almost surely, where
  `κ = h_r(z) + Q log r` and `μ''` is the LQG measure of the normalized whole-plane field;
* the first lognormal moment of the circle average (`IsWholePlaneGFF.lintegral_circleAverage_lognormal_rpow_eq`,
  Harmonic-Balls `Proofs/GFF/CircleAverageLognormalMoments`), which gives the tail `P(e^{γκ} ≥ t) ≤ K/t` by Markov.
  No Gaussian tail bound is needed, since only some exponent `q > 0` is required.

The affine map is `S x = (x + 4 + 4i)/8`, with `S(B_3) ⊆ [0,1]²` and `S(B_s(z)) = B_{s/8}(S z)`.
Notation: Armstrong-Kuusi-Mourrat (cone and ball notation), Duplantier-Sheffield (LQG measure, coordinate change).
-/

open MeasureTheory Filter Topology Metric HarmonicBalls ProbabilityTheory Set
open scoped ENNReal
open MatedCRT.Lemma68Window

namespace MatedCRT.ShortWindowHV

/-- The normalization at `α₀ = 0` is the identity on circle-average families. -/
theorem fieldCircleAverage_zero_eq (h : ℝ → ℂ → ℝ) : fieldCircleAverage 0 h = h := by
  funext ε x
  simp [fieldCircleAverage]

/-- The coordinate-change constant at a positive radius: `κ = h_r(z) + Q log r`. -/
theorem coordKappa_eq_of_pos (γ r : ℝ) (hr : 0 < r) (z : ℂ) (h : ℝ → ℂ → ℝ) :
    sdw_coordKappa γ r z h = h r z + lqgQ γ * Real.log r := by
  unfold sdw_coordKappa
  rw [Complex.norm_real, Real.norm_of_nonneg hr.le]

/-- **Explicit affine coordinate change.** For a whole-plane GFF `(hC, hcirc)` with LQG measure
`μ` and `r > 0`, the push-forward of `μ` under `x ↦ (x - z)/r` is `e^{γκ}` times the LQG measure `μ''` of the
normalized whole-plane field `h(r · + z) - κ`, where `κ = h_r(z) + Q log r`. The multiplier is kept explicit. The proof
is that of `wholePlaneLQGCoordinateChangeStep_of_coordChange` (`ShortWindowDerived.lean:85`), with the multiplier
`c = e^{γκ}` stated instead of hidden in an existential. -/
theorem sdw_affineCoordChange_explicit (hCC : MatedCRT.S2VG.LitCoordChange) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hwp : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (r : ℝ) (hr : 0 < r) (z : ℂ) :
    ∃ (hC'' : Ω → (ℂ → ℝ) → ℝ) (hcirc'' : Ω → ℝ → ℂ → ℝ) (μ'' : Ω → Measure ℂ),
      IsWholePlaneGFF P hC'' hcirc'' ∧ IsLQGMeasure P γ hcirc'' μ'' ∧
      ∀ᵐ ω ∂P, (μ ω).map (fun x => (x - z) / (r : ℂ)) =
        ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ r z (hcirc ω))) • μ'' ω := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hQ : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    positivity
  have hfield : IsLQGMeasureOfField P γ 0 hcirc μ := by
    unfold IsLQGMeasureOfField
    simp only [fieldCircleAverage_zero_eq]
    exact hμ
  have hA := hCC Ω P γ hC hcirc hwp hγ hγ2 hQ μ hfield
  have hG := HarmonicBalls.wholePlaneGFFAffineInvariance_proved P hC hcirc hwp (r : ℂ) hr0 z
  refine ⟨_, _, fun ω => ENNReal.ofReal (Real.exp (-(γ * sdw_coordKappa γ r z (hcirc ω)))) •
      (μ ω).map (fun x => (x - z) / (r : ℂ)), hG, ?_, ?_⟩
  · filter_upwards [hA] with ω hω
    have h1 := hω (r : ℂ) hr0 z
    apply sdw_isLQGLimit_shift
    convert h1 using 1
    funext ε w
    simp only [fieldCircleAverage, sdw_coordKappa, zero_mul, sub_zero]
    ring
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [smul_smul, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      ENNReal.ofReal_one, one_smul]

/-- Preimage of a ball under the affine map `x ↦ (x - z)/r`: `S(B_s(w)) = B_{s/r}(S w)` for `S x = (x - z)/r`. -/
theorem preimage_affine_ball (z w : ℂ) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    (fun x : ℂ => (x - z) / (r : ℂ)) ⁻¹' ball ((w - z) / (r : ℂ)) (s / r) = ball w s := by
  ext x
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have key : (x - z) / (r : ℂ) - (w - z) / (r : ℂ) = (x - w) / (r : ℂ) := by ring
  simp only [mem_preimage, mem_ball, dist_eq_norm, key, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  exact div_lt_div_iff_of_pos_right hr

/-- The affine image of the ball `B_3` lies in the unit square `[0,1]²` for `b = -4 - 4i`, `r = 8`. -/
theorem affine_mem_unitSquare {b : ℂ} (hb : b = -4 - 4 * Complex.I) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 3) :
    (z - b) / ((8 : ℝ) : ℂ) ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := by
  have h : ‖z‖ < 3 := by simpa using hz
  have hre : |z.re| < 3 := lt_of_le_of_lt (Complex.abs_re_le_norm z) h
  have him : |z.im| < 3 := lt_of_le_of_lt (Complex.abs_im_le_norm z) h
  rw [abs_lt] at hre him
  have hbre : b.re = -4 := by rw [hb]; norm_num
  have hbim : b.im = -4 := by rw [hb]; norm_num
  rw [Complex.mem_reProdIm, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
    hbre, hbim, mem_Icc, mem_Icc]
  constructor <;> constructor <;> linarith [hre.1, hre.2, him.1, him.2]

/-- **Markov tail of the normalizing factor (lognormal first moment).** For a whole-plane GFF and `r > 0`, the event
`{e^{γκ} ≥ t}` with `κ = h_r(z) + Q log r` has probability at most `K/t` for a constant `K` independent of `t`. -/
theorem coordFactor_markov (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (hgff : IsWholePlaneGFF P hC hcirc) (γ : ℝ) (r : ℝ) (hr : 0 < r)
    (z : ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t →
      P {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ r z (hcirc ω)))} ≤
        ENNReal.ofReal (K / t) := by
  have hm : Measurable (fun ω => hcirc ω r z) := hgff.measurable_circle r z hr
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = Real.exp (γ * (lqgQ γ * Real.log r)) := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; exact Real.exp_pos _
  have hV0 : 0 < Real.exp ((1 * γ) ^ 2 * variance (fun ω => hcirc ω r z) P / 2) := Real.exp_pos _
  refine ⟨k * Real.exp ((1 * γ) ^ 2 * variance (fun ω => hcirc ω r z) P / 2), by positivity, fun t ht => ?_⟩
  have hfac : ∀ ω, ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ r z (hcirc ω))) =
      ENNReal.ofReal k * ENNReal.ofReal (Real.exp (γ * hcirc ω r z)) := by
    intro ω
    rw [coordKappa_eq_of_pos γ r hr z, ← ENNReal.ofReal_mul hk0.le, hk, ← Real.exp_add]
    congr 2
    ring
  have hlin : ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * hcirc ω r z)) ∂P =
      ENNReal.ofReal (Real.exp ((1 * γ) ^ 2 * variance (fun ω => hcirc ω r z) P / 2)) := by
    have h := hgff.lintegral_circleAverage_lognormal_rpow_eq hr z γ 1
    simp only [Real.rpow_one] at h
    exact h
  have hmeas : Measurable (fun ω => ENNReal.ofReal k * ENNReal.ofReal (Real.exp (γ * hcirc ω r z))) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (hm.const_mul γ)))
  have hset : {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ r z (hcirc ω)))} =
      {ω | ENNReal.ofReal t ≤ ENNReal.ofReal k * ENNReal.ofReal (Real.exp (γ * hcirc ω r z))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hfac ω]
  rw [hset]
  refine (meas_ge_le_lintegral_div hmeas.aemeasurable (ε := ENNReal.ofReal t)
    (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top).trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hlin, ← ENNReal.ofReal_mul hk0.le,
    ENNReal.ofReal_div_of_pos ht]

/-- **Affine ball-mass transfer and the upper volume tail (`hV` derived).** Under the cited
ball-mass bounds `LitWholePlaneBallMass` and the cited coordinate change `LitCoordChange`, the whole-plane upper
volume tail `WholePlaneUpperVolumeTailStep` holds: `μ(B_s(z)) ≤ s^{α/2}` for all `z ∈ B_3`, outside an event of
probability `O(s^q)`. -/
theorem wholePlaneUpperVolumeTailStep_of_ballMass (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) : MatedCRT.WholePlaneUpperVolumeTailStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hgff hμ
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = -4 - 4 * Complex.I := ⟨_, rfl⟩
  obtain ⟨hC'', hcirc'', μ'', hgff'', hμ'', hrel⟩ :=
    sdw_affineCoordChange_explicit hCC γ hγ hγ2 Ω P hC hcirc μ hgff hμ 8 (by norm_num) b
  have hμ0 : IsLQGMeasureOfField P γ 0 hcirc'' μ'' := by
    unfold IsLQGMeasureOfField
    simp only [fieldCircleAverage_zero_eq]
    exact hμ''
  obtain ⟨βu, hβu_def⟩ : ∃ x : ℝ, x = 2 / (2 - γ) ^ 2 + 1 := ⟨_, rfl⟩
  have hβu_pos : 0 < βu := by rw [hβu_def]; positivity
  have hβu1 : 2 / (2 - γ) ^ 2 < βu := by rw [hβu_def]; linarith
  have hβl0 : (0 : ℝ) < 1 / (2 + γ) ^ 2 := by positivity
  have hβl1 : 1 / (2 + γ) ^ 2 < 2 / (2 + γ) ^ 2 := by
    apply div_lt_div_of_pos_right (by norm_num) (by positivity)
  obtain ⟨p, hp, C, ρ₀, hρ₀, hpoly⟩ :=
    hBM Ω P γ hC'' hcirc'' hgff'' hγ hγ2 μ'' hμ0 (1 / (2 + γ) ^ 2) βu hβl0 hβl1 hβu1
  obtain ⟨K1, hK1, htail⟩ := coordFactor_markov Ω P hC hcirc hgff γ 8 (by norm_num) b
  obtain ⟨α, hα⟩ : ∃ x : ℝ, x = 1 / βu := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  have hαβ : α * βu = 1 := by rw [hα]; exact one_div_mul_cancel hβu_pos.ne'
  refine ⟨α / 2, min (α / 2) (α * p), K1 + |C|, min 1 (8 * ρ₀ ^ (1 / α)), by positivity,
    lt_min (by positivity) (mul_pos hα0 hp), lt_min one_pos (mul_pos (by norm_num)
      (Real.rpow_pos_of_pos hρ₀ _)), ?_⟩
  intro s hs hsr
  have hs1 : s < 1 := lt_of_lt_of_le hsr (min_le_left _ _)
  have hs8 : s < 8 * ρ₀ ^ (1 / α) := lt_of_lt_of_le hsr (min_le_right _ _)
  have hεpos : 0 < (s / 8) ^ α := Real.rpow_pos_of_pos (by positivity) α
  have hεlt : (s / 8) ^ α < ρ₀ := by
    calc (s / 8) ^ α < (ρ₀ ^ (1 / α)) ^ α :=
          Real.rpow_lt_rpow (by positivity) (by linarith) hα0
      _ = ρ₀ := by rw [← Real.rpow_mul hρ₀.le, one_div_mul_cancel hα0.ne', Real.rpow_one]
  have hεβ : ((s / 8) ^ α) ^ βu = s / 8 := by
    rw [← Real.rpow_mul (by positivity), hαβ, Real.rpow_one]
  -- the good event of the cited ball-mass bound at radius `ε = (s/8)^α` (the set of `WholePlaneLQGBallMassBounds`)
  obtain ⟨Eset, hEset⟩ : ∃ E : ℝ → Set Ω, E = fun ε => {ω | (∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      ENNReal.ofReal ε ≤ μ'' ω (ball z (ε ^ (1 / (2 + γ) ^ 2)))) ∧
      ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, μ'' ω (ball z (ε ^ βu)) ≤ ENNReal.ofReal ε} := ⟨_, rfl⟩
  have hPε : P (Eset ((s / 8) ^ α))ᶜ ≤ ENNReal.ofReal (C * ((s / 8) ^ α) ^ p) := by
    rw [hEset]
    exact hpoly _ hεpos hεlt
  -- the affine transform and the coordinate factor
  obtain ⟨T, hT⟩ : ∃ T : ℂ → ℂ, T = fun x => (x - b) / ((8 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hTm : Measurable T := by
    rw [hT]
    exact (measurable_id.sub_const b).div_const _
  have hN : P {ω | ¬ ((μ ω).map T =
      ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω))) • μ'' ω)} = 0 := by
    rw [hT]
    exact ae_iff.mp hrel
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = s ^ (-(α / 2)) := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; exact Real.rpow_pos_of_pos hs _
  -- per-point bound on the good event
  have hpt : ∀ ω, (μ ω).map T =
      ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω))) • μ'' ω →
      ¬ (ENNReal.ofReal t ≤ ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω)))) →
      ω ∈ Eset ((s / 8) ^ α) → ∀ z ∈ ball (0 : ℂ) 3, μ ω (ball z s) ≤ ENNReal.ofReal (s ^ (α / 2)) := by
    intro ω hrelω hlt hE z hz
    rw [hEset] at hE
    have hball : ball z s = T ⁻¹' ball ((z - b) / ((8 : ℝ) : ℂ)) (s / 8) := by
      rw [hT]
      exact (preimage_affine_ball b z (by norm_num) s).symm
    have hmem := affine_mem_unitSquare hb hz
    have hμ'' : μ'' ω (ball ((z - b) / ((8 : ℝ) : ℂ)) (s / 8)) ≤ ENNReal.ofReal ((s / 8) ^ α) := by
      have h2 := hE.2 _ hmem
      rwa [hεβ] at h2
    have hc : ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω))) ≤ ENNReal.ofReal t :=
      (not_le.mp hlt).le
    have hnum : t * (s / 8) ^ α ≤ s ^ (α / 2) := by
      have h1 : (s / 8) ^ α ≤ s ^ α := Real.rpow_le_rpow (by positivity) (by linarith) hα0.le
      calc t * (s / 8) ^ α ≤ t * s ^ α := mul_le_mul_of_nonneg_left h1 ht.le
        _ = s ^ (α / 2) := by
          rw [ht_def, ← Real.rpow_add hs]
          congr 1
          ring
    rw [hball, ← Measure.map_apply hTm measurableSet_ball, hrelω, Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω))) *
          μ'' ω (ball ((z - b) / ((8 : ℝ) : ℂ)) (s / 8))
        ≤ ENNReal.ofReal t * ENNReal.ofReal ((s / 8) ^ α) := mul_le_mul' hc hμ''
      _ = ENNReal.ofReal (t * (s / 8) ^ α) := (ENNReal.ofReal_mul ht.le).symm
      _ ≤ ENNReal.ofReal (s ^ (α / 2)) := ENNReal.ofReal_le_ofReal hnum
  -- the complement of the good set is contained in the three bad events
  have hsub : {ω | ∀ z ∈ ball (0 : ℂ) 3, μ ω (ball z s) ≤ ENNReal.ofReal (s ^ (α / 2))}ᶜ ⊆
      ({ω | ¬ ((μ ω).map T =
        ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω))) • μ'' ω)} ∪
        {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω)))}) ∪
        (Eset ((s / 8) ^ α))ᶜ := by
    intro ω hω
    by_contra hcon
    apply hω
    have hrelω : (μ ω).map T =
        ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω))) • μ'' ω := by
      by_contra h
      exact hcon (Or.inl (Or.inl h))
    have hlt : ¬ (ENNReal.ofReal t ≤ ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω)))) :=
      fun h => hcon (Or.inl (Or.inr h))
    have hE : ω ∈ Eset ((s / 8) ^ α) := by
      by_contra h
      exact hcon (Or.inr h)
    exact hpt ω hrelω hlt hE
  -- the numerical bounds
  have hq1 : s ^ (α / 2) ≤ s ^ (min (α / 2) (α * p)) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1.le (min_le_left _ _)
  have htinv : K1 / t = K1 * s ^ (α / 2) := by
    rw [ht_def, Real.rpow_neg hs.le, div_inv_eq_mul]
  have hεp : ((s / 8) ^ α) ^ p ≤ s ^ (min (α / 2) (α * p)) := by
    rw [← Real.rpow_mul (by positivity)]
    calc (s / 8) ^ (α * p) ≤ s ^ (α * p) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ ≤ s ^ (min (α / 2) (α * p)) := Real.rpow_le_rpow_of_exponent_ge hs hs1.le (min_le_right _ _)
  have hε0 : 0 ≤ ((s / 8) ^ α) ^ p := by positivity
  have hK1s : 0 ≤ K1 * s ^ (min (α / 2) (α * p)) := mul_nonneg hK1 (Real.rpow_nonneg hs.le _)
  have hCs : 0 ≤ |C| * s ^ (min (α / 2) (α * p)) := mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hs.le _)
  have hE2 : P ({ω | ¬ ((μ ω).map T =
        ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω))) • μ'' ω)} ∪
        {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω)))})
        ≤ ENNReal.ofReal (K1 * s ^ (min (α / 2) (α * p))) := by
    refine (measure_union_le _ _).trans ?_
    rw [hN, zero_add]
    refine (htail t ht).trans ?_
    exact ENNReal.ofReal_le_ofReal (by rw [htinv]; exact mul_le_mul_of_nonneg_left hq1 hK1)
  have hF : P (Eset ((s / 8) ^ α))ᶜ ≤ ENNReal.ofReal (|C| * s ^ (min (α / 2) (α * p))) :=
    hPε.trans (ENNReal.ofReal_le_ofReal (by
      calc C * ((s / 8) ^ α) ^ p ≤ |C| * ((s / 8) ^ α) ^ p :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hε0
        _ ≤ |C| * s ^ (min (α / 2) (α * p)) := mul_le_mul_of_nonneg_left hεp (abs_nonneg C)))
  calc P {ω | ∀ z ∈ ball (0 : ℂ) 3, μ ω (ball z s) ≤ ENNReal.ofReal (s ^ (α / 2))}ᶜ
      ≤ P (({ω | ¬ ((μ ω).map T =
        ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω))) • μ'' ω)} ∪
        {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω)))}) ∪
        (Eset ((s / 8) ^ α))ᶜ) := measure_mono hsub
    _ ≤ P ({ω | ¬ ((μ ω).map T =
        ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω))) • μ'' ω)} ∪
        {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (Real.exp (γ * sdw_coordKappa γ 8 b (hcirc ω)))}) +
        P (Eset ((s / 8) ^ α))ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (K1 * s ^ (min (α / 2) (α * p))) + ENNReal.ofReal (|C| * s ^ (min (α / 2) (α * p))) :=
        add_le_add hE2 hF
    _ = ENNReal.ofReal ((K1 + |C|) * s ^ (min (α / 2) (α * p))) := by
        rw [← ENNReal.ofReal_add hK1s hCs, ← add_mul]

/-- **`hprev_of_shortWindow_noH0` with `hV` discharged.**
The frozen input `hV : FPWholePlaneUpperVolumeTail` of `hprev_of_shortWindow_noH0` (`ShortWindowH0.lean:62`) is replaced
by `wholePlaneUpperVolumeTailStep_of_ballMass hBM hCC`. The frozen Prop `FPWholePlaneUpperVolumeTail` is by definition
`WholePlaneUpperVolumeTailStep` (`FirstPass/Frozen/S5S6S7.lean:38`), so the term is accepted without a conversion.
The remaining binders are `hE` (`LitExistence`, for `h0`), `hBM` and `hCC` (the two cited inputs of `hV`), `hB1` and `hμ`,
as in `hprev_of_shortWindow_noH0`. -/
theorem hprev_of_shortWindow_noH0V (hE : MatedCRT.S2VG.LitExistence)
    (hBM : MatedCRT.S2VG.LitWholePlaneBallMass) (hCC : MatedCRT.S2VG.LitCoordChange)
    (hB1 : ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ) :
    ShortWindowGoodRadiusPrevalenceStmt :=
  MatedCRT.Lemma68Window.hprev_of_shortWindow_noH0 hE hCC
    (wholePlaneUpperVolumeTailStep_of_ballMass hBM hCC) hB1 hμ

end MatedCRT.ShortWindowHV

#print axioms MatedCRT.ShortWindowHV.sdw_affineCoordChange_explicit
#print axioms MatedCRT.ShortWindowHV.coordFactor_markov
#print axioms MatedCRT.ShortWindowHV.wholePlaneUpperVolumeTailStep_of_ballMass
#print axioms MatedCRT.ShortWindowHV.hprev_of_shortWindow_noH0V
