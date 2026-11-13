import MatedCRT.FirstPass.Derived.GmcFirstMomentSingular
import MatedCRT.FirstPass.Derived.GmcGreenApproxGFF

/-!
# Intensity bound for the γ-LQG measure of `h^ℂ - γ log |·|` away from the origin

Let `h^ℂ` be a whole-plane GFF, `0 < γ < 2`, and let `Γ = gmcLimit γ ρ ρ₂ ψ` be the cut-off γ-LQG measure of
`h = h^ℂ - γ log |·|` (`ψ = clockPsi (fieldCircleAverage γ ∘ hc)`). For a continuous `φ ≥ 0` whose support lies in
the annulus `{s₀ ≤ |x| ≤ R}` with `s₀ > 0`,
`E ∫ φ dΓ ≤ (R + 1)^{γ²} s₀^{-γ²} ∫ φ(x) dx`
(`lintegral_lintegral_gmcLimit_le`). The proof is Fatou's lemma along the almost-sure vague convergence of the
circle-average approximations (`ae_gmcApproxCut_finite_and_isVagueLimitOn_gff`), Tonelli, and the first moment of the
circle-average density (`lintegral_density_fieldCircleAverage_le`).
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- A continuous function `φ ≥ 0` with compact support has finite `∫⁻ φ dm` when `m (tsupport φ) < ∞`. -/
lemma lintegral_ofReal_ne_top_of_tsupport {m : Measure ℂ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hm : m (tsupport φ) < ∞) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂m ≠ ∞ := by
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hle : ∀ x, ENNReal.ofReal (φ x) ≤ (tsupport φ).indicator (fun _ => ENNReal.ofReal M) x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · rw [indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM x))
    · rw [image_eq_zero_of_notMem_tsupport hx, ENNReal.ofReal_zero]
      exact zero_le
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_indicator_const (isClosed_tsupport φ).measurableSet]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm.ne

/-- For a continuous `φ ≥ 0` with compact support and `m (tsupport φ) < ∞`, the lower integral of `φ` is the
image of its Bochner integral. -/
lemma lintegral_ofReal_eq_ofReal_integral_of_tsupport {m : Measure ℂ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) (hm : m (tsupport φ) < ∞) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂m = ENNReal.ofReal (∫ x, φ x ∂m) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hφ0) hφ.aestronglyMeasurable,
    ENNReal.ofReal_toReal (lintegral_ofReal_ne_top_of_tsupport hφ hφc hm)]


/-- Joint measurability of the cut-off density along a measurable family of circle-average fields. -/
lemma measurable_gmcCutDensity_comp {X : Type*} [MeasurableSpace X] (γ ρ ρ₂ : ℝ) (k : ℕ)
    {g : X → UnitDiskCircleIndex → ℝ} (hg : Measurable g) :
    Measurable fun p : X × ℂ => gmcCutDensity γ ρ ρ₂ k (g p.1) p.2 := by
  have h := (measurable_uncurry_gmcCutDensity γ ρ ρ₂ k).comp ((hg.comp measurable_fst).prodMk measurable_snd)
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using h

/-- **Intensity bound for a cut-off chaos limit (abstract form).** Let `ψ ω'` be a measurable family of circle-average
fields, almost surely continuous and given by `H ω'` on the index set, whose cut-off approximations converge vaguely
to `gmcLimit γ ρ ρ₂ (ψ ω')` almost surely. If at all small dyadic scales `E[ε^{γ²/2} e^{γ H_ε(x)}] ≤ C` at every
point of the support of a continuous `φ ≥ 0` with compact support, then `E ∫ φ dΓ ≤ C ∫ φ(x) dx`. -/
theorem lintegral_lintegral_gmcLimit_le_of {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [SFinite P']
    {γ ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {ψ : Ω' → UnitDiskCircleIndex → ℝ} (hψm : Measurable ψ)
    {H : Ω' → ℝ → ℂ → ℝ} (hH : ∀ ω' (q : UnitDiskCircleIndex), ψ ω' q = H ω' q.1.1 q.1.2)
    (hcont : ∀ᵐ ω' ∂P', Continuous (ψ ω'))
    (hV : ∀ᵐ ω' ∂P', (∀ K, IsCompact K → ∀ᶠ k in atTop, gmcApproxCut γ ρ ρ₂ k (ψ ω') K < ∞) ∧
      QuantumZipper.IsVagueLimitOn univ (fun k => gmcApproxCut γ ρ ρ₂ k (ψ ω')) (gmcLimit γ ρ ρ₂ (ψ ω')))
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) (hφc : HasCompactSupport φ) {C : ℝ≥0∞}
    (hmom : ∀ᶠ k in atTop, ∀ x, φ x ≠ 0 →
      ∫⁻ ω', ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω' (dyadicScale k) x)) ∂P' ≤ C) :
    ∫⁻ ω', ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcLimit γ ρ ρ₂ (ψ ω')) ∂P' ≤ C * ∫⁻ x, ENNReal.ofReal (φ x) := by
  have hφm : Measurable fun x => ENNReal.ofReal (φ x) := hφ.measurable.ennreal_ofReal
  have hFm : ∀ k, Measurable fun ω' => ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcApproxCut γ ρ ρ₂ k (ψ ω')) := by
    intro k
    have h := (Measure.measurable_lintegral hφm).comp ((measurable_gmcApproxCut γ ρ ρ₂ k).comp hψm)
    simpa only [Function.comp_def] using h
  -- Step 1: almost surely, `∫ φ dΓ ≤ liminf_k ∫ φ dΓ_k` (vague convergence).
  have hlim : ∀ᵐ ω' ∂P', ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcLimit γ ρ ρ₂ (ψ ω')) ≤
      liminf (fun k => ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcApproxCut γ ρ ρ₂ k (ψ ω'))) atTop := by
    filter_upwards [hV] with ω' hω'
    obtain ⟨hfin, hV'⟩ := hω'
    have hK := hV'.2.1 (tsupport φ) hφc.isCompact (subset_univ _)
    have hT := hV'.2.2 φ hφ hφc (subset_univ _)
    have hT' : Tendsto (fun k => ENNReal.ofReal (∫ x, φ x ∂(gmcApproxCut γ ρ ρ₂ k (ψ ω')))) atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcLimit γ ρ ρ₂ (ψ ω')))) := by
      rw [lintegral_ofReal_eq_ofReal_integral_of_tsupport hφ hφc hφ0 hK]
      exact (ENNReal.continuous_ofReal.tendsto _).comp hT
    have hev : (fun k => ENNReal.ofReal (∫ x, φ x ∂(gmcApproxCut γ ρ ρ₂ k (ψ ω')))) =ᶠ[atTop]
        fun k => ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcApproxCut γ ρ ρ₂ k (ψ ω')) := by
      filter_upwards [hfin (tsupport φ) hφc.isCompact] with k hk
      exact (lintegral_ofReal_eq_ofReal_integral_of_tsupport hφ hφc hφ0 hk).symm
    exact ((hT'.congr' hev).liminf_eq).ge
  -- Step 2: the first moment of `∫ φ dΓ_k` at small dyadic scales (Tonelli).
  have hscale : ∀ᶠ k in atTop, dyadicScale k ≤ 1 - ρ₂ := by
    have ht : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) := by
      unfold dyadicScale
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact ht.eventually (Iic_mem_nhds (by linarith : (0 : ℝ) < 1 - ρ₂))
  have hk_bound : ∀ k, dyadicScale k ≤ 1 - ρ₂ → (∀ x, φ x ≠ 0 →
      ∫⁻ ω', ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω' (dyadicScale k) x)) ∂P' ≤ C) →
      ∫⁻ ω', ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcApproxCut γ ρ ρ₂ k (ψ ω')) ∂P' ≤
        C * ∫⁻ x, ENNReal.ofReal (φ x) := by
    intro k hk hmk
    have hε : 0 < dyadicScale k := dyadicScale_pos k
    have hdm : Measurable fun p : Ω' × ℂ => ENNReal.ofReal (gmcCutDensity γ ρ ρ₂ k (ψ p.1) p.2) :=
      (measurable_gmcCutDensity_comp γ ρ ρ₂ k hψm).ennreal_ofReal
    have hFeq : ∀ ω', ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcApproxCut γ ρ ρ₂ k (ψ ω')) =
        ∫⁻ x, ENNReal.ofReal (gmcCutDensity γ ρ ρ₂ k (ψ ω') x) * ENNReal.ofReal (φ x) := by
      intro ω'
      have hdx : Measurable fun x => ENNReal.ofReal (gmcCutDensity γ ρ ρ₂ k (ψ ω') x) :=
        ((measurable_uncurry_gmcCutDensity γ ρ ρ₂ k).of_uncurry_left).ennreal_ofReal
      rw [gmcApproxCut, lintegral_withDensity_eq_lintegral_mul _ hdx hφm]
      simp only [Pi.mul_apply]
    have hpt : ∀ x, ∫⁻ ω', ENNReal.ofReal (gmcCutDensity γ ρ ρ₂ k (ψ ω') x) * ENNReal.ofReal (φ x) ∂P' ≤
        ENNReal.ofReal (φ x) * C := by
      intro x
      by_cases hx : φ x = 0
      · simp [hx]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
      gcongr
      refine le_trans (lintegral_mono_ae ?_) (hmk x hx)
      filter_upwards [hcont] with ω' hω'
      rw [gmcCutDensity_eq_of_lt hρρ₂ hω' (hH ω') hk x]
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left
        (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le) (gmcCutoff_le_one ρ ρ₂ x))
    calc ∫⁻ ω', ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcApproxCut γ ρ ρ₂ k (ψ ω')) ∂P'
        = ∫⁻ ω', (∫⁻ x, ENNReal.ofReal (gmcCutDensity γ ρ ρ₂ k (ψ ω') x) * ENNReal.ofReal (φ x)) ∂P' := by
          simp only [hFeq]
      _ = ∫⁻ x, ∫⁻ ω', ENNReal.ofReal (gmcCutDensity γ ρ ρ₂ k (ψ ω') x) * ENNReal.ofReal (φ x) ∂P' :=
          lintegral_lintegral_swap ((hdm.mul (hφm.comp measurable_snd)).aemeasurable)
      _ ≤ ∫⁻ x, ENNReal.ofReal (φ x) * C := lintegral_mono hpt
      _ = C * ∫⁻ x, ENNReal.ofReal (φ x) := by
          rw [lintegral_mul_const _ hφm, mul_comm]
  -- Step 3: Fatou.
  calc ∫⁻ ω', ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcLimit γ ρ ρ₂ (ψ ω')) ∂P'
      ≤ ∫⁻ ω', liminf (fun k => ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcApproxCut γ ρ ρ₂ k (ψ ω'))) atTop ∂P' :=
        lintegral_mono_ae hlim
    _ ≤ liminf (fun k => ∫⁻ ω', ∫⁻ x, ENNReal.ofReal (φ x) ∂(gmcApproxCut γ ρ ρ₂ k (ψ ω')) ∂P') atTop :=
        lintegral_liminf_le' fun k => (hFm k).aemeasurable
    _ ≤ C * ∫⁻ x, ENNReal.ofReal (φ x) :=
        liminf_le_of_frequently_le' ((hscale.and hmom).mono fun k hk => hk_bound k hk.1 hk.2).frequently

/-- **Intensity bound for the γ-LQG measure of `h^ℂ - γ log |·|` away from the origin.** For a whole-plane GFF
`h^ℂ`, `0 < γ < 2`, `ρ < ρ₂ < 1`, and a continuous `φ ≥ 0` with `s₀ ≤ |x| ≤ R` wherever `φ x ≠ 0` (`s₀ > 0`):
`E ∫ φ dΓ ≤ (R + 1)^{γ²} s₀^{-γ²} ∫ φ(x) dx`, where `Γ = gmcLimit γ ρ ρ₂ ψ` is the cut-off γ-LQG measure of
`h = h^ℂ - γ log |·|`. -/
theorem lintegral_lintegral_gmcLimit_le {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [SFinite P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) {s₀ R : ℝ} (hs₀ : 0 < s₀)
    (hsupp : ∀ x, φ x ≠ 0 → s₀ ≤ ‖x‖ ∧ ‖x‖ ≤ R) :
    ∫⁻ ω', ∫⁻ x, ENNReal.ofReal (φ x)
        ∂(gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')) ∂P' ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1)) * s₀ ^ (-γ ^ 2)) *
        ∫⁻ x, ENNReal.ofReal (φ x) := by
  have hmeas : ∀ (r' : ℝ) (z' : ℂ), 0 < r' → Measurable fun ω => fieldCircleAverage γ (hc ω) r' z' :=
    fun r' z' hr' => (hG.measurable_circle r' z' hr').sub measurable_const
  have hφc : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun x hx => ?_
    by_contra h
    exact hx (mem_closedBall_zero_iff.2 (hsupp x h).2)
  have hcont : ∀ᵐ ω' ∂P', Continuous (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') := by
    filter_upwards [hG.ae_continuousOn_circle] with ω' hcc
    have hcF := continuousOn_fieldCircleAverage (α₀ := γ) hcc
    exact hcF.comp_continuous continuous_subtype_val (fun q => ⟨q.2.1, mem_univ _⟩)
  refine lintegral_lintegral_gmcLimit_le_of hρρ₂ hρ₂ (measurable_unitDiskCircle _ hmeas) (fun _ _ => rfl) hcont
    (ae_gmcApproxCut_finite_and_isVagueLimitOn_gff hG hγ hγ2 hρρ₂ hρ₂) hφ hφ0 hφc
    (Eventually.of_forall fun k x hx => ?_)
  obtain ⟨hs, hR⟩ := hsupp x hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs
    linarith
  have hε1 : dyadicScale k ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  refine (lintegral_density_fieldCircleAverage_le hG hγ.le ((norm_nonneg x).trans hR) (dyadicScale_pos k) hε1
    hx0 hR).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le))
  exact Real.rpow_le_rpow_of_nonpos hs₀ hs (by nlinarith)


/-- The continuous bump `max 0 (min 1 (2 - |x - y| / t))`: it equals `1` on `closedBall y t` and vanishes off
`ball y (2 t)`. -/
noncomputable def ballBump (y : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  max 0 (min 1 (2 - dist x y / t))

lemma continuous_ballBump (y : ℂ) (t : ℝ) : Continuous (ballBump y t) :=
  continuous_const.max (continuous_const.min
    (continuous_const.sub ((continuous_id.dist continuous_const).div_const t)))

lemma ballBump_nonneg (y : ℂ) (t : ℝ) (x : ℂ) : 0 ≤ ballBump y t x :=
  le_max_left _ _

lemma ballBump_le_one (y : ℂ) (t : ℝ) (x : ℂ) : ballBump y t x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma ballBump_eq_one {y : ℂ} {t : ℝ} (ht : 0 < t) {x : ℂ} (hx : dist x y ≤ t) : ballBump y t x = 1 := by
  have h1 : dist x y / t ≤ 1 := (div_le_one ht).2 hx
  have h2 : min 1 (2 - dist x y / t) = 1 := min_eq_left (by linarith)
  rw [ballBump, h2]
  exact max_eq_right zero_le_one

lemma dist_lt_of_ballBump_ne_zero {y : ℂ} {t : ℝ} (ht : 0 < t) {x : ℂ} (hx : ballBump y t x ≠ 0) :
    dist x y < 2 * t := by
  by_contra h
  have h1 : 2 ≤ dist x y / t := (le_div_iff₀ ht).2 (by linarith)
  have h2 : min 1 (2 - dist x y / t) ≤ 0 := (min_le_right _ _).trans (by linarith)
  exact hx (max_eq_left h2)

/-- **Ball masses of the γ-LQG measure of `h^ℂ - γ log |·|` away from the origin.** For a whole-plane GFF `h^ℂ`,
`0 < γ < 2`, `ρ < ρ₂ < 1`, a ball `closedBall y t` with `s₀ + 2 t ≤ |y|` (`s₀, t > 0`) and `|y| + 2 t ≤ R`:
`E Γ(closedBall y t) ≤ (R + 1)^{γ²} s₀^{-γ²} · |ball y (2 t)|`, where `Γ = gmcLimit γ ρ ρ₂ ψ`. -/
theorem lintegral_gmcLimit_closedBall_le {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [SFinite P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1)
    {y : ℂ} {s₀ t R : ℝ} (hs₀ : 0 < s₀) (ht : 0 < t) (hyt : s₀ + 2 * t ≤ ‖y‖) (hR : ‖y‖ + 2 * t ≤ R) :
    ∫⁻ ω', gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (closedBall y t) ∂P' ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1)) * s₀ ^ (-γ ^ 2)) * volume (ball y (2 * t)) := by
  have hsupp : ∀ x, ballBump y t x ≠ 0 → s₀ ≤ ‖x‖ ∧ ‖x‖ ≤ R := by
    intro x hx
    have hd := dist_lt_of_ballBump_ne_zero ht hx
    rw [dist_eq_norm] at hd
    have h1 := norm_sub_norm_le y x
    have h2 := norm_sub_norm_le x y
    rw [norm_sub_rev] at h1
    constructor <;> linarith
  have hlow : ∀ x, (closedBall y t).indicator 1 x ≤ ENNReal.ofReal (ballBump y t x) := by
    intro x
    by_cases hx : x ∈ closedBall y t
    · rw [indicator_of_mem hx, ballBump_eq_one ht (mem_closedBall.1 hx), ENNReal.ofReal_one]
      rfl
    · rw [indicator_of_notMem hx]
      exact zero_le
  have hup : ∀ x, ENNReal.ofReal (ballBump y t x) ≤ (ball y (2 * t)).indicator 1 x := by
    intro x
    by_cases hx : ballBump y t x = 0
    · rw [hx, ENNReal.ofReal_zero]
      exact zero_le
    · rw [indicator_of_mem (mem_ball.2 (dist_lt_of_ballBump_ne_zero ht hx))]
      exact ENNReal.ofReal_le_one.2 (ballBump_le_one y t x)
  calc ∫⁻ ω', gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (closedBall y t) ∂P'
      ≤ ∫⁻ ω', ∫⁻ x, ENNReal.ofReal (ballBump y t x)
          ∂(gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')) ∂P' := by
        refine lintegral_mono fun ω' => ?_
        rw [← lintegral_indicator_one measurableSet_closedBall]
        exact lintegral_mono hlow
    _ ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1)) * s₀ ^ (-γ ^ 2)) *
          ∫⁻ x, ENNReal.ofReal (ballBump y t x) :=
        lintegral_lintegral_gmcLimit_le hG hγ hγ2 hρρ₂ hρ₂ (continuous_ballBump y t) (ballBump_nonneg y t) hs₀
          hsupp
    _ ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1)) * s₀ ^ (-γ ^ 2)) * volume (ball y (2 * t)) := by
        gcongr
        rw [← lintegral_indicator_one measurableSet_ball]
        exact lintegral_mono hup

end MatedCRT.KilledOccupation
