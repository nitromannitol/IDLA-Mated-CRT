import MatedCRT.FirstPass.S2y.ConeRadialCodes

/-!
# Internal angular integrability on the circles of a quantum cone

For a `γ`-quantum cone the circle average `h_r(z)` of the radial process is almost surely integrable in the angle along
`∂B_r(z)`, also when the circle passes through the origin (Duplantier-Sheffield, arXiv:1409.7055, §4; Armstrong-Kuusi-Mourrat).
The argument is internal: it uses only the measurability `hcm`, the almost sure joint continuity `hcont` on `(0,∞) × ℂ`
and the radial law `HasConeRadialLaw`. No named input is needed.

* `norm_exp_add_exp_mul_I`, `norm_circleMap_tangent`: on the tangent circle `‖z‖ = r`, `z = r e^{iα}` and
  `‖circleMap z r θ‖ = 2 r |cos((θ-α)/2)|`.
* `intervalIntegrable_log_cos_affine`: `log |cos|` is interval integrable along the affine angle (`Real.intervalIntegrable_log_cos`).
* `integrableOn_smallDominator`: the deterministic majorant `1_{‖circleMap z r θ‖ ≤ 1} (1 + (1+|γ|)(-log ‖circleMap z r θ‖))`
  is integrable on `(0, 2π]`.
* `ae_lintegral_smallCircleIntegrand_lt_top`: Tonelli on `Ω × ℝ` with the marginal bound `lintegral_radial_le`.
* `ae_intervalIntegrable_radial_circle`: the almost sure interval integrability of `θ ↦ |h_{‖circleMap z r θ‖}(0)|`.
* `radialSphereCode_ae_eq`: the unconditional sphere-average code, the wrapper of `radialSphereCode_ae_eq_of_circInt`.
-/

open MeasureTheory Filter Topology Set Metric
open ProbabilityTheory HarmonicBalls MarkovProcess
open scoped Real NNReal ENNReal

namespace MatedCRT

/-- The sum of the unit vectors `e^{iα}` and `e^{iθ}` has modulus `2 |cos((θ-α)/2)|`. -/
lemma norm_exp_add_exp_mul_I (α θ : ℝ) :
    ‖Complex.exp (α * Complex.I) + Complex.exp (θ * Complex.I)‖ = 2 * |Real.cos ((θ - α) / 2)| := by
  have h1 : Complex.exp (α * Complex.I)
      = Complex.exp (((α + θ) / 2 : ℝ) * Complex.I) * Complex.exp (-(((θ - α) / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : Complex.exp (θ * Complex.I)
      = Complex.exp (((α + θ) / 2 : ℝ) * Complex.I) * Complex.exp ((((θ - α) / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h3 : Complex.exp (-(((θ - α) / 2 : ℝ) : ℂ) * Complex.I)
      + Complex.exp ((((θ - α) / 2 : ℝ) : ℂ) * Complex.I) = 2 * ((Real.cos ((θ - α) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.two_cos, add_comm]
  rw [h1, h2, ← mul_add, h3, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- On the tangent circle `‖z‖ = r` one writes `z = r e^{iα}`, and then `‖circleMap z r θ‖ = 2 r |cos((θ-α)/2)|`. -/
lemma norm_circleMap_tangent {r : ℝ} (hr : 0 < r) (α θ : ℝ) :
    ‖circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ‖ = 2 * r * |Real.cos ((θ - α) / 2)| := by
  have hx : circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ
      = (r : ℂ) * (Complex.exp (α * Complex.I) + Complex.exp (θ * Complex.I)) := by
    simp only [circleMap]; ring
  rw [hx, norm_mul, norm_exp_add_exp_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  ring

/-- Reverse triangle inequality on a circle: `|‖z‖ - r| ≤ ‖circleMap z r θ‖`. -/
lemma abs_norm_sub_le_norm_circleMap (z : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    |‖z‖ - r| ≤ ‖circleMap z r θ‖ := by
  have hw : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hc : circleMap z r θ = z + (r : ℂ) * Complex.exp (θ * Complex.I) := rfl
  rw [hc]
  have h1 := norm_sub_le (z + (r : ℂ) * Complex.exp (θ * Complex.I)) ((r : ℂ) * Complex.exp (θ * Complex.I))
  have h2 := norm_sub_le (z + (r : ℂ) * Complex.exp (θ * Complex.I)) z
  rw [add_sub_cancel_right, hw] at h1
  rw [add_sub_cancel_left, hw] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Upper bound on a circle: `‖circleMap z r θ‖ ≤ ‖z‖ + r`. -/
lemma norm_circleMap_le_add (z : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) : ‖circleMap z r θ‖ ≤ ‖z‖ + r := by
  have hc : circleMap z r θ = z + (r : ℂ) * Complex.exp (θ * Complex.I) := rfl
  rw [hc]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_pos hr]

lemma measurable_norm_circleMap (z : ℂ) (r : ℝ) : Measurable fun θ : ℝ => ‖circleMap z r θ‖ :=
  (continuous_norm.comp (continuous_circleMap z r)).measurable

lemma volume_Ioc_two_pi_ne_top : volume (Ioc (0 : ℝ) (2 * π)) ≠ ∞ := by
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

/-- `θ ↦ log |cos((θ-α)/2)|` is interval integrable on `[0, 2π]`: `Real.intervalIntegrable_log_cos` on the
rescaled and shifted interval. -/
lemma intervalIntegrable_log_cos_affine (α : ℝ) :
    IntervalIntegrable (fun θ : ℝ => Real.log (Real.cos ((θ - α) / 2))) volume 0 (2 * π) := by
  have h1 := (intervalIntegrable_log_cos (a := -α / 2) (b := (2 * π - α) / 2)).comp_mul_left
    (c := (1 / 2 : ℝ))
  have h2 := h1.comp_sub_right α
  have ea : -α / 2 / (1 / 2) + α = 0 := by ring
  have eb : (2 * π - α) / 2 / (1 / 2) + α = 2 * π := by ring
  rw [ea, eb] at h2
  convert h2 using 1
  funext θ
  simp only [Function.comp]
  rw [show (θ - α) / 2 = 1 / 2 * (θ - α) by ring]

/-- **Tangent case, deterministic.** If `‖z‖ = r`, the function `θ ↦ 1_{‖circleMap z r θ‖ ≤ 1} (-log ‖circleMap z r θ‖)`
is integrable on `(0, 2π]`: its logarithmic singularity at the (at most one) point where the circle meets the origin is
the one of `log |cos|`. -/
lemma integrableOn_log_small_tangent {r : ℝ} (hr : 0 < r) (α : ℝ) :
    IntegrableOn (fun θ : ℝ => Set.indicator {θ : ℝ | ‖circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ‖ ≤ 1}
      (fun θ : ℝ => -Real.log ‖circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ‖) θ) (Ioc 0 (2 * π)) := by
  have hρ := measurable_norm_circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r
  have hmeas : Measurable fun θ : ℝ => Set.indicator {θ : ℝ | ‖circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ‖ ≤ 1}
      (fun θ : ℝ => -Real.log ‖circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ‖) θ :=
    ((Real.measurable_log.comp hρ).neg).indicator (measurableSet_le hρ measurable_const)
  have hl : IntegrableOn (fun θ : ℝ => ‖Real.log (Real.cos ((θ - α) / 2))‖) (Ioc 0 (2 * π)) :=
    (intervalIntegrable_log_cos_affine α).norm.1
  have hc : IntegrableOn (fun _ : ℝ => |Real.log (2 * r)|) (Ioc 0 (2 * π)) := integrableOn_const volume_Ioc_two_pi_ne_top
  refine Integrable.mono' (Integrable.add hc hl) hmeas.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs with hθ
  · rcases (norm_nonneg (circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ)).eq_or_lt with h0 | hpos
    · rw [← h0, Real.log_zero, neg_zero, norm_zero]
      exact add_nonneg (abs_nonneg _) (norm_nonneg _)
    · rw [norm_circleMap_tangent hr] at hpos ⊢
      have hcos : |Real.cos ((θ - α) / 2)| ≠ 0 := by
        intro h
        rw [h, mul_zero] at hpos
        exact lt_irrefl _ hpos
      have hlog : Real.log (2 * r * |Real.cos ((θ - α) / 2)|)
          = Real.log (2 * r) + Real.log (Real.cos ((θ - α) / 2)) := by
        rw [Real.log_mul (mul_pos two_pos hr).ne' hcos, Real.log_abs]
      rw [hlog]
      calc ‖-(Real.log (2 * r) + Real.log (Real.cos ((θ - α) / 2)))‖
          = ‖Real.log (2 * r) + Real.log (Real.cos ((θ - α) / 2))‖ := norm_neg _
        _ ≤ ‖Real.log (2 * r)‖ + ‖Real.log (Real.cos ((θ - α) / 2))‖ := norm_add_le _ _
        _ = |Real.log (2 * r)| + ‖Real.log (Real.cos ((θ - α) / 2))‖ := by rw [Real.norm_eq_abs]
  · simp only [norm_zero]
    exact add_nonneg (abs_nonneg _) (norm_nonneg _)

/-- **Deterministic integrability of the small-radius logarithm on a circle**. For `r > 0`,
`θ ↦ 1_{‖circleMap z r θ‖ ≤ 1} (-log ‖circleMap z r θ‖)` is integrable on `(0, 2π]`. If `‖z‖ ≠ r` the circle keeps distance
`|‖z‖ - r| > 0` from the origin; if `‖z‖ = r` this is `integrableOn_log_small_tangent`. -/
lemma integrableOn_log_small_circleMap (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun θ : ℝ => Set.indicator {θ : ℝ | ‖circleMap z r θ‖ ≤ 1}
      (fun θ : ℝ => -Real.log ‖circleMap z r θ‖) θ) (Ioc 0 (2 * π)) := by
  by_cases hz : ‖z‖ = r
  · obtain ⟨α, rfl⟩ : ∃ α : ℝ, z = (r : ℂ) * Complex.exp (α * Complex.I) := by
      refine ⟨Complex.arg z, ?_⟩
      have h := Complex.norm_mul_exp_arg_mul_I z
      rw [hz] at h
      exact h.symm
    exact integrableOn_log_small_tangent hr α
  · have hρ := measurable_norm_circleMap z r
    have hmeas : Measurable fun θ : ℝ => Set.indicator {θ : ℝ | ‖circleMap z r θ‖ ≤ 1}
        (fun θ : ℝ => -Real.log ‖circleMap z r θ‖) θ :=
      ((Real.measurable_log.comp hρ).neg).indicator (measurableSet_le hρ measurable_const)
    have hδ : 0 < |‖z‖ - r| := abs_pos.2 (sub_ne_zero.2 hz)
    have hc : IntegrableOn (fun _ : ℝ => |Real.log (|‖z‖ - r|)|) (Ioc 0 (2 * π)) := integrableOn_const volume_Ioc_two_pi_ne_top
    refine Integrable.mono' hc hmeas.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with hθ
    · have hlow := abs_norm_sub_le_norm_circleMap z hr θ
      have hl1 : Real.log |‖z‖ - r| ≤ Real.log ‖circleMap z r θ‖ := Real.log_le_log hδ hlow
      have hl2 : 0 ≤ -Real.log ‖circleMap z r θ‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) hθ)
      have hB : -Real.log |‖z‖ - r| ≤ |Real.log (|‖z‖ - r|)| := neg_le_abs _
      rw [Real.norm_eq_abs, abs_of_nonneg hl2]
      linarith
    · simp only [norm_zero]
      exact abs_nonneg _

/-- The majorant of the small-radius part: `1_{‖circleMap z r θ‖ ≤ 1} (1 + (1+|γ|)(-log ‖circleMap z r θ‖))`. -/
noncomputable def smallDominator (γ : ℝ) (z : ℂ) (r : ℝ) (θ : ℝ) : ℝ :=
  Set.indicator {θ : ℝ | ‖circleMap z r θ‖ ≤ 1} (fun _ => (1 : ℝ)) θ
    + (1 + |γ|) * Set.indicator {θ : ℝ | ‖circleMap z r θ‖ ≤ 1} (fun θ => -Real.log ‖circleMap z r θ‖) θ

lemma integrableOn_smallDominator (γ : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (smallDominator γ z r) (Ioc (0 : ℝ) (2 * π)) := by
  have hS1 : MeasurableSet {θ : ℝ | ‖circleMap z r θ‖ ≤ 1} :=
    measurableSet_le (measurable_norm_circleMap z r) measurable_const
  have hc1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) (2 * π)) := integrableOn_const volume_Ioc_two_pi_ne_top
  unfold smallDominator
  exact Integrable.add (hc1.indicator hS1)
    (Integrable.const_mul (integrableOn_log_small_circleMap z hr) (1 + |γ|))

/-- The small-radius integrand on `Ω × ℝ`: `1_{‖circleMap z r θ‖ ≤ 1} |1_T c_ω(‖circleMap z r θ‖, 0)|`, as an
`ℝ≥0∞` value. The radius is written as `exp(-(-log ‖circleMap z r θ‖))`, so the angle enters through `t = -log s`
and the point `θ` where the circle meets the origin is harmless (it is a null set). -/
noncomputable def smallCircleIntegrand {Ω : Type*} (c : Ω → ℝ → ℂ → ℝ) (T : Set Ω) (z : ℂ) (r : ℝ) (p : Ω × ℝ) :
    ℝ≥0∞ :=
  if ‖circleMap z r p.2‖ ≤ 1 then
    ENNReal.ofReal |T.indicator (fun ω' => c ω' (Real.exp (-(-Real.log ‖circleMap z r p.2‖))) 0) p.1|
  else 0

/-- Joint measurability of the small-radius integrand, from the Carathéodory form `measurable_uncurry_radial`. -/
lemma measurable_smallCircleIntegrand {Ω : Type*} [MeasurableSpace Ω] {c : Ω → ℝ → ℂ → ℝ} {T : Set Ω}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z) (hT : MeasurableSet T)
    (hgood : ∀ ω ∈ T, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) (z : ℂ) (r : ℝ) :
    Measurable (smallCircleIntegrand c T z r) := by
  have hρ := measurable_norm_circleMap z r
  have hU := measurable_uncurry_radial hcm hT hgood
  have hΦm : Measurable fun p : Ω × ℝ =>
      T.indicator (fun ω' => c ω' (Real.exp (-(-Real.log ‖circleMap z r p.2‖))) 0) p.1 := by
    have h1 : Measurable fun p : Ω × ℝ => (-Real.log ‖circleMap z r p.2‖, p.1) :=
      ((Real.measurable_log.comp (hρ.comp measurable_snd)).neg).prodMk measurable_fst
    exact hU.comp h1
  have hS : MeasurableSet {p : Ω × ℝ | ‖circleMap z r p.2‖ ≤ 1} :=
    measurableSet_le (hρ.comp measurable_snd) measurable_const
  exact Measurable.ite hS (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hΦm)) measurable_const

/-- **Almost sure finiteness of the small-radius angular integral**. For the good modification
`T` of the circle averages, almost surely `∫_{(0,2π]} 1_{‖circleMap z r θ‖ ≤ 1} |c_ω(‖circleMap z r θ‖,0)| dθ < ∞`.
Joint measurability is `measurable_smallCircleIntegrand`; the expectation at each angle is bounded by
`lintegral_radial_le`; the majorant is `integrableOn_smallDominator`. -/
lemma ae_lintegral_smallCircleIntegrand_lt_top {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {c : Ω → ℝ → ℂ → ℝ} (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z) {ν : Measure (ContinuousPath ℝ)}
    (hν : IsProbabilityMeasure ν) (hrad : P.map (fun ω => radialProcess (c ω)) = quantumConeRadialLaw γ ν)
    [IsFiniteMeasure P] {T : Set Ω} (hT : MeasurableSet T) (hPT : P Tᶜ = 0)
    (hgood : ∀ ω ∈ T, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, ∫⁻ θ in Ioc (0 : ℝ) (2 * π), smallCircleIntegrand c T z r (ω, θ) < ⊤ := by
  have hFm := measurable_smallCircleIntegrand hcm hT hgood z r
  have hfin : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), ENNReal.ofReal (smallDominator γ z r θ) < ⊤ :=
    Integrable.lintegral_lt_top (integrableOn_smallDominator γ z hr)
  have hbound : ∀ θ : ℝ, ∫⁻ ω, smallCircleIntegrand c T z r (ω, θ) ∂P
      ≤ ENNReal.ofReal (smallDominator γ z r θ) := by
    intro θ
    by_cases hθ : ‖circleMap z r θ‖ ≤ 1
    · have ht : 0 ≤ -Real.log ‖circleMap z r θ‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) hθ)
      have hle := lintegral_radial_le hcm hν hrad hPT ht
      have hD : smallDominator γ z r θ = 1 + (1 + |γ|) * (-Real.log ‖circleMap z r θ‖) := by
        simp [smallDominator, hθ]
      rw [hD]
      calc ∫⁻ ω, smallCircleIntegrand c T z r (ω, θ) ∂P
          = ∫⁻ ω, ENNReal.ofReal |T.indicator (fun ω' => c ω' (Real.exp (-(-Real.log ‖circleMap z r θ‖))) 0) ω| ∂P := by
            simp [smallCircleIntegrand, hθ]
        _ ≤ ENNReal.ofReal (1 + (-Real.log ‖circleMap z r θ‖) + |γ| * (-Real.log ‖circleMap z r θ‖)) := hle
        _ = ENNReal.ofReal (1 + (1 + |γ|) * (-Real.log ‖circleMap z r θ‖)) := by congr 1; ring
    · have hD : smallDominator γ z r θ = 0 := by simp [smallDominator, hθ]
      have hI : ∫⁻ ω, smallCircleIntegrand c T z r (ω, θ) ∂P = 0 := by
        simp [smallCircleIntegrand, hθ]
      rw [hD, hI, ENNReal.ofReal_zero]
  have hI : ∫⁻ ω, (∫⁻ θ in Ioc (0 : ℝ) (2 * π), smallCircleIntegrand c T z r (ω, θ)) ∂P < ⊤ := by
    have hswap : ∫⁻ ω, (∫⁻ θ in Ioc (0 : ℝ) (2 * π), smallCircleIntegrand c T z r (ω, θ)) ∂P
        = ∫⁻ θ in Ioc (0 : ℝ) (2 * π), ∫⁻ ω, smallCircleIntegrand c T z r (ω, θ) ∂P :=
      lintegral_lintegral_swap hFm.aemeasurable
    rw [hswap]
    exact lt_of_le_of_lt (lintegral_mono hbound) hfin
  exact ae_lt_top hFm.lintegral_prod_right' hI.ne

/-- **Almost sure angular integrability of the circle averages of a quantum cone**. For every radius
`r > 0` and centre `z`, almost surely `θ ↦ |c_ω(‖circleMap z r θ‖, 0)|` is interval integrable on `[0, 2π]`, including
when the circle passes through the origin (the tangent case `‖z‖ = r`). Internal: the hypotheses are `hcm`, `hcont` and
`HasConeRadialLaw`. -/
theorem ae_intervalIntegrable_radial_circle {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {c : Ω → ℝ → ℂ → ℝ}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hrad : HasConeRadialLaw γ P c) :
    ∀ r z, 0 < r → ∀ᵐ ω ∂P,
      IntervalIntegrable (fun θ : ℝ => |c ω ‖circleMap z r θ‖ 0|) volume 0 (2 * π) := by
  intro r z hr
  obtain ⟨ν, hν, hrad'⟩ := hrad
  obtain ⟨T, hT, hPT, hgood⟩ := exists_measurable_good_set hcont
  have : IsFiniteMeasure P := isFiniteMeasure_of_radial_law hcm hν.1 hrad'
  have hsmall := ae_lintegral_smallCircleIntegrand_lt_top hcm hν.1 hrad' hT hPT hgood hr z
  have hTc : ∀ᵐ ω ∂P, ω ∈ T := by
    rw [ae_iff]
    exact hPT
  filter_upwards [hsmall, hTc] with ω hω hωT
  have hρ := measurable_norm_circleMap z r
  have hgc : Continuous fun t : ℝ => c ω (Real.exp (-t)) 0 :=
    (hgood ω hωT).comp_continuous (f := fun t : ℝ => ((Real.exp (-t)), (0 : ℂ)))
      (by fun_prop) (fun t => ⟨Real.exp_pos _, Set.mem_univ _⟩)
  set Ψ : ℝ → ℝ := fun θ =>
    |T.indicator (fun ω' => c ω' (Real.exp (-(-Real.log ‖circleMap z r θ‖))) 0) ω| with hΨdef
  have hpt_eq : ∀ θ : ℝ, smallCircleIntegrand c T z r (ω, θ)
      = if ‖circleMap z r θ‖ ≤ 1 then ENNReal.ofReal (Ψ θ) else 0 := fun θ => rfl
  have hΨeq : ∀ θ : ℝ, ‖circleMap z r θ‖ ≠ 0 → Ψ θ = |c ω ‖circleMap z r θ‖ 0| := by
    intro θ hθ
    have hpos : 0 < ‖circleMap z r θ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hθ)
    simp only [hΨdef]
    rw [Set.indicator_of_mem hωT, neg_neg, Real.exp_log hpos]
  have hΨm : Measurable Ψ := by
    have hfun : Ψ = fun θ : ℝ => |c ω (Real.exp (-(-Real.log ‖circleMap z r θ‖))) 0| := by
      funext θ
      simp only [hΨdef]
      rw [Set.indicator_of_mem hωT]
    rw [hfun]
    exact continuous_abs.measurable.comp (hgc.measurable.comp ((Real.measurable_log.comp hρ).neg))
  have hcontω : ContinuousOn (fun s : ℝ => c ω s 0) (Icc (1 : ℝ) (1 + ‖z‖ + r)) :=
    (hgood ω hωT).comp (f := fun s : ℝ => ((s : ℝ), (0 : ℂ)))
      (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨lt_of_lt_of_le one_pos hs.1, Set.mem_univ _⟩)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontω
  have hΨC : ∀ θ : ℝ, 1 < ‖circleMap z r θ‖ → Ψ θ ≤ C := by
    intro θ hθ
    have hR : ‖circleMap z r θ‖ ≤ 1 + ‖z‖ + r := by
      have := norm_circleMap_le_add z hr θ
      linarith
    rw [hΨeq θ (lt_trans one_pos hθ).ne', ← Real.norm_eq_abs]
    exact hC _ ⟨hθ.le, hR⟩
  have hpt : ∀ θ : ℝ, ENNReal.ofReal (Ψ θ)
      ≤ (if ‖circleMap z r θ‖ ≤ 1 then ENNReal.ofReal (Ψ θ) else 0) + ENNReal.ofReal C := by
    intro θ
    by_cases hθ : ‖circleMap z r θ‖ ≤ 1
    · simp only [hθ, ↓reduceIte]
      exact le_self_add
    · simp only [hθ, ↓reduceIte, zero_add]
      exact ENNReal.ofReal_le_ofReal (hΨC θ (not_le.1 hθ))
  have hω' : ∫⁻ θ in Ioc (0 : ℝ) (2 * π),
      (if ‖circleMap z r θ‖ ≤ 1 then ENNReal.ofReal (Ψ θ) else 0) < ⊤ := hω
  have hlt : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), ENNReal.ofReal (Ψ θ) < ⊤ := by
    calc ∫⁻ θ in Ioc (0 : ℝ) (2 * π), ENNReal.ofReal (Ψ θ)
        ≤ ∫⁻ θ in Ioc (0 : ℝ) (2 * π),
            ((if ‖circleMap z r θ‖ ≤ 1 then ENNReal.ofReal (Ψ θ) else 0) + ENNReal.ofReal C) :=
          lintegral_mono hpt
      _ = (∫⁻ θ in Ioc (0 : ℝ) (2 * π), (if ‖circleMap z r θ‖ ≤ 1 then ENNReal.ofReal (Ψ θ) else 0))
            + ∫⁻ _ in Ioc (0 : ℝ) (2 * π), ENNReal.ofReal C :=
          lintegral_add_right _ measurable_const
      _ < ⊤ := by
          refine ENNReal.add_lt_top.2 ⟨hω', ?_⟩
          rw [setLIntegral_const, Real.volume_Ioc]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hint : IntegrableOn Ψ (Ioc (0 : ℝ) (2 * π)) := by
    refine ⟨hΨm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun θ => abs_nonneg _)]
    exact hlt
  have hcongr : IntegrableOn (fun θ : ℝ => |c ω ‖circleMap z r θ‖ 0|) (Ioc (0 : ℝ) (2 * π)) := by
    refine Integrable.congr hint ?_
    filter_upwards [ae_circleMap_ne_zero (z := z) hr] with θ hθ
    exact hΨeq θ (norm_ne_zero_iff.2 hθ)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  exact hcongr

/-- **Radial sphere-average code is correct almost surely, with no named input**. This is
`radialSphereCode_ae_eq_of_circInt` with its angular-integrability hypothesis supplied by
`ae_intervalIntegrable_radial_circle`: the sphere average `h_r(z)` is the a.s. limit of the sphere codes. -/
theorem radialSphereCode_ae_eq {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : Ω → ℝ → ℂ → ℝ}
    (hcm : ∀ r z, 0 < r → Measurable fun ω => c ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hrad : HasConeRadialLaw γ P c)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (fun ω => radialSphereCode r z (circleProcess (c ω))) =ᵐ[P]
      (fun ω => Real.circleAverage (fun x => c ω ‖x‖ 0) z r) :=
  radialSphereCode_ae_eq_of_circInt hcm hcont hrad (ae_intervalIntegrable_radial_circle hcm hcont hrad) hr z

end MatedCRT

#print axioms MatedCRT.norm_circleMap_tangent
#print axioms MatedCRT.integrableOn_log_small_circleMap
#print axioms MatedCRT.ae_lintegral_smallCircleIntegrand_lt_top
#print axioms MatedCRT.ae_intervalIntegrable_radial_circle
#print axioms MatedCRT.radialSphereCode_ae_eq
