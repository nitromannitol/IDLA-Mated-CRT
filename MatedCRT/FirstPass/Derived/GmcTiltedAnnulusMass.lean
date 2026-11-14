import MatedCRT.FirstPass.Derived.GmcIntensityBound
import MatedCRT.FirstPass.Derived.GmcTiltedCircleMoment

/-!
# Tilted intensity bound for the γ-LQG measure of `h^ℂ - γ log |·|` near the origin

Let `h^ℂ` be a whole-plane GFF, `0 < γ < 2`, and let `Γ = gmcLimit γ ρ ρ₂ ψ` be the cut-off γ-LQG measure of
`h = h^ℂ - γ log |·|` (`ψ = clockPsi (fieldCircleAverage γ ∘ hc)`). For a continuous `φ ≥ 0` whose support lies in
the annulus `{s₀ ≤ |x| ≤ R}`, `0 < s₀ ≤ R < s ≤ 1`, the first moment of `∫ φ dΓ` tilted by `e^{-γ h^ℂ_s(0)}` is
`E[e^{-γ h^ℂ_s(0)} ∫ φ dΓ] ≤ s^{γ²/2} s₀^{-γ²} ∫ φ(x) dx`
(`lintegral_exp_neg_centredCircle_mul_lintegral_gmcLimit_le`).

The proof is Fatou's lemma along the almost-sure vague convergence of the circle-average approximations
(`lintegral_lintegral_gmcLimit_le_of`), applied under the tilted measure `P'.withDensity e^{-γ h^ℂ_s(0)}`, which is
absolutely continuous with respect to `P'`, together with the pointwise comparison `h_ε(x) ≤ h^ℂ_ε(x) - γ log |x|`
and the Gaussian identity `E[ε^{γ²/2} e^{γ h^ℂ_ε(x)} e^{-γ h^ℂ_s(0)}] = s^{γ²/2}` for `|x| + ε ≤ s`
(`lintegral_density_mul_exp_neg_centredCircle`). Tilting by the circle average at the scale of the annulus is the
first-moment estimate for the LQG mass near a `γ`-log singularity (Duplantier-Sheffield 2011, Section 3).
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **Tilted first moment of the LQG mass of an annulus about the origin.** For a whole-plane GFF `h^ℂ`,
`0 < γ < 2`, and a continuous `φ ≥ 0` supported in `{s₀ ≤ |x| ≤ R}` with `0 < s₀ ≤ R < s ≤ 1`:
`E[e^{-γ h^ℂ_s(0)} ∫ φ dΓ] ≤ s^{γ²/2} s₀^{-γ²} ∫ φ(x) dx`, where `Γ` is the cut-off γ-LQG measure of
`h^ℂ - γ log |·|`. -/
theorem lintegral_exp_neg_centredCircle_mul_lintegral_gmcLimit_le {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [SFinite P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂)
    (hρ₂ : ρ₂ < 1) {φ : ℂ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) {s₀ R s : ℝ} (hs₀ : 0 < s₀)
    (hs₀R : s₀ ≤ R) (hRs : R < s) (hs1 : s ≤ 1) (hsupp : ∀ x, φ x ≠ 0 → s₀ ≤ ‖x‖ ∧ ‖x‖ ≤ R) :
    ∫⁻ ω', ENNReal.ofReal (Real.exp (-γ * hc ω' s 0)) *
        ∫⁻ x, ENNReal.ofReal (φ x)
          ∂(gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')) ∂P' ≤
      ENNReal.ofReal (s ^ (γ ^ 2 / 2) * s₀ ^ (-γ ^ 2)) * ∫⁻ x, ENNReal.ofReal (φ x) := by
  have hs : 0 < s := by linarith
  have hdm : Measurable fun ω' => ENNReal.ofReal (Real.exp (-γ * hc ω' s 0)) :=
    ((hG.measurable_circle s 0 hs).const_mul (-γ)).exp.ennreal_ofReal
  have hdt : ∀ᵐ ω' ∂P', ENNReal.ofReal (Real.exp (-γ * hc ω' s 0)) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hac := withDensity_absolutelyContinuous P' fun ω' => ENNReal.ofReal (Real.exp (-γ * hc ω' s 0))
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
  have hscale : ∀ᶠ k in atTop, dyadicScale k ≤ s - R := by
    have ht : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) := by
      unfold dyadicScale
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact ht.eventually (Iic_mem_nhds (by linarith : (0 : ℝ) < s - R))
  have hkey : ∫⁻ ω', ∫⁻ x, ENNReal.ofReal (φ x)
        ∂(gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω'))
        ∂(P'.withDensity fun ω' => ENNReal.ofReal (Real.exp (-γ * hc ω' s 0))) ≤
      ENNReal.ofReal (s ^ (γ ^ 2 / 2) * s₀ ^ (-γ ^ 2)) * ∫⁻ x, ENNReal.ofReal (φ x) := by
    refine lintegral_lintegral_gmcLimit_le_of hρρ₂ hρ₂ (measurable_unitDiskCircle _ hmeas) (fun _ _ => rfl)
      (hac.ae_le hcont) (hac.ae_le (ae_gmcApproxCut_finite_and_isVagueLimitOn_gff hG hγ hγ2 hρρ₂ hρ₂))
      hφ hφ0 hφc ?_
    filter_upwards [hscale] with k hk x hx
    obtain ⟨hs0x, hRx⟩ := hsupp x hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hs0x
      linarith
    have hε := dyadicScale_pos k
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable P' hdm hdt]
    simp only [Pi.mul_apply]
    calc ∫⁻ ω', ENNReal.ofReal (Real.exp (-γ * hc ω' s 0)) *
          ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
            Real.exp (γ * fieldCircleAverage γ (hc ω') (dyadicScale k) x)) ∂P'
        ≤ ∫⁻ ω', ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hc ω' (dyadicScale k) x)) *
            ENNReal.ofReal (Real.exp (-γ * hc ω' s 0)) * ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂P' := by
          refine lintegral_mono fun ω' => ?_
          have h1 : ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
                Real.exp (γ * fieldCircleAverage γ (hc ω') (dyadicScale k) x)) ≤
              ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hc ω' (dyadicScale k) x)) *
                ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (density_fieldCircleAverage_le hγ.le (hc ω') hε hx0)
          calc ENNReal.ofReal (Real.exp (-γ * hc ω' s 0)) *
                ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
                  Real.exp (γ * fieldCircleAverage γ (hc ω') (dyadicScale k) x))
              ≤ ENNReal.ofReal (Real.exp (-γ * hc ω' s 0)) *
                (ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hc ω' (dyadicScale k) x)) *
                  ENNReal.ofReal (‖x‖ ^ (-γ ^ 2))) := by gcongr
            _ = _ := by ring
      _ = ENNReal.ofReal (s ^ (γ ^ 2 / 2)) * ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
            lintegral_density_mul_exp_neg_centredCircle hG γ hε hs1 (by linarith)]
      _ ≤ ENNReal.ofReal (s ^ (γ ^ 2 / 2) * s₀ ^ (-γ ^ 2)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hs.le _))
          exact Real.rpow_le_rpow_of_nonpos hs₀ hs0x (by nlinarith)
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable P' hdm hdt] at hkey
  simpa only [Pi.mul_apply] using hkey

/-- The continuous annular bump `max 0 (min 1 (min (3 - 2 |x| / b) (2 |x| / a - 1)))`: it equals `1` on
`{a ≤ |x| ≤ b}`, takes values in `[0, 1]`, and vanishes off `{a / 2 ≤ |x| ≤ 3 b / 2}`. -/
noncomputable def annulusBump (a b : ℝ) (x : ℂ) : ℝ :=
  max 0 (min 1 (min (3 - 2 * (‖x‖ / b)) (2 * (‖x‖ / a) - 1)))

lemma continuous_annulusBump (a b : ℝ) : Continuous (annulusBump a b) :=
  continuous_const.max (continuous_const.min
    ((continuous_const.sub (continuous_const.mul (continuous_norm.div_const b))).min
      ((continuous_const.mul (continuous_norm.div_const a)).sub continuous_const)))

lemma annulusBump_nonneg (a b : ℝ) (x : ℂ) : 0 ≤ annulusBump a b x :=
  le_max_left _ _

lemma annulusBump_le_one (a b : ℝ) (x : ℂ) : annulusBump a b x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma annulusBump_eq_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℂ} (h1 : a ≤ ‖x‖) (h2 : ‖x‖ ≤ b) :
    annulusBump a b x = 1 := by
  have hb1 : ‖x‖ / b ≤ 1 := (div_le_one hb).2 h2
  have ha1 : 1 ≤ ‖x‖ / a := (le_div_iff₀ ha).2 (by linarith)
  unfold annulusBump
  rw [min_eq_left (le_min (by linarith) (by linarith)), max_eq_right zero_le_one]

lemma annulusBump_support {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℂ} (hx : annulusBump a b x ≠ 0) :
    a / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 3 * b / 2 := by
  refine ⟨not_lt.1 fun h => hx ?_, not_lt.1 fun h => hx ?_⟩
  · have h' : ‖x‖ / a < 1 / 2 := (div_lt_iff₀ ha).2 (by linarith)
    exact max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans (by linarith)))
  · have h' : 3 / 2 < ‖x‖ / b := (lt_div_iff₀ hb).2 (by linarith)
    exact max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans (by linarith)))

/-- **Tilted first moment of the LQG mass of an `e`-adic annulus about the origin.** For a whole-plane GFF `h^ℂ`,
`0 < γ < 2` and `0 < τ ≤ 1`, with `Γ` the cut-off γ-LQG measure of `h^ℂ - γ log |·|`:
`E[e^{-γ h^ℂ_τ(0)} Γ{τ / (2e) ≤ |x| ≤ τ / 2}] ≤ τ^{γ²/2} (τ / (4e))^{-γ²} π τ²`. -/
theorem lintegral_exp_neg_centredCircle_mul_gmcLimit_annulus_le {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [SFinite P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂)
    (hρ₂ : ρ₂ < 1) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∫⁻ ω', ENNReal.ofReal (Real.exp (-γ * hc ω' τ 0)) *
        gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')
          {x | τ / (2 * Real.exp 1) ≤ ‖x‖ ∧ ‖x‖ ≤ τ / 2} ∂P' ≤
      ENNReal.ofReal (τ ^ (γ ^ 2 / 2) * (τ / (2 * Real.exp 1) / 2) ^ (-γ ^ 2)) *
        ENNReal.ofReal (Real.pi * τ ^ 2) := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have ha : 0 < τ / (2 * Real.exp 1) := by positivity
  have hb : 0 < τ / 2 := by positivity
  have hab : τ / (2 * Real.exp 1) ≤ τ / 2 :=
    div_le_div_of_nonneg_left hτ.le two_pos (by linarith)
  have hA : MeasurableSet {x : ℂ | τ / (2 * Real.exp 1) ≤ ‖x‖ ∧ ‖x‖ ≤ τ / 2} :=
    (measurableSet_le measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)
  have hle : ∀ m : Measure ℂ, m {x : ℂ | τ / (2 * Real.exp 1) ≤ ‖x‖ ∧ ‖x‖ ≤ τ / 2} ≤
      ∫⁻ x, ENNReal.ofReal (annulusBump (τ / (2 * Real.exp 1)) (τ / 2) x) ∂m := by
    intro m
    rw [← lintegral_indicator_one hA]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ {x : ℂ | τ / (2 * Real.exp 1) ≤ ‖x‖ ∧ ‖x‖ ≤ τ / 2}
    · rw [indicator_of_mem hx, annulusBump_eq_one ha hb hx.1 hx.2, ENNReal.ofReal_one]
      rfl
    · rw [indicator_of_notMem hx]
      exact zero_le
  have hvol : ∫⁻ x, ENNReal.ofReal (annulusBump (τ / (2 * Real.exp 1)) (τ / 2) x) ≤
      ENNReal.ofReal (Real.pi * τ ^ 2) := by
    have hvb : volume (ball (0 : ℂ) τ) = ENNReal.ofReal (Real.pi * τ ^ 2) := by
      rw [Complex.volume_ball, ← ENNReal.ofReal_pow hτ.le, mul_comm (ENNReal.ofReal _),
        ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
    rw [← hvb, ← lintegral_indicator_one measurableSet_ball]
    refine lintegral_mono fun x => ?_
    by_cases hx : annulusBump (τ / (2 * Real.exp 1)) (τ / 2) x = 0
    · rw [hx, ENNReal.ofReal_zero]
      exact zero_le
    · have hxb : x ∈ ball (0 : ℂ) τ := by
        rw [mem_ball_zero_iff]
        linarith [(annulusBump_support ha hb hx).2]
      rw [indicator_of_mem hxb]
      exact ENNReal.ofReal_le_one.2 (annulusBump_le_one _ _ x)
  calc ∫⁻ ω', ENNReal.ofReal (Real.exp (-γ * hc ω' τ 0)) *
        gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')
          {x | τ / (2 * Real.exp 1) ≤ ‖x‖ ∧ ‖x‖ ≤ τ / 2} ∂P'
      ≤ ∫⁻ ω', ENNReal.ofReal (Real.exp (-γ * hc ω' τ 0)) *
          ∫⁻ x, ENNReal.ofReal (annulusBump (τ / (2 * Real.exp 1)) (τ / 2) x)
            ∂(gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')) ∂P' :=
        lintegral_mono fun ω' => by gcongr; exact hle _
    _ ≤ ENNReal.ofReal (τ ^ (γ ^ 2 / 2) * (τ / (2 * Real.exp 1) / 2) ^ (-γ ^ 2)) *
          ∫⁻ x, ENNReal.ofReal (annulusBump (τ / (2 * Real.exp 1)) (τ / 2) x) :=
        lintegral_exp_neg_centredCircle_mul_lintegral_gmcLimit_le hG hγ hγ2 hρρ₂ hρ₂
          (continuous_annulusBump _ _) (annulusBump_nonneg _ _) (by positivity) (by linarith)
          (by linarith) hτ1 fun x hx => annulusBump_support ha hb hx
    _ ≤ _ := by gcongr

end MatedCRT.KilledOccupation
