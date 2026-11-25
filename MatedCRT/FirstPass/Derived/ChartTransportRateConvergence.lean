import MatedCRT.FirstPass.Derived.ChartTransportedMeasure
import MatedCRT.FirstPass.Derived.ChartTransportMeasurable
import MatedCRT.FirstPass.Derived.DiscCanonicalRate
import LatticeProb.LQG.CompactBallLimitPower

/-!
# Convergence of the transported approximating rates

Let `ψ` be an inverse chart of the bounded open set `U` (a conformal map of `U` onto the unit disc, `φ = ψ⁻¹`), let
`h_ε` be circle averages of a field whose approximations `ε^{γ²/2} e^{γ h_ε(x)} dx` converge vaguely to the LQG
measure `μ` along `ε_n = 2^{-n}` (`IsLQGLimit`), and let

  `e_n(v) = (ε_n^{γ²/2} e^{γ h_{ε_n}(φ v)} + ε_n) / |ψ'(φ v)|²`

be the transported rates of the approximating LQG clocks (`chartTransportRate U ψ (lqgApproxRate γ h n)`).

* `e_n(v) dv → ψ_*(μ|_U)` vaguely on every closed disc `B̄(0, r)`, `r < 1`
  (`tendsto_integral_withDensity_chartTransportRate`): for `F` continuous with support in `B̄(0, r)`, the function
  `1_U · F ∘ ψ` is continuous with compact support (`IsInverseChart.continuous_indicator_comp`), and
  `∫ F e_n = ∫_U F(ψ x) (ε_n^{γ²/2} e^{γ h_{ε_n}(x)} + ε_n) dx`.
* A uniform upper power bound `μ_{ε_n}(B(x, t)) ≤ t^β` of the approximations at centers of a disc containing `U`
  passes to `e_n(v) dv` and to `ψ_*(μ|_U)` on `B(0, r)` with one exponent and one radius
  (`exists_chartTransportRate_ball_le_and_map_restrict_ball_le`), since `φ` is Lipschitz on `B̄(0, (1 + r)/2)`.
* The masses `∫_{B(0,1)} e_n = ∫_U (ε_n^{γ²/2} e^{γ h_{ε_n}} + ε_n)` are eventually bounded
  (`exists_eventually_withDensity_lqgApproxRate_le`, `withDensity_chartTransportRate_ball_one`).

These are the hypotheses of the uniform convergence of Green potentials on discs, the analytic input of the
identification of the limit of the transported clocks through the Revuz measure `ψ_*(μ|_U)` (Berestycki (2015),
Theorem 1.3; Armitage–Gardiner, §4.3).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-! ### Test functions pulled back by an inverse chart -/

/-- **Pulled-back test functions are continuous.** If `F` is continuous with support in `B̄(0, r)`, `r < 1`, then
`1_U · F ∘ ψ` is continuous: it vanishes near every point outside `U`, since `ψ` maps the frontier of `U` to the unit
circle. -/
theorem IsInverseChart.continuous_indicator_comp (hψ : IsInverseChart U z ψ) (hU : IsOpen U) {F : ℂ → ℝ}
    (hF : Continuous F) {r : ℝ} (hr : r < 1) (hFs : tsupport F ⊆ closedBall 0 r) :
    Continuous (U.indicator (F ∘ ψ)) := by
  have hWo : IsOpen (ψ ⁻¹' (closedBall (0 : ℂ) r)ᶜ ∪ (closure U)ᶜ) :=
    (isClosed_closedBall.isOpen_compl.preimage ψ.continuous).union isClosed_closure.isOpen_compl
  have hzero : ∀ y ∈ ψ ⁻¹' (closedBall (0 : ℂ) r)ᶜ ∪ (closure U)ᶜ, U.indicator (F ∘ ψ) y = 0 := by
    intro y hy
    rcases hy with hy | hy
    · by_cases hyU : y ∈ U
      · rw [indicator_of_mem hyU]
        show F (ψ y) = 0
        exact image_eq_zero_of_notMem_tsupport fun h => hy (hFs h)
      · exact indicator_of_notMem hyU _
    · exact indicator_of_notMem (fun h => hy (subset_closure h)) _
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact (continuousAt_congr (eventuallyEq_of_mem (hU.mem_nhds hx)
      fun y hy => (indicator_of_mem hy (F ∘ ψ)).symm)).1 (hF.comp ψ.continuous).continuousAt
  · have hxW : x ∈ ψ ⁻¹' (closedBall (0 : ℂ) r)ᶜ ∪ (closure U)ᶜ := by
      by_cases hxc : x ∈ closure U
      · refine Or.inl ?_
        have hfr : x ∈ frontier U := by
          rw [frontier, hU.interior_eq]
          exact ⟨hxc, hx⟩
        have hs : ψ x ∈ sphere (0 : ℂ) 1 := hψ.image_frontier ▸ mem_image_of_mem ψ hfr
        rw [mem_sphere_zero_iff_norm] at hs
        show ψ x ∉ closedBall (0 : ℂ) r
        rw [mem_closedBall_zero_iff, hs]
        exact not_le.2 hr
      · exact Or.inr hxc
    exact (continuousAt_congr (eventuallyEq_of_mem (hWo.mem_nhds hxW)
      fun y hy => (hzero y hy).symm)).1 continuousAt_const

/-- On a bounded set `U`, `1_U · G` has compact support. -/
theorem hasCompactSupport_indicator_of_isBounded (hUb : Bornology.IsBounded U) (G : ℂ → ℝ) :
    HasCompactSupport (U.indicator G) :=
  HasCompactSupport.intro hUb.isCompact_closure fun _ hx => indicator_of_notMem (fun h => hx (subset_closure h)) _

/-! ### The approximating rate as a measure -/

/-- `(ε_n^{γ²/2} e^{γ h_{ε_n}(x)} + ε_n) dx = μ_{ε_n} + ε_n dx`. -/
theorem withDensity_lqgApproxRate (γ : ℝ) (hε : ℝ → ℂ → ℝ) (n : ℕ) :
    (volume.withDensity fun x => ENNReal.ofReal (lqgApproxRate γ hε n x)) =
      lqgApprox γ hε (dyadicScale n) + ENNReal.ofReal (dyadicScale n) • volume := by
  have hε0 : 0 ≤ dyadicScale n := (dyadicScale_pos n).le
  have hsplit : (fun x => ENNReal.ofReal (lqgApproxRate γ hε n x)) =
      (fun x => ENNReal.ofReal (dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale n) x))) +
        fun _ => ENNReal.ofReal (dyadicScale n) := by
    funext x
    exact ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hε0 _) (Real.exp_pos _).le) hε0
  rw [hsplit, withDensity_add_right _ measurable_const, withDensity_const]
  rfl

theorem withDensity_lqgApproxRate_apply (γ : ℝ) (hε : ℝ → ℂ → ℝ) (n : ℕ) (A : Set ℂ) :
    volume.withDensity (fun x => ENNReal.ofReal (lqgApproxRate γ hε n x)) A =
      lqgApprox γ hε (dyadicScale n) A + ENNReal.ofReal (dyadicScale n) * volume A := by
  rw [withDensity_lqgApproxRate, Measure.add_apply, Measure.smul_apply, smul_eq_mul]

theorem integral_withDensity_lqgApproxRate {γ : ℝ} {hε : ℝ → ℂ → ℝ} {n : ℕ}
    (hcont : Continuous (hε (dyadicScale n))) {G : ℂ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G) :
    ∫ x, G x ∂(volume.withDensity fun x => ENNReal.ofReal (lqgApproxRate γ hε n x)) =
      ∫ x, G x ∂(lqgApprox γ hε (dyadicScale n)) + dyadicScale n * ∫ x, G x := by
  have hlf : IsFiniteMeasureOnCompacts (lqgApprox γ hε (dyadicScale n)) := by
    have : IsLocallyFiniteMeasure (lqgApprox γ hε (dyadicScale n)) := by
      unfold lqgApprox
      exact IsLocallyFiniteMeasure.withDensity_ofReal
        (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcont)))
    infer_instance
  have hGi : Integrable G (lqgApprox γ hε (dyadicScale n)) := hG.integrable_of_hasCompactSupport hGc
  have hGv : Integrable G volume := hG.integrable_of_hasCompactSupport hGc
  rw [withDensity_lqgApproxRate, integral_add_measure hGi (hGv.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, ENNReal.toReal_ofReal (dyadicScale_pos n).le, smul_eq_mul]

/-- **The approximating rates converge vaguely to the LQG measure.** -/
theorem tendsto_integral_withDensity_lqgApproxRate {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (hμ : IsLQGLimit γ hε μ) (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) {G : ℂ → ℝ}
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    Tendsto (fun n : ℕ => ∫ x, G x ∂(volume.withDensity fun x => ENNReal.ofReal (lqgApproxRate γ hε n x)))
      atTop (𝓝 (∫ x, G x ∂μ)) := by
  have hd : Tendsto (fun n : ℕ => dyadicScale n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h0 : Tendsto (fun n : ℕ => dyadicScale n * ∫ x, G x) atTop (𝓝 0) := by
    simpa using hd.mul_const (∫ x, G x)
  have h := (hμ.tendsto_integral G hG hGc).add h0
  rw [add_zero] at h
  exact Tendsto.congr (fun n => (integral_withDensity_lqgApproxRate (hcont n) hG hGc).symm) h

/-! ### Transported rates -/

/-- `∫ F(v) ρ̃(v) dv = ∫ 1_U(x) F(ψ x) ρ(x) dx` for `F` supported in a closed disc `B̄(0, r)`, `r < 1`. -/
theorem integral_withDensity_chartTransportRate (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (ρ : ℂ → ℝ)
    {F : ℂ → ℝ} (hF : Continuous F) {r : ℝ} (hr : r < 1) (hFs : tsupport F ⊆ closedBall 0 r) :
    ∫ v, F v ∂(volume.withDensity fun v => ENNReal.ofReal (chartTransportRate U ψ ρ v)) =
      ∫ x, U.indicator (F ∘ ψ) x ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  have hF0 : ∀ v, v ∉ ball (0 : ℂ) 1 → F v = 0 := fun v hv =>
    image_eq_zero_of_notMem_tsupport fun h => hv (closedBall_subset_ball hr (hFs h))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF0, restrict_withDensity measurableSet_ball,
    withDensity_chartTransportRate_eq_map hψ hU ρ,
    integral_map ψ.continuous.measurable.aemeasurable hF.aestronglyMeasurable,
    integral_indicator hU.measurableSet]
  rfl

/-- **The transported approximating rates converge vaguely to the image of the LQG measure.** For `F` continuous
with support in `B̄(0, r)`, `r < 1`: `∫ F e_n → ∫ F d(ψ_*(μ|_U))`. -/
theorem tendsto_integral_withDensity_chartTransportRate (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ} (hμ : IsLQGLimit γ hε μ)
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) {F : ℂ → ℝ} (hF : Continuous F) {r : ℝ} (hr : r < 1)
    (hFs : tsupport F ⊆ closedBall 0 r) :
    Tendsto (fun n : ℕ => ∫ v, F v ∂(volume.withDensity fun v =>
        ENNReal.ofReal (chartTransportRate U ψ (lqgApproxRate γ hε n) v)))
      atTop (𝓝 (∫ v, F v ∂((μ.restrict U).map ψ))) := by
  have hG := hψ.continuous_indicator_comp hU hF hr hFs
  have hGc := hasCompactSupport_indicator_of_isBounded hUb (F ∘ ψ)
  have hlim : ∫ v, F v ∂((μ.restrict U).map ψ) = ∫ x, U.indicator (F ∘ ψ) x ∂μ := by
    rw [integral_map ψ.continuous.measurable.aemeasurable hF.aestronglyMeasurable,
      integral_indicator hU.measurableSet]
    rfl
  rw [hlim]
  exact Tendsto.congr (fun n => (integral_withDensity_chartTransportRate hψ hU _ hF hr hFs).symm)
    (tendsto_integral_withDensity_lqgApproxRate hμ hcont hG hGc)

/-- **Disc masses of a transported rate.** With `φ` `L`-Lipschitz on `B̄(0, R)`, `R < 1`, and
`B̄(x, s) ⊆ B̄(0, R)`: `∫_{B(x,s)} ρ̃ ≤ ∫_{B(φ x, L s)} ρ`. -/
theorem withDensity_chartTransportRate_ball_le (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (ρ : ℂ → ℝ)
    {L R : ℝ} (hL0 : 0 < L) (hR : R < 1)
    (hL : ∀ v ∈ closedBall (0 : ℂ) R, ∀ w ∈ closedBall (0 : ℂ) R,
      ‖chartMap U ψ v - chartMap U ψ w‖ ≤ L * ‖v - w‖)
    {x : ℂ} {s : ℝ} (hs : 0 ≤ s) (hxs : closedBall x s ⊆ closedBall 0 R) :
    volume.withDensity (fun v => ENNReal.ofReal (chartTransportRate U ψ ρ v)) (ball x s) ≤
      volume.withDensity (fun y => ENNReal.ofReal (ρ y)) (ball (chartMap U ψ x) (L * s)) := by
  have hsub : ball x s ⊆ ball (0 : ℂ) 1 :=
    ball_subset_closedBall.trans (hxs.trans (closedBall_subset_ball hR))
  have h1 : volume.withDensity (fun v => ENNReal.ofReal (chartTransportRate U ψ ρ v)) (ball x s) =
      (volume.withDensity (fun v => ENNReal.ofReal (chartTransportRate U ψ ρ v))).restrict (ball 0 1)
        (ball x s) := by
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.2 hsub]
  rw [h1, restrict_withDensity measurableSet_ball, withDensity_chartTransportRate_eq_map hψ hU ρ]
  exact hψ.map_restrict_ball_le _ hL0 hL hs hxs

/-- The mass of a transported rate on the unit disc is the mass of the rate on `U`. -/
theorem withDensity_chartTransportRate_ball_one (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (ρ : ℂ → ℝ) :
    volume.withDensity (fun v => ENNReal.ofReal (chartTransportRate U ψ ρ v)) (ball 0 1) =
      volume.withDensity (fun x => ENNReal.ofReal (ρ x)) U := by
  rw [← Measure.restrict_apply_univ (ball (0 : ℂ) 1), restrict_withDensity measurableSet_ball,
    withDensity_chartTransportRate_eq_map hψ hU ρ, Measure.map_apply ψ.continuous.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

/-! ### Power bounds -/

/-- `K s^β ≤ s^{β/2}` for all small `s > 0`. -/
theorem exists_forall_mul_rpow_le_rpow_half {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) :
    ∃ s₁ > 0, ∀ s, 0 < s → s < s₁ → K * s ^ β ≤ s ^ (β / 2) := by
  obtain ⟨δ, hδ, hKδ⟩ := exists_pos_mul_rpow_lt hK (half_pos hβ) one_pos
  refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
  have h1 : s ^ β = s ^ (β / 2) * s ^ (β / 2) := by
    rw [← Real.rpow_add hs, add_halves]
  have h2 : s ^ (β / 2) ≤ δ ^ (β / 2) := Real.rpow_le_rpow hs.le hsδ.le (half_pos hβ).le
  have h3 : 0 ≤ s ^ (β / 2) := Real.rpow_nonneg hs.le _
  have h4 : K * s ^ (β / 2) ≤ 1 := ((mul_le_mul_of_nonneg_left h2 hK).trans hKδ.le)
  rw [h1]
  nlinarith [mul_nonneg h3 (sub_nonneg.2 h4)]

/-- `(L s)^β + π (L s)² ≤ s^q` for all small `s > 0`, with `q = min(β, 2)/2`. -/
theorem exists_forall_mul_rpow_add_le_rpow {L β : ℝ} (hL0 : 0 < L) (hβ : 0 < β) :
    ∃ q > (0 : ℝ), ∃ s₁ > 0, ∀ s, 0 < s → s < s₁ → (L * s) ^ β + Real.pi * (L * s) ^ 2 ≤ s ^ q := by
  set p : ℝ := min β 2 with hp
  have hp0 : 0 < p := lt_min hβ two_pos
  have hK0 : 0 ≤ (1 + Real.pi) * L ^ p :=
    mul_nonneg (by linarith [Real.pi_pos]) (Real.rpow_nonneg hL0.le _)
  obtain ⟨s₂, hs₂, hKs⟩ := exists_forall_mul_rpow_le_rpow_half hK0 hp0
  refine ⟨p / 2, half_pos hp0, min s₂ (1 / L), lt_min hs₂ (one_div_pos.2 hL0), fun s hs hs₁ => ?_⟩
  have hx0 : 0 < L * s := mul_pos hL0 hs
  have hx1 : L * s ≤ 1 := by
    have h := (lt_div_iff₀ hL0).1 (hs₁.trans_le (min_le_right _ _))
    linarith [mul_comm s L]
  have h1 : (L * s) ^ β ≤ (L * s) ^ p := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (min_le_left _ _)
  have h2 : (L * s) ^ 2 ≤ (L * s) ^ p := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (min_le_right _ _)
  have h3 : (L * s) ^ p = L ^ p * s ^ p := Real.mul_rpow hL0.le hs.le
  rw [h3] at h1 h2
  have h4 := hKs s hs (hs₁.trans_le (min_le_left _ _))
  have h5 := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  linarith

/-- **Uniform power bounds for the transported rates and the image of the LQG measure.** Let `U ⊆ B̄(0, R₁)` and
let the approximations satisfy `μ_{ε_n}(B(x, t)) ≤ t^β` for all `n`, `x ∈ B̄(0, R₁)` and `t < t₀`. Then for
`r < 1` there are `q, s₁ > 0` such that, for all `n`, `v ∈ B(0, r)` and `s < s₁`, `∫_{B(v,s)} e_n ≤ s^q` and
`ψ_*(μ|_U)(B(v, s)) ≤ s^q`. -/
theorem exists_chartTransportRate_ball_le_and_map_restrict_ball_le (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ} (hμ : IsLQGLimit γ hε μ)
    {R₁ β t₀ : ℝ} (hβ : 0 < β) (ht₀ : 0 < t₀) (hU₁ : U ⊆ closedBall 0 R₁)
    (hpow : ∀ n : ℕ, ∀ x ∈ closedBall (0 : ℂ) R₁, ∀ t, 0 < t → t < t₀ →
      lqgApprox γ hε (dyadicScale n) (ball x t) ≤ ENNReal.ofReal (t ^ β))
    {r : ℝ} (hr : r < 1) :
    ∃ q > (0 : ℝ), ∃ s₁ > 0, (∀ n : ℕ, ∀ s, 0 < s → s < s₁ → ∀ v ∈ ball (0 : ℂ) r,
      volume.withDensity (fun v => ENNReal.ofReal (chartTransportRate U ψ (lqgApproxRate γ hε n) v))
        (ball v s) ≤ ENNReal.ofReal (s ^ q)) ∧
      ∀ s, 0 < s → s < s₁ → ∀ v ∈ ball (0 : ℂ) r, (μ.restrict U).map ψ (ball v s) ≤ ENNReal.ofReal (s ^ q) := by
  have hR : (r + 1) / 2 < 1 := by linarith
  obtain ⟨L, hL0, hL⟩ := hψ.exists_norm_chartMap_sub_le hU hUb hR
  obtain ⟨q, hq, s₂, hs₂, hreal⟩ := exists_forall_mul_rpow_add_le_rpow hL0 hβ
  have hvague : QuantumZipper.IsVagueLimitOn univ (fun k => lqgApprox γ hε (dyadicScale k)) μ := by
    refine ⟨by simp, fun S hS _ => ?_, fun f hf hfc _ => hμ.tendsto_integral f hf hfc⟩
    have := hμ.isLocallyFiniteMeasure
    exact hS.measure_lt_top
  have key : ∀ s, 0 < s → s < min s₂ (min ((1 - r) / 2) (t₀ / L)) → ∀ v ∈ ball (0 : ℂ) r,
      closedBall v s ⊆ closedBall 0 ((r + 1) / 2) ∧ chartMap U ψ v ∈ closedBall 0 R₁ ∧ L * s < t₀ ∧
        (L * s) ^ β + Real.pi * (L * s) ^ 2 ≤ s ^ q := by
    intro s hs hs₁ v hv
    have hsr : s < (1 - r) / 2 := hs₁.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hst : s < t₀ / L := hs₁.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hvr : ‖v‖ < r := mem_ball_zero_iff.1 hv
    refine ⟨fun w hw => ?_, hU₁ (hψ.chartMap_mem (ball_subset_ball hr.le hv)), ?_,
      hreal s hs (hs₁.trans_le (min_le_left _ _))⟩
    · rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_closedBall_zero_iff]
      have h1 := norm_sub_norm_le w v
      linarith
    · have h1 := (lt_div_iff₀ hL0).1 hst
      linarith [mul_comm s L]
  refine ⟨q, hq, min s₂ (min ((1 - r) / 2) (t₀ / L)),
    lt_min hs₂ (lt_min (by linarith) (div_pos ht₀ hL0)), fun n s hs hs₁ v hv => ?_, fun s hs hs₁ v hv => ?_⟩
  · obtain ⟨hxs, hφ, hLs, hbd⟩ := key s hs hs₁ v hv
    have hLs0 : 0 < L * s := mul_pos hL0 hs
    refine (withDensity_chartTransportRate_ball_le hψ hU _ hL0 hR hL hs.le hxs).trans ?_
    rw [withDensity_lqgApproxRate_apply, volume_ball_complex _ hLs0.le]
    have hd1 : ENNReal.ofReal (dyadicScale n) ≤ 1 :=
      ENNReal.ofReal_le_one.2 (show dyadicScale n ≤ 1 from pow_le_one₀ (by norm_num) (by norm_num))
    calc lqgApprox γ hε (dyadicScale n) (ball (chartMap U ψ v) (L * s)) +
          ENNReal.ofReal (dyadicScale n) * ENNReal.ofReal (Real.pi * (L * s) ^ 2)
        ≤ ENNReal.ofReal ((L * s) ^ β) + 1 * ENNReal.ofReal (Real.pi * (L * s) ^ 2) := by
          gcongr
          exact hpow n _ hφ _ hLs0 hLs
      _ = ENNReal.ofReal ((L * s) ^ β + Real.pi * (L * s) ^ 2) := by
          rw [one_mul, ENNReal.ofReal_add (Real.rpow_nonneg hLs0.le _) (by positivity)]
      _ ≤ ENNReal.ofReal (s ^ q) := ENNReal.ofReal_le_ofReal hbd
  · obtain ⟨hxs, hφ, hLs, hbd⟩ := key s hs hs₁ v hv
    have hLs0 : 0 < L * s := mul_pos hL0 hs
    refine (hψ.map_restrict_ball_le μ hL0 hL hs.le hxs).trans ?_
    have hμb : μ (ball (chartMap U ψ v) (L * s)) ≤ ENNReal.ofReal ((L * s) ^ β) := by
      refine LatticeProb.LQG.measure_open_le_of_isVagueLimitOn hvague isOpen_ball isBounded_ball ?_
        fun k => hpow k _ hφ _ hLs0 hLs
      refine ⟨chartMap U ψ v + ((L * s + 1 : ℝ) : ℂ), ?_⟩
      simp only [mem_compl_iff, mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (show (0 : ℝ) ≤ L * s + 1 by linarith), not_lt]
      linarith
    refine hμb.trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ Real.pi * (L * s) ^ 2 := by positivity
    linarith

/-! ### Mass bounds -/

/-- A continuous plateau: `1` on `B̄(0, R)`, `0` off `B(0, R + 1)`. -/
noncomputable def discPlateau (R : ℝ) (x : ℂ) : ℝ := max 0 (min 1 (R + 1 - ‖x‖))

theorem continuous_discPlateau (R : ℝ) : Continuous (discPlateau R) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))

theorem discPlateau_nonneg (R : ℝ) (x : ℂ) : 0 ≤ discPlateau R x := le_max_left _ _

theorem hasCompactSupport_discPlateau (R : ℝ) : HasCompactSupport (discPlateau R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 1)) fun x hx => ?_
  rw [mem_closedBall_zero_iff, not_le] at hx
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem discPlateau_eq_one {R : ℝ} {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) : discPlateau R x = 1 := by
  rw [mem_closedBall_zero_iff] at hx
  unfold discPlateau
  rw [min_eq_left (by linarith)]
  exact max_eq_right zero_le_one

theorem measure_closedBall_le_integral_discPlateau (R : ℝ) (m : Measure ℂ) [IsFiniteMeasureOnCompacts m] :
    m (closedBall 0 R) ≤ ENNReal.ofReal (∫ x, discPlateau R x ∂m) := by
  rw [ofReal_integral_eq_lintegral_ofReal ((continuous_discPlateau R).integrable_of_hasCompactSupport
      (hasCompactSupport_discPlateau R)) (ae_of_all _ fun x => discPlateau_nonneg R x),
    ← lintegral_indicator_one measurableSet_closedBall]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ closedBall (0 : ℂ) R
  · rw [indicator_of_mem hx, Pi.one_apply, discPlateau_eq_one hx, ENNReal.ofReal_one]
  · rw [indicator_of_notMem hx]
    exact zero_le

/-- **The masses of the approximating rates on a bounded set are eventually bounded.** -/
theorem exists_eventually_withDensity_lqgApproxRate_le {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (hμ : IsLQGLimit γ hε μ) (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) {A : Set ℂ}
    (hA : Bornology.IsBounded A) :
    ∃ M : ℝ, ∀ᶠ n in atTop,
      volume.withDensity (fun x => ENNReal.ofReal (lqgApproxRate γ hε n x)) A ≤ ENNReal.ofReal M := by
  obtain ⟨R, hR⟩ := hA.subset_closedBall 0
  have hG := tendsto_integral_withDensity_lqgApproxRate hμ hcont (continuous_discPlateau R)
    (hasCompactSupport_discPlateau R)
  refine ⟨∫ x, discPlateau R x ∂μ + 1, ?_⟩
  filter_upwards [(tendsto_order.1 hG).2 _ (lt_add_one _)] with n hn
  have hlf : IsFiniteMeasureOnCompacts
      (volume.withDensity fun x => ENNReal.ofReal (lqgApproxRate γ hε n x)) := by
    have : IsLocallyFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (lqgApproxRate γ hε n x)) :=
      IsLocallyFiniteMeasure.withDensity_ofReal (continuous_lqgApproxRate (hcont n))
    infer_instance
  exact (measure_mono hR).trans ((measure_closedBall_le_integral_discPlateau R _).trans
    (ENNReal.ofReal_le_ofReal hn.le))

end MatedCRT
