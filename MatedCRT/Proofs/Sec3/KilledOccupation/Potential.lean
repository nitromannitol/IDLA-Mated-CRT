import Mathlib
import HarmonicBalls.Defs.Green
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Defs.LBM
import MatedCRT.Proofs.Sec3.KilledOccupation.WeightIdentity

/-!
# Potential bound for the disk occupation clock (Appendix B, step S3)

Source: `paper/appendix-occupation-C16.tex`, eq:occ-potential (lines 262-270): the supremum over `v ∈ D`
of `∫_D G_D(v,x) μ_h(dx)` is finite, derived there from the Green bound `2 G_D(v,x) ≤ C_D (1 + log⁺(1/|v-x|))`
(consequence of eq:occ-green, lines 44-47) and the mass bound eq:occ-mass (lines 245-250) by a dyadic annulus
sum. Here the annulus sum is replaced by the layer-cake formula `lintegral_eq_lintegral_meas_lt` together with
the exponential form `log(4/|v-x|) > t ⇔ |v-x| < 4 e^{-t}`.

The Green function is `HarmonicBalls.greenFunction` (HB `Defs/Green.lean:70`, normalized `ΔG = -δ`).
The explicit disk formula eq:occ-green is the Prop `GreenDiskFormula` (a hypothesis of the theorem below;
source: tex:44-47, Armitage-Gardiner §4.1 as cited in HB `Defs/Green.lean`).
The mass bound enters as the hypothesis `hmass`, which is the conclusion of `ae_ballMass_le_rpow`
(`WeightIdentity.lean`, tex:245-250).
-/

noncomputable section

open MeasureTheory Metric Filter Set Real
open scoped ENNReal

namespace MatedCRT.KilledOccupation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The explicit Green function of the disk `B_r(z)` (paper eq:occ-green, tex:44-47): for `v ≠ x` in the disk,
`G(v,x) = (2π)⁻¹ log |(1 - ā b)/(a - b)|` with `a = (v - z)/r`, `b = (x - z)/r`. Hypothesis; source tex:44-47. -/
def GreenDiskFormula (z : ℂ) (r : ℝ) : Prop :=
  ∀ v ∈ ball z r, ∀ x ∈ ball z r, v ≠ x →
    HarmonicBalls.greenFunction (ball z r) v x =
      (2 * π)⁻¹ * Real.log (‖1 - (starRingEnd ℂ) ((v - z) / r) * ((x - z) / r)‖ /
        ‖(v - z) / r - (x - z) / r‖)

lemma norm_div_radius_lt_one {z w : ℂ} {r : ℝ} (hr : 0 < r) (hw : w ∈ ball z r) :
    ‖(w - z) / r‖ < 1 := by
  rw [mem_ball, dist_eq_norm] at hw
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_lt_one hr]
  exact hw

/-- The disk Green function is bounded by `(2π)⁻¹ log(4/|v-x|)` (tex:262-263: the logarithmic Green bound). -/
lemma greenFunction_disk_le_log {z : ℂ} {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hG : GreenDiskFormula z r)
    {v x : ℂ} (hv : v ∈ ball z r) (hx : x ∈ ball z r) (hvx : v ≠ x) :
    HarmonicBalls.greenFunction (ball z r) v x ≤ (2 * π)⁻¹ * Real.log (4 / ‖v - x‖) := by
  rw [hG v hv x hx hvx]
  have hdpos : 0 < ‖v - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hvx)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have ha : ‖(v - z) / r‖ < 1 := norm_div_radius_lt_one hr hv
  have hb : ‖(x - z) / r‖ < 1 := norm_div_radius_lt_one hr hx
  set a := (v - z) / r with ha_def
  set b := (x - z) / r with hb_def
  have hnum : 0 < ‖1 - (starRingEnd ℂ) a * b‖ := by
    rw [norm_pos_iff]
    intro h0
    have h1 : (starRingEnd ℂ) a * b = 1 := by linear_combination -h0
    have h2 : ‖(starRingEnd ℂ) a‖ * ‖b‖ = 1 := by rw [← norm_mul, h1, norm_one]
    rw [Complex.norm_conj] at h2
    have : ‖a‖ * ‖b‖ < 1 := by nlinarith [norm_nonneg a, norm_nonneg b]
    linarith
  have hnum2 : ‖1 - (starRingEnd ℂ) a * b‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) ((starRingEnd ℂ) a * b)
    rw [norm_one, norm_mul, Complex.norm_conj] at h
    nlinarith [norm_nonneg a, norm_nonneg b]
  have hden : ‖a - b‖ = ‖v - x‖ / r := by
    rw [ha_def, hb_def, ← sub_div, sub_sub_sub_cancel_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hab : 0 < ‖a - b‖ := by rw [hden]; positivity
  calc Real.log (‖1 - (starRingEnd ℂ) a * b‖ / ‖a - b‖)
      ≤ Real.log (2 / ‖a - b‖) :=
        Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hnum2 hab.le)
    _ = Real.log (2 * r / ‖v - x‖) := by rw [hden]; congr 1; field_simp
    _ ≤ Real.log (4 / ‖v - x‖) :=
        Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith) hdpos.le)

lemma log_four_div_nonneg {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 4) : 0 ≤ Real.log (4 / d) := by
  rcases eq_or_lt_of_le hd0 with h | h
  · rw [← h, div_zero, Real.log_zero]
  · apply Real.log_nonneg
    rw [le_div_iff₀ h]
    linarith

lemma dist_lt_of_lt_log {d t : ℝ} (hd : 0 ≤ d) (ht : 0 < t) (h : t < Real.log (4 / d)) :
    d < 4 * Real.exp (-t) := by
  rcases eq_or_lt_of_le hd with h0 | hpos
  · rw [← h0, div_zero, Real.log_zero] at h
    linarith
  · rw [Real.lt_log_iff_exp_lt (by positivity)] at h
    rw [Real.exp_neg]
    have h1 : Real.exp t * d < 4 := by
      rwa [lt_div_iff₀ hpos] at h
    have h2 : 0 < Real.exp t := Real.exp_pos t
    rw [← div_eq_mul_inv, lt_div_iff₀ h2]
    linarith

/-- **eq:occ-potential** (tex:262-270), in the form used by the clock identification. Assume the Green disk
formula (tex:44-47) on `D = B_r(z)`, `D ⊆ B_ρ`, and the mass bound (eq:occ-mass, tex:245-250) with exponent
`b > 0` on the centres `B_{ρ₁}` (`ρ < ρ₁ < 1`). Then almost surely there is `K` with
`∫_D G_D(v,x) μ_h(dx) ≤ K` for every `v ∈ D`. The finite-mass fact `μ_h(D) < ∞` is proved from the
mass bound by a finite cover of the compact closed ball. -/
theorem ae_sup_greenPotential_finite (P : Measure Ω) (μ : Ω → Measure ℂ) {b ρ ρ₁ : ℝ} (hb : 0 < b)
    (hρ₁ : ρ₁ < 1) (hρρ₁ : ρ < ρ₁)
    (hmass : ∀ᵐ ω ∂P, ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ v ∈ ball (0 : ℂ) ρ₁, ∀ a : ℝ, 0 < a → a < r₀ →
      μ ω (ball v a) ≤ ENNReal.ofReal (C * a ^ b))
    (z : ℂ) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hD : ball z r ⊆ ball 0 ρ)
    (hG : GreenDiskFormula z r) :
    ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ v ∈ ball z r,
      ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) v x) ∂(μ ω) ≤
        ENNReal.ofReal K := by
  filter_upwards [hmass] with ω hω
  obtain ⟨C₀, r₀, hr₀, hbound⟩ := hω
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = |C₀| := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; exact abs_nonneg _
  have hbound' : ∀ v ∈ ball (0 : ℂ) ρ₁, ∀ a : ℝ, 0 < a → a < r₀ →
      μ ω (ball v a) ≤ ENNReal.ofReal (C * a ^ b) := by
    intro v hv a ha hae
    refine (hbound v hv a ha hae).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hCdef]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg ha.le _)
  have hρ1 : ρ < 1 := lt_trans hρρ₁ hρ₁
  have hr2 : r ≤ 2 := by linarith
  have hDρ : ∀ x ∈ ball z r, x ∈ ball (0 : ℂ) ρ₁ := fun x hx => ball_subset_ball hρρ₁.le (hD hx)
  have hdiam : ∀ v ∈ ball z r, ∀ x ∈ ball z r, ‖v - x‖ < 2 := by
    intro v hv x hx
    rw [mem_ball, dist_eq_norm] at hv hx
    have : ‖v - x‖ ≤ ‖v - z‖ + ‖x - z‖ := by
      calc ‖v - x‖ = ‖(v - z) - (x - z)‖ := by ring_nf
        _ ≤ ‖v - z‖ + ‖x - z‖ := norm_sub_le _ _
    linarith
  -- finite mass of the disk, from the mass bound on a finite cover
  have hMfin : μ ω (ball z r) ≠ ⊤ := by
    obtain ⟨t, hts, htfin, hcov⟩ :=
      finite_cover_balls_of_compact (isCompact_closedBall (0 : ℂ) ρ) (half_pos hr₀)
    have hsub : ball z r ⊆ ⋃ x ∈ htfin.toFinset, ball x (r₀ / 2) := by
      intro w hw
      have hw' : w ∈ closedBall (0 : ℂ) ρ := ball_subset_closedBall (hD hw)
      have := hcov hw'
      simpa using this
    have hterm : ∀ x ∈ htfin.toFinset, μ ω (ball x (r₀ / 2)) ≠ ⊤ := by
      intro x hx
      have hxt : x ∈ ball (0 : ℂ) ρ₁ := by
        have h1 := hts (htfin.mem_toFinset.1 hx)
        rw [mem_closedBall, dist_zero_right] at h1
        rw [mem_ball, dist_zero_right]
        linarith
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (hbound' x hxt (r₀ / 2) (half_pos hr₀) (by linarith))
    have hfin : μ ω (⋃ x ∈ htfin.toFinset, ball x (r₀ / 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 hterm) (measure_biUnion_finset_le _ _)
    exact ne_top_of_le_ne_top hfin (measure_mono hsub)
  -- constants of the layer-cake estimate
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (μ ω (ball z r)).toReal := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact ENNReal.toReal_nonneg
  have hMeq : ENNReal.ofReal M = μ ω (ball z r) := by rw [hM, ENNReal.ofReal_toReal hMfin]
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.log (4 / r₀) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = M * Real.exp (b * T) + C * 4 ^ b := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    have : 0 ≤ C * (4 : ℝ) ^ b := mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _)
    positivity
  -- pointwise tail estimate: μ(D ∩ {t < log(4/|v-x|)}) ≤ A e^{-bt}
  have hcount : ∀ v ∈ ball z r, ∀ t : ℝ, 0 < t →
      (μ ω).restrict (ball z r) {x | t < Real.log (4 / ‖v - x‖)} ≤
        ENNReal.ofReal (A * Real.exp (-b * t)) := by
    intro v hv t ht
    rw [Measure.restrict_apply' measurableSet_ball]
    have hvρ : v ∈ ball (0 : ℂ) ρ₁ := hDρ v hv
    rcases le_or_gt t T with htT | htT
    · -- t ≤ T: the set is contained in the disk, bounded by its mass
      have hMle : ENNReal.ofReal M ≤ ENNReal.ofReal (A * Real.exp (-b * t)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ Real.exp (b * T) * Real.exp (-b * t) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        have h2 : A * Real.exp (-b * t)
            = M * (Real.exp (b * T) * Real.exp (-b * t)) + C * 4 ^ b * Real.exp (-b * t) := by
          rw [hA]; ring
        have h3 : 0 ≤ C * 4 ^ b * Real.exp (-b * t) := by
          have : 0 ≤ C * (4 : ℝ) ^ b := mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _)
          positivity
        have h4 : M ≤ M * (Real.exp (b * T) * Real.exp (-b * t)) := le_mul_of_one_le_right hM0 h1
        linarith
      calc μ ω ({x | t < Real.log (4 / ‖v - x‖)} ∩ ball z r) ≤ μ ω (ball z r) :=
            measure_mono inter_subset_right
        _ = ENNReal.ofReal M := hMeq.symm
        _ ≤ ENNReal.ofReal (A * Real.exp (-b * t)) := hMle
    · -- t > T: the set lies in a ball of radius `4 e^{-t} < r₀`
      have hsmall : 4 * Real.exp (-t) < r₀ := by
        have h1 : Real.exp (-t) < Real.exp (-T) := Real.exp_lt_exp.2 (by linarith)
        have h2 : Real.exp (-T) = r₀ / 4 := by
          rw [hT, Real.exp_neg, Real.exp_log (by positivity)]
          field_simp
        linarith
      have hsub : {x | t < Real.log (4 / ‖v - x‖)} ∩ ball z r ⊆ ball v (4 * Real.exp (-t)) := by
        intro x hx
        rw [mem_ball, dist_eq_norm, ← norm_neg, neg_sub]
        exact dist_lt_of_lt_log (norm_nonneg _) ht hx.1
      have hpow : (4 * Real.exp (-t)) ^ b = 4 ^ b * Real.exp (-b * t) := by
        rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
        congr 2
        ring
      calc μ ω ({x | t < Real.log (4 / ‖v - x‖)} ∩ ball z r)
          ≤ μ ω (ball v (4 * Real.exp (-t))) := measure_mono hsub
        _ ≤ ENNReal.ofReal (C * (4 * Real.exp (-t)) ^ b) :=
            hbound' v hvρ _ (by positivity) hsmall
        _ ≤ ENNReal.ofReal (A * Real.exp (-b * t)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hpow]
            have h2 : A * Real.exp (-b * t)
                = M * (Real.exp (b * T) * Real.exp (-b * t)) + C * 4 ^ b * Real.exp (-b * t) := by
              rw [hA]; ring
            have h3 : 0 ≤ M * (Real.exp (b * T) * Real.exp (-b * t)) := by positivity
            linarith
  -- the dominating integral is finite
  have hint : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (A * Real.exp (-b * t)) ≠ ⊤ := by
    have hi : Integrable (fun t : ℝ => A * Real.exp (-b * t)) (volume.restrict (Ioi (0 : ℝ))) :=
      (exp_neg_integrableOn_Ioi 0 hb).const_mul A
    have hnn : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ A * Real.exp (-b * t) :=
      ae_of_all _ (fun t => mul_nonneg hA0 (Real.exp_pos _).le)
    rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
    exact ENNReal.ofReal_ne_top
  refine ⟨(ENNReal.ofReal ((2 * π)⁻¹) *
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (A * Real.exp (-b * t))).toReal, fun v hv => ?_⟩
  have hfin : ENNReal.ofReal ((2 * π)⁻¹) *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (A * Real.exp (-b * t)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hint
  rw [ENNReal.ofReal_toReal hfin]
  -- pointwise Green bound on the disk (the diagonal value of `greenFunction` is `0`)
  have hGle : ∀ x ∈ ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) v x) ≤
      ENNReal.ofReal ((2 * π)⁻¹) * ENNReal.ofReal (Real.log (4 / ‖v - x‖)) := by
    intro x hx
    by_cases hxv : x = v
    · have hdiag : HarmonicBalls.greenFunction (ball z r) v v = 0 := by
        unfold HarmonicBalls.greenFunction
        simp
      rw [hxv, hdiag, ENNReal.ofReal_zero]
      exact zero_le
    · rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal
        (greenFunction_disk_le_log hr hr2 hG hv hx (Ne.symm hxv))
  have hbound_D : ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) v x) ∂(μ ω)
      ≤ ∫⁻ x in ball z r, ENNReal.ofReal ((2 * π)⁻¹) * ENNReal.ofReal (Real.log (4 / ‖v - x‖))
          ∂(μ ω) :=
    setLIntegral_mono' measurableSet_ball hGle
  -- layer cake for the logarithmic kernel on the disk
  have hlayer : ∫⁻ x in ball z r, ENNReal.ofReal (Real.log (4 / ‖v - x‖)) ∂(μ ω)
      = ∫⁻ t in Ioi (0 : ℝ), (μ ω).restrict (ball z r) {x | t < Real.log (4 / ‖v - x‖)} := by
    refine lintegral_eq_lintegral_meas_lt _ ?_ ?_
    · exact (ae_restrict_mem measurableSet_ball).mono fun x hx =>
        log_four_div_nonneg (norm_nonneg _) (by linarith [hdiam v hv x hx])
    · exact (show Measurable (fun x : ℂ => Real.log (4 / ‖v - x‖)) by fun_prop).aemeasurable
  have hlayer_le : ∫⁻ t in Ioi (0 : ℝ), (μ ω).restrict (ball z r) {x | t < Real.log (4 / ‖v - x‖)}
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (A * Real.exp (-b * t)) :=
    setLIntegral_mono' measurableSet_Ioi (fun t ht => hcount v hv t ht)
  calc ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) v x) ∂(μ ω)
      ≤ ∫⁻ x in ball z r, ENNReal.ofReal ((2 * π)⁻¹) * ENNReal.ofReal (Real.log (4 / ‖v - x‖))
          ∂(μ ω) := hbound_D
    _ = ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ x in ball z r, ENNReal.ofReal (Real.log (4 / ‖v - x‖))
          ∂(μ ω) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((2 * π)⁻¹) *
          ∫⁻ t in Ioi (0 : ℝ), (μ ω).restrict (ball z r) {x | t < Real.log (4 / ‖v - x‖)} := by
        rw [hlayer]
    _ ≤ ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (A * Real.exp (-b * t)) :=
        mul_le_mul_of_nonneg_left hlayer_le (by positivity)

/-- **Step S0** (tex:48-52): the ordinary Brownian occupation identity for standard planar Brownian motion
(generator `½Δ`, `planarBrownianMotion`) killed on exiting the disk: for `y ∈ B_r(z)` and bounded measurable `f`,
`E_y ∫_0^τ f(B_t) dt = 2 ∫_{B_r(z)} G(y,x) f(x) dx`, with `G` the Green function `ΔG = -δ` (HB `greenFunction`).
No proof exists in the repository: the MarkovProcess killed-process files give exit-time facts only, and grep found
no generator or Dynkin occupation identity. Consumers take this Prop as a hypothesis of the exact type. -/
def KilledBrownianOccupationOnBall (z : ℂ) (r : ℝ) : Prop :=
  ∀ y ∈ ball z r, ∀ f : ℂ → ℝ, Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
    ∫ b, (∫ t in Ioc (0 : ℝ) (HarmonicBalls.pathExitTime (ball z r) b).toReal, f (b t.toNNReal))
        ∂HarmonicBalls.planarBrownianMotion y
      = 2 * ∫ x in ball z r, HarmonicBalls.greenFunction (ball z r) y x * f x

/-- The S2 mass bound feeds the potential bound: under the eq:occ-BGmass hypothesis (exponent `b`), the disk
Green potential is almost surely bounded (tex:262-270). -/
theorem ae_sup_greenPotential_of_BGMass (P : Measure Ω) (μ : Ω → Measure ℂ) {b ρ ρ₁ : ℝ} (hb : 0 < b)
    (hρ₁ : ρ₁ < 1) (hρρ₁ : ρ < ρ₁) (hBG : BGMassUpperBoundDyadic P μ b)
    (z : ℂ) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hD : ball z r ⊆ ball 0 ρ)
    (hG : GreenDiskFormula z r) :
    ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ v ∈ ball z r,
      ∫⁻ x in ball z r, ENNReal.ofReal (HarmonicBalls.greenFunction (ball z r) v x) ∂(μ ω) ≤
        ENNReal.ofReal K :=
  ae_sup_greenPotential_finite P μ hb hρ₁ hρρ₁ (ae_ballMass_le_rpow P μ hb hρ₁ hBG) z hr hrρ hD hG

end MatedCRT.KilledOccupation
