import HarmonicBalls.Proofs.Potential.GreenPotentialHolder

/-!
# Uniform convergence of Green potentials on a disc

Let `ν_n, ν` be measures on `ℂ` with a common upper power growth `ν(B(z, r)) ≤ r^β` (`z ∈ B_R = B(0, R)`,
`r < r₀`) and a common mass bound `ν(B_R) ≤ m`, and let `ν_n → ν` vaguely on `B_R` (for every continuous `F`
with support in the closed disc, `∫ F dν_n → ∫ F dν`). Then the Green potentials `G_{B_R} ν_n(x) = ∫ G_{B_R}(x, y)
ν_n(dy)` converge to `G_{B_R} ν(x)` uniformly on the closed disc
(`eventually_forall_abs_greenPotential_ball_sub_lt`).

The proof has three steps.
* The potentials are uniformly Hölder on the closed disc (`abs_greenPotential_ball_sub_le`, from the Hölder estimate
  of the harmonic-balls formalization, `HarmonicBalls.greenPotential_ball_holder_of_upper`, whose constant is
  monotone in the mass).
* At a fixed point `x` the kernel is split by the cutoff `φ_s` (`annulusCutoff`, `0` on `B(x, s/2)`, `1` off
  `B(x, s)`): `G(x, ·) φ_s` is continuous with support in the closed disc, so its integrals converge, and the rest
  is at most `C s^{α/2}` uniformly, by the logarithmic bound `G_{B_R}(x, y) ≤ (2π a)⁻¹ (2R)^a |x - y|^{-a}`
  (`greenFunction_ball_le_rpow`) and the Riesz potential bound of `|x - y|^{-α}` under the power growth.
* Equicontinuity and pointwise convergence on the compact closed disc give uniform convergence (finite net).

This is the convergence of potentials behind the identification of the time change of killed Brownian motion
through its Revuz measure (Armitage–Gardiner, §4.3; Berestycki (2015), Theorem 1.3).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology
open scoped NNReal ENNReal ComplexConjugate

namespace MatedCRT

open HarmonicBalls

/-! ### A logarithmic bound for the Green function of a disc -/

/-- `G_{B_R}(x, y) ≤ (2π a)⁻¹ (2R)^a |x - y|^{-a}` for `x ∈ B_R`, every `y` and every `a > 0`. -/
theorem greenFunction_ball_le_rpow {R a : ℝ} (ha : 0 < a) {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) (y : ℂ) :
    greenFunction (ball 0 R) x y ≤ (2 * Real.pi * a)⁻¹ * (2 * R) ^ a * ‖x - y‖ ^ (-a) := by
  have hR : 0 < R := (norm_nonneg x).trans_lt (mem_ball_zero_iff.1 hx)
  have h2π : 0 < 2 * Real.pi * a := mul_pos (by positivity) ha
  have hrhs : 0 ≤ (2 * Real.pi * a)⁻¹ * (2 * R) ^ a * ‖x - y‖ ^ (-a) :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 h2π.le) (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hy : y ∈ ball (0 : ℂ) R
  · rcases eq_or_ne x y with rfl | hxy
    · rw [greenFunction_self]
      exact hrhs
    rw [greenFunction_ball hx hy hxy, greenBall]
    have hd : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have hnum : 0 < ‖(R : ℂ) ^ 2 - conj x * y‖ :=
      norm_sub_conj_mul_pos hR (mem_ball_zero_iff.1 hx) (mem_ball_zero_iff.1 hy).le
    have hle : ‖(R : ℂ) ^ 2 - conj x * y‖ ≤ 2 * R ^ 2 := by
      calc ‖(R : ℂ) ^ 2 - conj x * y‖ ≤ ‖(R : ℂ) ^ 2‖ + ‖conj x * y‖ := norm_sub_le _ _
        _ = R ^ 2 + ‖x‖ * ‖y‖ := by
            rw [norm_mul, Complex.norm_conj, ← Complex.ofReal_pow, Complex.norm_real,
              Real.norm_of_nonneg (sq_nonneg R)]
        _ ≤ R ^ 2 + R * R := add_le_add le_rfl (mul_le_mul (mem_ball_zero_iff.1 hx).le
            (mem_ball_zero_iff.1 hy).le (norm_nonneg _) hR.le)
        _ = 2 * R ^ 2 := by ring
    have harg : ‖(R : ℂ) ^ 2 - conj x * y‖ / (R * ‖x - y‖) ≤ 2 * R / ‖x - y‖ := by
      rw [div_le_div_iff₀ (mul_pos hR hd) hd]
      nlinarith [mul_le_mul_of_nonneg_right hle hd.le]
    have hlog : Real.log (‖(R : ℂ) ^ 2 - conj x * y‖ / (R * ‖x - y‖)) ≤ (2 * R / ‖x - y‖) ^ a / a :=
      (Real.log_le_log (div_pos hnum (mul_pos hR hd)) harg).trans
        (Real.log_le_rpow_div (div_pos (show (0 : ℝ) < 2 * R by linarith) hd).le ha)
    have hpow : (2 * R / ‖x - y‖) ^ a = (2 * R) ^ a * ‖x - y‖ ^ (-a) := by
      rw [Real.div_rpow (show (0 : ℝ) ≤ 2 * R by linarith) hd.le, Real.rpow_neg hd.le, div_eq_mul_inv]
    rw [hpow] at hlog
    refine (mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ (2 * Real.pi)⁻¹ by positivity)).trans
      (le_of_eq ?_)
    ring
  · rw [greenFunction_of_notMem_right hy x]
    exact hrhs

/-! ### Constants -/

theorem greenPotentialRieszBound_mono {β r₀ m m' : ℝ} (hβ : 0 < β) (hr₀ : 0 < r₀) (hmm' : m ≤ m') :
    greenPotentialRieszBound β r₀ m ≤ greenPotentialRieszBound β r₀ m' := by
  have hα := greenPotentialHolderExponent_pos hβ
  have hαβ := greenPotentialHolderExponent_lt hβ
  have h2 : 0 ≤ greenPotentialHolderExponent β / (β - greenPotentialHolderExponent β) :=
    div_nonneg hα.le (sub_pos.2 hαβ).le
  have h3 : 0 ≤ (2 / r₀) ^ β := Real.rpow_nonneg (div_nonneg zero_le_two hr₀.le) _
  have h4 : m * (2 / r₀) ^ β ≤ m' * (2 / r₀) ^ β := mul_le_mul_of_nonneg_right hmm' h3
  unfold greenPotentialRieszBound volumeGrowthAllScalesConstant
  linarith [mul_le_mul_of_nonneg_right (add_le_add_left h4 (2 ^ β)) h2]

theorem greenPotentialHolderConstant_mono {β r₀ m m' : ℝ} (hβ : 0 < β) (hr₀ : 0 < r₀) (hmm' : m ≤ m') :
    greenPotentialHolderConstant β r₀ m ≤ greenPotentialHolderConstant β r₀ m' := by
  unfold greenPotentialHolderConstant
  exact mul_le_mul_of_nonneg_left (greenPotentialRieszBound_mono hβ hr₀ hmm')
    (mul_nonneg zero_le_two (inv_nonneg.2 (mul_nonneg Real.pi_pos.le
      (greenPotentialHolderExponent_pos hβ).le)))

/-- The constant of the cutoff error: `(2π α/2)⁻¹ (2R)^{α/2} K`, with `α = min(β,1)/2` and `K` the Riesz
potential bound. -/
noncomputable def greenCutoffConstant (R r₀ β m : ℝ) : ℝ :=
  (2 * Real.pi * (greenPotentialHolderExponent β / 2))⁻¹ * (2 * R) ^ (greenPotentialHolderExponent β / 2) *
    greenPotentialRieszBound β r₀ m

theorem greenCutoffConstant_nonneg {R r₀ β m : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β) (hm : 0 ≤ m) :
    0 ≤ greenCutoffConstant R r₀ β m := by
  unfold greenCutoffConstant
  exact mul_nonneg (mul_nonneg (inv_nonneg.2 (mul_nonneg (by positivity)
    (half_pos (greenPotentialHolderExponent_pos hβ)).le))
      (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * R by linarith) _))
    (greenPotentialRieszBound_nonneg hβ hr₀ hm)

theorem exists_pos_mul_rpow_lt {k p ε : ℝ} (hk : 0 ≤ k) (hp : 0 < p) (hε : 0 < ε) :
    ∃ s > 0, k * s ^ p < ε := by
  have hq : 0 < ε / (k + 1) := div_pos hε (by linarith)
  refine ⟨(ε / (k + 1)) ^ p⁻¹, Real.rpow_pos_of_pos hq _, ?_⟩
  rw [Real.rpow_inv_rpow hq.le hp.ne', mul_div_assoc', div_lt_iff₀ (by linarith)]
  nlinarith

/-! ### Uniform Hölder continuity and the Riesz bound -/

section Disc

variable {R r₀ β m : ℝ}

/-- **Uniform Hölder continuity of Green potentials.** Under the power growth `ν(B(z, r)) ≤ r^β` (`z ∈ B_R`,
`r < r₀`) and `ν(B_R) ≤ m`, the kernel `G_{B_R}(x, ·)` is `ν`-integrable and the Green potential is Hölder on the
closed disc, with constant `greenPotentialHolderConstant β r₀ m` and exponent `min(β,1)/2`. -/
theorem abs_greenPotential_ball_sub_le (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β) (hm : 0 ≤ m)
    {ν : Measure ℂ}
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, ν (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hmass : ν (ball 0 R) ≤ ENNReal.ofReal m) :
    (∀ x, Integrable (greenFunction (ball 0 R) x) ν) ∧
    ∀ x ∈ closedBall (0 : ℂ) R, ∀ x' ∈ closedBall (0 : ℂ) R,
      |greenPotential (ball 0 R) ν x - greenPotential (ball 0 R) ν x'| ≤
        greenPotentialHolderConstant β r₀ m * ‖x - x'‖ ^ greenPotentialHolderExponent β := by
  have hfin : ν (ball 0 R) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  obtain ⟨hint, hhol⟩ := greenPotential_ball_holder_of_upper hR hr₀ hβ hup hfin (f := fun _ => (1 : ℝ))
    aestronglyMeasurable_const zero_le_one (ae_of_all _ fun _ => by simp)
  have hset : ∀ x, ∫ y in ball 0 R, greenFunction (ball 0 R) x y ∂ν = greenPotential (ball 0 R) ν x :=
    fun x => setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => greenFunction_of_notMem_right hy x
  have hmR : (ν (ball 0 R)).toReal ≤ m := ENNReal.toReal_le_of_le_ofReal hm hmass
  refine ⟨fun x => ?_, fun x hx x' hx' => ?_⟩
  · by_cases hx : x ∈ ball (0 : ℂ) R
    · have h := hint x (ball_subset_closedBall hx)
      simp only [mul_one] at h
      refine (integrableOn_iff_integrable_of_support_subset fun y hy => ?_).1 h
      by_contra h'
      exact hy (greenFunction_of_notMem_right h' x)
    · rw [show greenFunction (ball 0 R) x = fun _ => 0 from funext (greenFunction_of_notMem_left hx)]
      exact integrable_zero _ _ _
  · have h := hhol x hx x' hx'
    simp only [mul_one, hset] at h
    exact h.trans (mul_le_mul_of_nonneg_right (greenPotentialHolderConstant_mono hβ hr₀ hmR)
      (Real.rpow_nonneg (norm_nonneg _) _))

/-- **Riesz potential bound.** Under the power growth and the mass bound,
`∫_{B_R} |x - y|^{-α} ν(dy) ≤ K` for `x` in the closed disc, `α = min(β,1)/2`,
`K = greenPotentialRieszBound β r₀ m`. -/
theorem lintegral_ball_rpow_neg_le (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β) (hm : 0 ≤ m)
    {ν : Measure ℂ}
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, ν (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hmass : ν (ball 0 R) ≤ ENNReal.ofReal m) {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) :
    ∫⁻ y in ball 0 R, ENNReal.ofReal (‖x - y‖ ^ (-greenPotentialHolderExponent β)) ∂ν ≤
      ENNReal.ofReal (greenPotentialRieszBound β r₀ m) := by
  have hfin : ν (ball 0 R) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hm₀ : 0 ≤ (ν (ball (0 : ℂ) R)).toReal := ENNReal.toReal_nonneg
  have hν : ν.restrict (ball 0 R) univ ≤ ENNReal.ofReal (ν (ball (0 : ℂ) R)).toReal := by
    rw [Measure.restrict_apply_univ, ENNReal.ofReal_toReal hfin]
  have h := lintegral_norm_sub_rpow_neg_le (greenPotentialHolderExponent_pos hβ)
    (greenPotentialHolderExponent_lt hβ) hm₀ (volumeGrowthAllScalesConstant_nonneg hr₀ hm₀) hν
    (fun r hr => restrict_ball_closedBall_le hR hr₀ hβ hup hfin hx hr)
  exact h.trans (ENNReal.ofReal_le_ofReal
    (greenPotentialRieszBound_mono hβ hr₀ (ENNReal.toReal_le_of_le_ofReal hm hmass)))

/-! ### The cutoff -/

/-- The cutoff `φ_s(y) = min(1, max(0, 2|y - x|/s - 1))`: `0` on `B(x, s/2)`, `1` off `B(x, s)`. -/
noncomputable def annulusCutoff (x : ℂ) (s : ℝ) (y : ℂ) : ℝ :=
  min 1 (max 0 (2 * ‖y - x‖ / s - 1))

theorem continuous_annulusCutoff (x : ℂ) (s : ℝ) : Continuous (annulusCutoff x s) := by
  unfold annulusCutoff
  exact continuous_const.min (continuous_const.max
    (((continuous_const.mul (continuous_sub_right x).norm).div_const s).sub continuous_const))

theorem annulusCutoff_nonneg (x : ℂ) (s : ℝ) (y : ℂ) : 0 ≤ annulusCutoff x s y :=
  le_min zero_le_one (le_max_left _ _)

theorem annulusCutoff_le_one (x : ℂ) (s : ℝ) (y : ℂ) : annulusCutoff x s y ≤ 1 :=
  min_le_left _ _

theorem annulusCutoff_eq_zero_of_lt {x y : ℂ} {s : ℝ} (hs : 0 < s) (h : ‖y - x‖ < s / 2) :
    annulusCutoff x s y = 0 := by
  have h1 : 2 * ‖y - x‖ / s - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hs]
    linarith
  rw [annulusCutoff, max_eq_left h1, min_eq_right zero_le_one]

theorem annulusCutoff_eq_one_of_le {x y : ℂ} {s : ℝ} (hs : 0 < s) (h : s ≤ ‖y - x‖) :
    annulusCutoff x s y = 1 := by
  have h1 : 1 ≤ 2 * ‖y - x‖ / s - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hs]
    linarith
  rw [annulusCutoff, max_eq_right (zero_le_one.trans h1), min_eq_left h1]

theorem continuous_greenFunction_mul_annulusCutoff {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) {s : ℝ} (hs : 0 < s) :
    Continuous fun y => greenFunction (ball 0 R) x y * annulusCutoff x s y := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hyx : y = x
  · rw [hyx]
    have h0 : (fun y => greenFunction (ball 0 R) x y * annulusCutoff x s y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [ball_mem_nhds x (half_pos hs)] with z hz
      rw [annulusCutoff_eq_zero_of_lt hs (by rw [← dist_eq_norm]; exact mem_ball.1 hz), mul_zero]
    exact continuousAt_const.congr h0.symm
  · exact ((continuousOn_greenFunction_ball hx).continuousAt (isOpen_compl_singleton.mem_nhds hyx)).mul
      (continuous_annulusCutoff x s).continuousAt

theorem tsupport_greenFunction_mul_subset (x : ℂ) (φ : ℂ → ℝ) :
    tsupport (fun y => greenFunction (ball 0 R) x y * φ y) ⊆ closedBall 0 R := by
  refine closure_minimal (fun y hy => ball_subset_closedBall ?_) isClosed_closedBall
  by_contra h
  exact hy (by simp only [greenFunction_of_notMem_right h x, zero_mul])

/-- **The cutoff error.** Under the power growth and the mass bound, for `x ∈ B_R` and `s > 0`, the cut-off kernel
`G(x, ·) φ_s` is integrable and `|G_{B_R} ν(x) - ∫ G(x, y) φ_s(y) ν(dy)| ≤ C s^{α/2}`. -/
theorem integrable_and_abs_greenPotential_ball_sub_cutoff_le (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hm : 0 ≤ m) {μ : Measure ℂ}
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hmass : μ (ball 0 R) ≤ ENNReal.ofReal m) {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) {s : ℝ} (hs : 0 < s) :
    Integrable (fun y => greenFunction (ball 0 R) x y * annulusCutoff x s y) μ ∧
    |greenPotential (ball 0 R) μ x - ∫ y, greenFunction (ball 0 R) x y * annulusCutoff x s y ∂μ| ≤
      greenCutoffConstant R r₀ β m * s ^ (greenPotentialHolderExponent β / 2) := by
  have hα := greenPotentialHolderExponent_pos hβ
  have ha : 0 < greenPotentialHolderExponent β / 2 := half_pos hα
  have hGi : Integrable (greenFunction (ball 0 R) x) μ :=
    (abs_greenPotential_ball_sub_le hR hr₀ hβ hm hup hmass).1 x
  have hG0 : ∀ y, 0 ≤ greenFunction (ball (0 : ℂ) R) x y := greenFunction_nonneg isBounded_ball x
  have hFi : Integrable (fun y => greenFunction (ball 0 R) x y * annulusCutoff x s y) μ := by
    refine hGi.mono ((measurable_greenFunction_ball R x).mul
      (continuous_annulusCutoff x s).measurable).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Real.norm_of_nonneg (annulusCutoff_nonneg x s y)]
    exact annulusCutoff_le_one x s y
  refine ⟨hFi, ?_⟩
  have hD0 : ∀ y, 0 ≤ greenFunction (ball 0 R) x y - greenFunction (ball 0 R) x y * annulusCutoff x s y :=
    fun y => by
      have := mul_le_of_le_one_right (hG0 y) (annulusCutoff_le_one x s y)
      linarith
  have hsub : greenPotential (ball 0 R) μ x - ∫ y, greenFunction (ball 0 R) x y * annulusCutoff x s y ∂μ =
      ∫ y, (greenFunction (ball 0 R) x y - greenFunction (ball 0 R) x y * annulusCutoff x s y) ∂μ :=
    (integral_sub hGi hFi).symm
  rw [hsub, abs_of_nonneg (integral_nonneg hD0)]
  have hc0 : 0 ≤ (2 * Real.pi * (greenPotentialHolderExponent β / 2))⁻¹ *
      (2 * R) ^ (greenPotentialHolderExponent β / 2) :=
    mul_nonneg (inv_nonneg.2 (mul_nonneg (by positivity) ha.le))
      (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * R by linarith) _)
  have hcs : 0 ≤ (2 * Real.pi * (greenPotentialHolderExponent β / 2))⁻¹ *
      (2 * R) ^ (greenPotentialHolderExponent β / 2) * s ^ (greenPotentialHolderExponent β / 2) :=
    mul_nonneg hc0 (Real.rpow_nonneg hs.le _)
  have hpt : ∀ y, ENNReal.ofReal (greenFunction (ball 0 R) x y -
      greenFunction (ball 0 R) x y * annulusCutoff x s y) ≤
      (ball (0 : ℂ) R).indicator (fun y => ENNReal.ofReal ((2 * Real.pi * (greenPotentialHolderExponent β / 2))⁻¹ *
        (2 * R) ^ (greenPotentialHolderExponent β / 2) * s ^ (greenPotentialHolderExponent β / 2) *
          ‖x - y‖ ^ (-greenPotentialHolderExponent β))) y := by
    intro y
    by_cases hy : y ∈ ball (0 : ℂ) R
    · rw [indicator_of_mem hy]
      refine ENNReal.ofReal_le_ofReal ?_
      rcases eq_or_ne y x with rfl | hyx
      · rw [greenFunction_self, zero_mul, sub_zero]
        exact mul_nonneg hcs (Real.rpow_nonneg (norm_nonneg _) _)
      by_cases hys : s ≤ ‖y - x‖
      · rw [annulusCutoff_eq_one_of_le hs hys, mul_one, sub_self]
        exact mul_nonneg hcs (Real.rpow_nonneg (norm_nonneg _) _)
      rw [not_le] at hys
      have hd : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hyx))
      have hds : ‖x - y‖ ≤ s := by
        rw [norm_sub_rev]
        exact hys.le
      have hGle := greenFunction_ball_le_rpow ha hx y
      have hsplit : ‖x - y‖ ^ (-(greenPotentialHolderExponent β / 2)) =
          ‖x - y‖ ^ (greenPotentialHolderExponent β / 2) * ‖x - y‖ ^ (-greenPotentialHolderExponent β) := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
      have hpow : ‖x - y‖ ^ (greenPotentialHolderExponent β / 2) ≤ s ^ (greenPotentialHolderExponent β / 2) :=
        Real.rpow_le_rpow hd.le hds ha.le
      have hφ := mul_nonneg (hG0 y) (annulusCutoff_nonneg x s y)
      rw [hsplit] at hGle
      have hmono := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hd.le (-greenPotentialHolderExponent β))) hc0
      linarith
    · rw [indicator_of_notMem hy, greenFunction_of_notMem_right hy x, zero_mul, sub_zero,
        ENNReal.ofReal_zero]
  have hmeas : Measurable fun y : ℂ => ‖x - y‖ ^ (-greenPotentialHolderExponent β) := by fun_prop
  have hle : ENNReal.ofReal (∫ y, (greenFunction (ball 0 R) x y -
      greenFunction (ball 0 R) x y * annulusCutoff x s y) ∂μ) ≤
      ENNReal.ofReal (greenCutoffConstant R r₀ β m * s ^ (greenPotentialHolderExponent β / 2)) := by
    have hDi : Integrable (fun y => greenFunction (ball 0 R) x y -
        greenFunction (ball 0 R) x y * annulusCutoff x s y) μ := hGi.sub hFi
    rw [ofReal_integral_eq_lintegral_ofReal hDi (ae_of_all _ hD0)]
    calc ∫⁻ y, ENNReal.ofReal (greenFunction (ball 0 R) x y -
          greenFunction (ball 0 R) x y * annulusCutoff x s y) ∂μ
        ≤ ∫⁻ y, (ball (0 : ℂ) R).indicator (fun y => ENNReal.ofReal
            ((2 * Real.pi * (greenPotentialHolderExponent β / 2))⁻¹ *
              (2 * R) ^ (greenPotentialHolderExponent β / 2) * s ^ (greenPotentialHolderExponent β / 2) *
                ‖x - y‖ ^ (-greenPotentialHolderExponent β))) y ∂μ := lintegral_mono hpt
      _ = ∫⁻ y in ball 0 R, ENNReal.ofReal ((2 * Real.pi * (greenPotentialHolderExponent β / 2))⁻¹ *
            (2 * R) ^ (greenPotentialHolderExponent β / 2) * s ^ (greenPotentialHolderExponent β / 2)) *
              ENNReal.ofReal (‖x - y‖ ^ (-greenPotentialHolderExponent β)) ∂μ := by
          rw [lintegral_indicator measurableSet_ball]
          exact lintegral_congr fun y => ENNReal.ofReal_mul hcs
      _ = ENNReal.ofReal ((2 * Real.pi * (greenPotentialHolderExponent β / 2))⁻¹ *
            (2 * R) ^ (greenPotentialHolderExponent β / 2) * s ^ (greenPotentialHolderExponent β / 2)) *
              ∫⁻ y in ball 0 R, ENNReal.ofReal (‖x - y‖ ^ (-greenPotentialHolderExponent β)) ∂μ :=
          lintegral_const_mul _ hmeas.ennreal_ofReal
      _ ≤ ENNReal.ofReal ((2 * Real.pi * (greenPotentialHolderExponent β / 2))⁻¹ *
            (2 * R) ^ (greenPotentialHolderExponent β / 2) * s ^ (greenPotentialHolderExponent β / 2)) *
              ENNReal.ofReal (greenPotentialRieszBound β r₀ m) :=
          mul_le_mul_of_nonneg_left
            (lintegral_ball_rpow_neg_le hR hr₀ hβ hm hup hmass (ball_subset_closedBall hx)) zero_le
      _ = ENNReal.ofReal (greenCutoffConstant R r₀ β m * s ^ (greenPotentialHolderExponent β / 2)) := by
          rw [← ENNReal.ofReal_mul hcs]
          congr 1
          unfold greenCutoffConstant
          ring
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (greenCutoffConstant_nonneg hR hr₀ hβ hm)
    (Real.rpow_nonneg hs.le _))).1 hle

/-! ### Convergence -/

variable {ν : ℕ → Measure ℂ} {ν₀ : Measure ℂ}

/-- **Pointwise convergence of Green potentials.** Under a common power growth and mass bound, if `ν_n → ν₀`
vaguely on the closed disc, then `G_{B_R} ν_n(x) → G_{B_R} ν₀(x)` for every `x` in the closed disc. -/
theorem tendsto_greenPotential_ball (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β) (hm : 0 ≤ m)
    (hup : ∀ n, ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, ν n (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hmass : ∀ n, ν n (ball 0 R) ≤ ENNReal.ofReal m)
    (hup₀ : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, ν₀ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hmass₀ : ν₀ (ball 0 R) ≤ ENNReal.ofReal m)
    (hvague : ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 R →
      Tendsto (fun n => ∫ y, F y ∂ν n) atTop (𝓝 (∫ y, F y ∂ν₀)))
    (x : ℂ) :
    Tendsto (fun n => greenPotential (ball 0 R) (ν n) x) atTop (𝓝 (greenPotential (ball 0 R) ν₀ x)) := by
  by_cases hxR : x ∈ ball (0 : ℂ) R
  swap
  · have h0 : ∀ μ : Measure ℂ, greenPotential (ball 0 R) μ x = 0 := fun μ => by
      simp [greenPotential, greenFunction_of_notMem_left hxR]
    simp only [h0]
    exact tendsto_const_nhds
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hα := greenPotentialHolderExponent_pos hβ
  obtain ⟨s, hs, hsε⟩ := exists_pos_mul_rpow_lt (greenCutoffConstant_nonneg hR hr₀ hβ hm) (half_pos hα)
    (show 0 < ε / 3 by linarith)
  have hnear₀ := (integrable_and_abs_greenPotential_ball_sub_cutoff_le hR hr₀ hβ hm hup₀ hmass₀ hxR hs).2
  have hnear := fun n =>
    (integrable_and_abs_greenPotential_ball_sub_cutoff_le hR hr₀ hβ hm (hup n) (hmass n) hxR hs).2
  have hF := hvague _ (continuous_greenFunction_mul_annulusCutoff hxR hs)
    (tsupport_greenFunction_mul_subset x (annulusCutoff x s))
  filter_upwards [Metric.tendsto_nhds.1 hF (ε / 3) (by linarith)] with n hn
  rw [Real.dist_eq] at hn ⊢
  obtain ⟨h1a, h1b⟩ := abs_le.1 (hnear n)
  obtain ⟨h2a, h2b⟩ := abs_lt.1 hn
  obtain ⟨h3a, h3b⟩ := abs_le.1 hnear₀
  rw [abs_lt]
  constructor <;> linarith

/-- **Uniform convergence of Green potentials on a disc.** Under a common power growth `ν(B(z, r)) ≤ r^β`
(`z ∈ B_R`, `r < r₀`) and a common mass bound `ν(B_R) ≤ m`, if `ν_n → ν₀` vaguely on the closed disc, then
`G_{B_R} ν_n → G_{B_R} ν₀` uniformly on the closed disc. -/
theorem eventually_forall_abs_greenPotential_ball_sub_lt (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hm : 0 ≤ m)
    (hup : ∀ n, ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, ν n (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hmass : ∀ n, ν n (ball 0 R) ≤ ENNReal.ofReal m)
    (hup₀ : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, ν₀ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hmass₀ : ν₀ (ball 0 R) ≤ ENNReal.ofReal m)
    (hvague : ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 R →
      Tendsto (fun n => ∫ y, F y ∂ν n) atTop (𝓝 (∫ y, F y ∂ν₀)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ closedBall (0 : ℂ) R,
      |greenPotential (ball 0 R) (ν n) x - greenPotential (ball 0 R) ν₀ x| < ε := by
  have hα := greenPotentialHolderExponent_pos hβ
  have hC := greenPotentialHolderConstant_nonneg hβ hr₀ hm
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_rpow_lt hC hα (show 0 < ε / 3 by linarith)
  have hHn := fun n => (abs_greenPotential_ball_sub_le hR hr₀ hβ hm (hup n) (hmass n)).2
  have hH₀ := (abs_greenPotential_ball_sub_le hR hr₀ hβ hm hup₀ hmass₀).2
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : ℂ) R).elim_finite_subcover
    (fun i : closedBall (0 : ℂ) R => ball (i : ℂ) δ) (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self hδ⟩)
  have hev : ∀ᶠ n in atTop, ∀ i ∈ t,
      |greenPotential (ball 0 R) (ν n) i - greenPotential (ball 0 R) ν₀ i| < ε / 3 := by
    refine (Filter.eventually_all_finset t).2 fun i _ => ?_
    have h := Metric.tendsto_nhds.1
      (tendsto_greenPotential_ball hR hr₀ hβ hm hup hmass hup₀ hmass₀ hvague i) (ε / 3) (by linarith)
    filter_upwards [h] with n hn
    rwa [Real.dist_eq] at hn
  filter_upwards [hev] with n hn x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
  have hxi' : ‖x - i‖ ^ greenPotentialHolderExponent β ≤ δ ^ greenPotentialHolderExponent β :=
    Real.rpow_le_rpow (norm_nonneg _) (by rw [← dist_eq_norm]; exact (mem_ball.1 hxi).le) hα.le
  have h4 := mul_le_mul_of_nonneg_left hxi' hC
  have h1 := hHn n x hx i i.2
  have h3 := hH₀ i i.2 x hx
  rw [norm_sub_rev] at h3
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_lt.1 (hn i hi)
  obtain ⟨h3a, h3b⟩ := abs_le.1 h3
  rw [abs_lt]
  constructor <;> linarith

end Disc

end MatedCRT
