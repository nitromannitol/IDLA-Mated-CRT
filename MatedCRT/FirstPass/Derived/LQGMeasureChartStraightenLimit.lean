import MatedCRT.FirstPass.Derived.LQGMeasureChartStraightenExponent
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward

/-!
# Straightening the transported bump: the fixed-scale limit

Let `ψ` be injective and holomorphic on `B(c, r)`, `φ = ψ⁻¹`, `f` a bump function of Sheffield–Wang, `0 < γ`, and
`g` a distribution on `B(c, r)` with local regularity `C^{-1/2}_loc` (`HasLocalRegularity g (-1/2)`). Suppose that the
smooth approximations of `g` with the variable radius `2^{-k} b(z)`, `b(z) = |φ'(ψ z)|`, converge vaguely in
`B(c, r)` to `μ` (the conclusion of the variable-radius step for this `b`; it is a hypothesis here). Then the smooth
approximations of the pulled-back field `g ∘ φ + Q log |φ'|` at the fixed scales `2^{-k}` converge vaguely in
`ψ(B(c, r))` to the image `ν(A) = μ(B(c, r) ∩ ψ⁻¹ A)` (`isVagueLimitOn_smoothApprox_pullbackPairing`).

Proof: by the comparison of the smoothed exponents (`smoothExponent_pullbackPairing_sub_le`), on the compact set
`φ(supp u)` the fixed-scale density of the pulled-back field at `w = ψ(z)`, times the Jacobian `|ψ'(z)|²` of the change
of variables `w = ψ(z)` (`withDensity_restrict_image_eq_map`), is the variable-radius density of `g` at `z` up to a
factor `e^{±C 2^{-k/2}}` (`γ Q = 2 + γ²/2` and `d(w)² |ψ'(z)|² = 1`). A two-sided comparison of measures bounds the
difference of the integrals of a test function by `(e^{C 2^{-k/2}} − 1)` times the integral of its absolute value
(`abs_integral_sub_le_of_le_smul`), which tends to `0`.

This completes the straightening step in the fixed-scale form of the coordinate change of Sheffield–Wang
(arXiv:1605.06171v2, Theorem 1.4; compare the change of variables in the proof of Duplantier–Sheffield,
arXiv:0808.1560v2, Proposition 2.1, p. 13).
-/

set_option autoImplicit false

noncomputable section

open scoped Classical ENNReal

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT

namespace LQGMeasureChart

namespace Straighten

variable {c : ℂ} {r : ℝ} {ψ : ℂ → ℂ} {f : ℂ → ℝ}

/-- The density of the fixed-scale smooth approximation of the pulled-back field
(`smoothApprox γ f (ψ '' ball c r) (pullbackPairing γ g ψ) ε = volume.withDensity (pullDensity …)`). -/
def pullDensity (γ : ℝ) (f : ℂ → ℝ) (c : ℂ) (r : ℝ) (ψ : ℂ → ℂ) (g : LQGMetric.DistOn (disc c r)) (ε : ℝ) :
    ℂ → ℝ≥0∞ := fun w =>
  if closedBall w ε ⊆ ψ '' ball c r then ENNReal.ofReal (Real.exp (smoothExponent γ f (pullbackPairing γ g ψ) ε w))
  else 0

/-- The density of the smooth approximation of `g` with the variable radius `ε |φ'(ψ z)|`. -/
def varDensity (γ : ℝ) (f : ℂ → ℝ) (c : ℂ) (r : ℝ) (ψ : ℂ → ℂ) (g : LQGMetric.DistOn (disc c r)) (ε : ℝ) :
    ℂ → ℝ≥0∞ := fun z =>
  if closedBall z (ε * ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖) ⊆ ball c r then
    ENNReal.ofReal (Real.exp (smoothExponent γ f (pairFun g) (ε * ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖) z))
  else 0

/-! ### Comparison of integrals against comparable measures -/

/-- If `ν₁ ≤ a ν₂` and `ν₂ ≤ a ν₁` with `a ≥ 1`, then `|∫ U dν₁ − ∫ U dν₂| ≤ (a − 1) ∫ |U| dν₂`. -/
theorem abs_integral_sub_le_of_le_smul {ν₁ ν₂ : Measure ℂ} {a : ℝ} (ha : 1 ≤ a)
    (h₁ : ν₁ ≤ ENNReal.ofReal a • ν₂) (h₂ : ν₂ ≤ ENNReal.ofReal a • ν₁) (U : ℂ → ℝ) :
    |∫ z, U z ∂ν₁ - ∫ z, U z ∂ν₂| ≤ (a - 1) * ∫ z, |U z| ∂ν₂ := by
  have ha0 : 0 < a := by linarith
  have hfin : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  by_cases hint : Integrable U ν₂
  · have hint₁ : Integrable U ν₁ := (hint.smul_measure hfin).mono_measure h₁
    have key : ∀ V : ℂ → ℝ, (∀ z, 0 ≤ V z) → Integrable V ν₂ → Integrable V ν₁ →
        |∫ z, V z ∂ν₁ - ∫ z, V z ∂ν₂| ≤ (a - 1) * ∫ z, V z ∂ν₂ := by
      intro V hV hV₂ hV₁
      have hup : ∫ z, V z ∂ν₁ ≤ a * ∫ z, V z ∂ν₂ := by
        have := integral_mono_measure h₁ (Eventually.of_forall hV) (hV₂.smul_measure hfin)
        rwa [integral_smul_measure, ENNReal.toReal_ofReal ha0.le, smul_eq_mul] at this
      have hlow : ∫ z, V z ∂ν₂ ≤ a * ∫ z, V z ∂ν₁ := by
        have := integral_mono_measure h₂ (Eventually.of_forall hV) (hV₁.smul_measure hfin)
        rwa [integral_smul_measure, ENNReal.toReal_ofReal ha0.le, smul_eq_mul] at this
      have h0 : 0 ≤ ∫ z, V z ∂ν₂ := integral_nonneg hV
      have h3 : a * ((2 - a) * ∫ z, V z ∂ν₂) ≤ a * ∫ z, V z ∂ν₁ := by
        nlinarith [mul_nonneg h0 (sq_nonneg (a - 1))]
      have h4 := le_of_mul_le_mul_left h3 ha0
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have hsplit : ∀ ν : Measure ℂ, Integrable U ν →
        ∫ z, U z ∂ν = ∫ z, max (U z) 0 ∂ν - ∫ z, max (-U z) 0 ∂ν := by
      intro ν hν
      rw [← integral_sub hν.pos_part hν.neg_part]
      congr 1
      funext z
      exact (max_zero_sub_max_neg_zero_eq_self (U z)).symm
    have habs : ∫ z, |U z| ∂ν₂ = ∫ z, max (U z) 0 ∂ν₂ + ∫ z, max (-U z) 0 ∂ν₂ := by
      rw [← integral_add hint.pos_part hint.neg_part]
      congr 1
      funext z
      exact (max_zero_add_max_neg_zero_eq_abs_self (U z)).symm
    rw [hsplit ν₁ hint₁, hsplit ν₂ hint, habs]
    have k1 := key (fun z => max (U z) 0) (fun z => le_max_right _ _) hint.pos_part hint₁.pos_part
    have k2 := key (fun z => max (-U z) 0) (fun z => le_max_right _ _) hint.neg_part hint₁.neg_part
    calc |∫ z, max (U z) 0 ∂ν₁ - ∫ z, max (-U z) 0 ∂ν₁ - (∫ z, max (U z) 0 ∂ν₂ - ∫ z, max (-U z) 0 ∂ν₂)|
        = |(∫ z, max (U z) 0 ∂ν₁ - ∫ z, max (U z) 0 ∂ν₂) -
            (∫ z, max (-U z) 0 ∂ν₁ - ∫ z, max (-U z) 0 ∂ν₂)| := by
          congr 1; ring
      _ ≤ |∫ z, max (U z) 0 ∂ν₁ - ∫ z, max (U z) 0 ∂ν₂| +
            |∫ z, max (-U z) 0 ∂ν₁ - ∫ z, max (-U z) 0 ∂ν₂| := abs_sub _ _
      _ ≤ (a - 1) * ∫ z, max (U z) 0 ∂ν₂ + (a - 1) * ∫ z, max (-U z) 0 ∂ν₂ := add_le_add k1 k2
      _ = (a - 1) * (∫ z, max (U z) 0 ∂ν₂ + ∫ z, max (-U z) 0 ∂ν₂) := by ring
  · have hn₁ : ¬ Integrable U ν₁ := fun h => hint ((h.smul_measure hfin).mono_measure h₂)
    rw [integral_undef hint, integral_undef hn₁, sub_zero, abs_zero]
    exact mul_nonneg (by linarith) (integral_nonneg fun z => abs_nonneg _)

/-- Pointwise comparison of densities on a measurable set gives the comparison of the restricted measures. -/
theorem withDensity_restrict_le_smul {μ₀ : Measure ℂ} {F G : ℂ → ℝ≥0∞} {K : Set ℂ} (hK : MeasurableSet K)
    {a : ℝ≥0∞} (ha : a ≠ ⊤) (h : ∀ z ∈ K, F z ≤ a * G z) :
    (μ₀.withDensity F).restrict K ≤ a • (μ₀.withDensity G).restrict K := by
  rw [restrict_withDensity hK, restrict_withDensity hK, ← withDensity_smul' a G ha]
  exact withDensity_mono (ae_restrict_of_forall_mem hK h)

/-! ### Change of variables -/

theorem piecewise_preimage_inter (A : Set ℂ) :
    ((ball c r).piecewise ψ fun _ => (0 : ℂ)) ⁻¹' A ∩ ball c r = ball c r ∩ ψ ⁻¹' A := by
  ext z
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨h1, h2⟩
    rw [piecewise_eq_of_mem _ _ _ h2] at h1
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    refine ⟨?_, h2⟩
    rw [piecewise_eq_of_mem _ _ _ h2]
    exact h1

theorem measurable_piecewise_ball (hψ : DifferentiableOn ℂ ψ (ball c r)) :
    Measurable ((ball c r).piecewise ψ fun _ => (0 : ℂ)) :=
  hψ.continuousOn.measurable_piecewise continuousOn_const measurableSet_ball

/-- **Change of variables `w = ψ(z)`** for a density `F` on `ψ(B(c, r))`, with Jacobian `|ψ'(z)|²`. -/
theorem withDensity_restrict_image_eq_map (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r))
    (F : ℂ → ℝ≥0∞) :
    (volume.restrict (ψ '' ball c r)).withDensity F =
      Measure.map ((ball c r).piecewise ψ fun _ => (0 : ℂ))
        ((volume.restrict (ball c r)).withDensity fun z => ENNReal.ofReal (‖deriv ψ z‖ ^ 2) * F (ψ z)) := by
  have hψm := measurable_piecewise_ball hψ
  ext A hA
  have hpre : MeasurableSet (((ball c r).piecewise ψ fun _ => (0 : ℂ)) ⁻¹' A) := hψm hA
  rw [withDensity_apply _ hA, Measure.map_apply hψm hA, withDensity_apply _ hpre,
    Measure.restrict_restrict hA, Measure.restrict_restrict hpre, piecewise_preimage_inter]
  have himg : A ∩ ψ '' ball c r = ψ '' (ball c r ∩ ψ ⁻¹' A) := by
    rw [Set.image_inter_preimage, Set.inter_comm]
  have hs : MeasurableSet (ball c r ∩ ψ ⁻¹' A) := by
    rw [← piecewise_preimage_inter]
    exact hpre.inter measurableSet_ball
  rw [himg]
  exact QuantumZipper.lintegral_comp_holo isOpen_ball hψ hinj (fun z hz => deriv_ne_zero hψ hinj hz) hs
    Set.inter_subset_left F

/-- The integral of a test function supported in `ψ(B(c, r))` against the fixed-scale smooth approximation of the
pulled-back field, as an integral on `B(c, r)`. -/
theorem integral_smoothApprox_eq (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r)) (γ : ℝ)
    (g : LQGMetric.DistOn (disc c r)) (ε : ℝ) {u : ℂ → ℝ} (hu : Continuous u)
    (husW : tsupport u ⊆ ψ '' ball c r) :
    ∫ w, u w ∂(smoothApprox γ f (ψ '' ball c r) (pullbackPairing γ g ψ) ε) =
      ∫ z, (ball c r).indicator (fun z => u (ψ z)) z ∂((volume.restrict (ball c r)).withDensity
        fun z => ENNReal.ofReal (‖deriv ψ z‖ ^ 2) * pullDensity γ f c r ψ g ε (ψ z)) := by
  have hW := isOpen_image hψ hinj
  have hψm := measurable_piecewise_ball hψ
  have h1 : smoothApprox γ f (ψ '' ball c r) (pullbackPairing γ g ψ) ε =
      volume.withDensity (pullDensity γ f c r ψ g ε) := rfl
  rw [h1, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ψ '' ball c r)
      (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (husW h)),
    restrict_withDensity hW.measurableSet, withDensity_restrict_image_eq_map hψ hinj,
    integral_map hψm.aemeasurable hu.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)] with z hz
  simp only [piecewise_eq_of_mem _ _ _ hz, indicator_of_mem hz]

/-! ### Comparison of the densities -/

theorem ofReal_exp_comparison {X Y d s : ℝ} (hd : 0 < d) (h : |Y - (X + 2 * Real.log d)| ≤ s) :
    ENNReal.ofReal (d⁻¹ ^ 2) * ENNReal.ofReal (Real.exp Y) ≤
        ENNReal.ofReal (Real.exp s) * ENNReal.ofReal (Real.exp X) ∧
      ENNReal.ofReal (Real.exp X) ≤
        ENNReal.ofReal (Real.exp s) * (ENNReal.ofReal (d⁻¹ ^ 2) * ENNReal.ofReal (Real.exp Y)) := by
  have h2 : Real.exp (2 * Real.log d) = d ^ 2 := by
    rw [show 2 * Real.log d = Real.log (d ^ 2) by rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  have key : d⁻¹ ^ 2 * Real.exp Y = Real.exp (Y - (X + 2 * Real.log d)) * Real.exp X := by
    rw [← Real.exp_add, show Y - (X + 2 * Real.log d) + X = Y - 2 * Real.log d by ring, Real.exp_sub, h2,
      inv_pow, div_eq_inv_mul]
  have he1 : Real.exp (Y - (X + 2 * Real.log d)) ≤ Real.exp s := Real.exp_le_exp.2 ((le_abs_self _).trans h)
  have he2 : Real.exp (-(Y - (X + 2 * Real.log d))) ≤ Real.exp s := Real.exp_le_exp.2 ((neg_le_abs _).trans h)
  have hX : Real.exp X = Real.exp (-(Y - (X + 2 * Real.log d))) * (d⁻¹ ^ 2 * Real.exp Y) := by
    rw [key, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (Real.exp_pos s).le, key]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right he1 (Real.exp_pos X).le)
  · rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (Real.exp_pos s).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hX]
    exact mul_le_mul_of_nonneg_right he2 (mul_nonneg (sq_nonneg _) (Real.exp_pos Y).le)

/-! ### The fixed-scale limit -/

/-- **Convergence of the integrals of a test function** against the fixed-scale smooth approximations of the
pulled-back field, from the variable-radius convergence for `g`. -/
theorem tendsto_integral_smoothApprox_pullback (hψ : DifferentiableOn ℂ ψ (ball c r))
    (hinj : InjOn ψ (ball c r)) {γ : ℝ} (hγ : 0 < γ) (hf : IsMollifier f) {g : LQGMetric.DistOn (disc c r)}
    (hg : HasLocalRegularity g (-(1 / 2))) {μ : Measure ℂ}
    (hvar : QuantumZipper.IsVagueLimitOn (ball c r)
      (fun k => volume.withDensity (varDensity γ f c r ψ g (HarmonicBalls.dyadicScale k))) μ)
    {u : ℂ → ℝ} (hu : Continuous u) (hus : HasCompactSupport u) (husW : tsupport u ⊆ ψ '' ball c r) :
    Tendsto (fun k => ∫ w, u w ∂(smoothApprox γ f (ψ '' ball c r) (pullbackPairing γ g ψ)
        (HarmonicBalls.dyadicScale k))) atTop
      (𝓝 (∫ z, (ball c r).indicator (fun z => u (ψ z)) z ∂μ)) := by
  have hW := isOpen_image hψ hinj
  have hK' : IsCompact (tsupport u) := hus
  have hφd := differentiableOn_invFunOn hψ hinj
  set Kx := Function.invFunOn ψ (ball c r) '' tsupport u with hKx_def
  have hKx : IsCompact Kx := hK'.image_of_continuousOn (hφd.continuousOn.mono husW)
  have hKxS : Kx ⊆ ball c r := by
    rintro _ ⟨w, hw, rfl⟩
    exact invFunOn_mem (husW hw)
  set U : ℂ → ℝ := (ball c r).indicator fun z => u (ψ z) with hU_def
  have hU0 : ∀ z, z ∉ Kx → U z = 0 := by
    intro z hz
    by_cases hzS : z ∈ ball c r
    · rw [hU_def, indicator_of_mem hzS]
      by_contra h
      exact hz ⟨ψ z, subset_tsupport u (Function.mem_support.2 h), invFunOn_apply hinj hzS⟩
    · exact indicator_of_notMem hzS _
  have hUS : ∀ z, z ∉ ball c r → U z = 0 := fun z hz => hU0 z fun h => hz (hKxS h)
  have hUc : Continuous U := continuous_of_continuousOn_of_eq_zero isOpen_ball hKx.isClosed hKxS
    ((hu.comp_continuousOn hψ.continuousOn).congr fun z hz => indicator_of_mem hz _) hU0
  have hUcs : HasCompactSupport U := HasCompactSupport.intro hKx hU0
  have hUts : tsupport U ⊆ ball c r :=
    (closure_minimal (fun z hz => Classical.byContradiction fun h => Function.mem_support.1 hz (hU0 z h))
      hKx.isClosed).trans hKxS
  have hAc : Continuous fun z => |U z| := hUc.abs
  have hAcs : HasCompactSupport fun z => |U z| :=
    HasCompactSupport.intro hKx fun z hz => by simp only [hU0 z hz, abs_zero]
  have hAts : tsupport (fun z => |U z|) ⊆ ball c r :=
    (closure_minimal (fun z hz => Classical.byContradiction fun h =>
      Function.mem_support.1 hz (by simp only [hU0 z h, abs_zero])) hKx.isClosed).trans hKxS
  have hlim := hvar.2.2 U hUc hUcs hUts
  have hlimA := hvar.2.2 _ hAc hAcs hAts
  -- the constants
  obtain ⟨C, ε₀, hε₀, HE⟩ := smoothExponent_pullbackPairing_sub_le hψ hinj hγ hf hg hK' husW
  obtain ⟨δ', hδ', hδ'W⟩ := hK'.exists_cthickening_subset_open hW husW
  obtain ⟨δ, hδ, hδS⟩ := hKx.exists_cthickening_subset_open isOpen_ball hKxS
  have hφ'c : ContinuousOn (deriv (Function.invFunOn ψ (ball c r))) (ψ '' ball c r) :=
    (hφd.deriv hW).continuousOn
  obtain ⟨Bd, hBd⟩ := hK'.exists_bound_of_continuousOn (hφ'c.mono husW)
  have hBd1 : 0 < max Bd 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hε₁ : 0 < min ε₀ (min δ' (δ / max Bd 1)) := lt_min hε₀ (lt_min hδ' (by positivity))
  have hdy : Tendsto HarmonicBalls.dyadicScale atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact this
  -- the comparison at small scales
  have hbound : ∀ᶠ k in atTop,
      |∫ w, u w ∂(smoothApprox γ f (ψ '' ball c r) (pullbackPairing γ g ψ) (HarmonicBalls.dyadicScale k)) -
        ∫ z, U z ∂(volume.withDensity (varDensity γ f c r ψ g (HarmonicBalls.dyadicScale k)))| ≤
      (Real.exp (max C 0 * Real.sqrt (HarmonicBalls.dyadicScale k)) - 1) *
        ∫ z, |U z| ∂(volume.withDensity (varDensity γ f c r ψ g (HarmonicBalls.dyadicScale k))) := by
    filter_upwards [hdy.eventually (Iic_mem_nhds hε₁)] with k hk
    set ε := HarmonicBalls.dyadicScale k with hε_def
    have hεpos : 0 < ε := HarmonicBalls.dyadicScale_pos k
    have hεε₀ : ε ≤ ε₀ := (show ε ≤ _ from hk).trans (min_le_left _ _)
    have hεδ' : ε ≤ δ' := (show ε ≤ _ from hk).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hεδ : ε ≤ δ / max Bd 1 := (show ε ≤ _ from hk).trans ((min_le_right _ _).trans (min_le_right _ _))
    set s := max C 0 * Real.sqrt ε with hs_def
    have hs0 : 0 ≤ s := mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
    have ha1 : 1 ≤ Real.exp s := Real.one_le_exp hs0
    set G : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖deriv ψ z‖ ^ 2) * pullDensity γ f c r ψ g ε (ψ z) with hG_def
    -- pointwise comparison of the densities on `Kx`
    have hpt : ∀ z ∈ Kx, G z ≤ ENNReal.ofReal (Real.exp s) * varDensity γ f c r ψ g ε z ∧
        varDensity γ f c r ψ g ε z ≤ ENNReal.ofReal (Real.exp s) * G z := by
      intro z hz
      have hzS := hKxS hz
      have hzK := hz
      obtain ⟨w, hw, hwz⟩ := hz
      have hψz : ψ z = w := by rw [← hwz]; exact apply_invFunOn (husW hw)
      have hψzK : ψ z ∈ tsupport u := hψz ▸ hw
      have hzW : ψ z ∈ ψ '' ball c r := mem_image_of_mem ψ hzS
      have hb : ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖ = ‖deriv ψ z‖⁻¹ := by
        rw [norm_deriv_invFunOn hψ hinj hzW, invFunOn_apply hinj hzS]
      have hnpos : 0 < ‖deriv ψ z‖ := norm_pos_iff.2 (deriv_ne_zero hψ hinj hzS)
      have hbpos : 0 < ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖ := by rw [hb]; positivity
      have hq : ‖deriv ψ z‖ = ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖⁻¹ := by rw [hb, inv_inv]
      have hc1 : closedBall (ψ z) ε ⊆ ψ '' ball c r :=
        ((closedBall_subset_closedBall hεδ').trans (closedBall_subset_cthickening hψzK δ')).trans hδ'W
      have hc2 : closedBall z (ε * ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖) ⊆ ball c r := by
        refine ((closedBall_subset_closedBall ?_).trans
          (closedBall_subset_cthickening hzK δ)).trans hδS
        have h3 : ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖ ≤ max Bd 1 :=
          (hBd _ hψzK).trans (le_max_left _ _)
        calc ε * ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖ ≤ δ / max Bd 1 * max Bd 1 :=
              mul_le_mul hεδ h3 (norm_nonneg _) (by positivity)
          _ = δ := div_mul_cancel₀ _ hBd1.ne'
      have hE := HE (ψ z) hψzK ε ⟨hεpos, hεε₀⟩
      rw [invFunOn_apply hinj hzS] at hE
      have hE' := hE.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg ε))
      have hcmp := ofReal_exp_comparison hbpos hE'
      simp only [hG_def, pullDensity, varDensity, ite_eq_left hc1, ite_eq_left hc2, hq]
      exact hcmp
    have hKxm : MeasurableSet Kx := hKx.isClosed.measurableSet
    have hm1 := withDensity_restrict_le_smul (μ₀ := volume.restrict (ball c r)) hKxm ENNReal.ofReal_ne_top
      fun z hz => (hpt z hz).1
    have hm2 := withDensity_restrict_le_smul (μ₀ := volume.restrict (ball c r)) hKxm ENNReal.ofReal_ne_top
      fun z hz => (hpt z hz).2
    have hmain := abs_integral_sub_le_of_le_smul ha1 hm1 hm2 U
    have hlam : ∫ z, U z ∂(((volume.restrict (ball c r)).withDensity G).restrict Kx) =
        ∫ w, u w ∂(smoothApprox γ f (ψ '' ball c r) (pullbackPairing γ g ψ) ε) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hU0,
        integral_smoothApprox_eq hψ hinj γ g ε hu husW]
    have hρ : ∀ F : ℂ → ℝ, (∀ z, z ∉ Kx → F z = 0) →
        ∫ z, F z ∂(((volume.restrict (ball c r)).withDensity (varDensity γ f c r ψ g ε)).restrict Kx) =
          ∫ z, F z ∂(volume.withDensity (varDensity γ f c r ψ g ε)) := by
      intro F hF
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hF, ← restrict_withDensity measurableSet_ball,
        setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hF z fun h => hz (hKxS h)]
    rw [hlam, hρ U hU0, hρ (fun z => |U z|) fun z hz => by simp only [hU0 z hz, abs_zero]] at hmain
    exact hmain
  -- conclusion
  have hc : Tendsto (fun k => (Real.exp (max C 0 * Real.sqrt (HarmonicBalls.dyadicScale k)) - 1) *
      ∫ z, |U z| ∂(volume.withDensity (varDensity γ f c r ψ g (HarmonicBalls.dyadicScale k)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => Real.exp (max C 0 * Real.sqrt (HarmonicBalls.dyadicScale k)) - 1) atTop (𝓝 0) := by
      have h2 : Tendsto (fun k => Real.exp (max C 0 * Real.sqrt (HarmonicBalls.dyadicScale k))) atTop
          (𝓝 (Real.exp (max C 0 * Real.sqrt 0))) :=
        ((Real.continuous_exp.comp (continuous_const.mul Real.continuous_sqrt)).tendsto 0).comp hdy
      have h3 := h2.sub_const 1
      simpa using h3
    simpa using h1.mul hlimA
  have hdiff := squeeze_zero_norm' (hbound.mono fun k hk => by rwa [Real.norm_eq_abs]) hc
  have hsum := hdiff.add hlim
  simpa using hsum

end Straighten

end LQGMeasureChart

section

variable {c : ℂ} {r : ℝ} {ψ : ℂ → ℂ} {f : ℂ → ℝ}

open LQGMeasureChart LQGMeasureChart.Straighten

/-- **The fixed-scale coordinate change on a disc, from the variable-radius convergence.** Let `ψ` be injective and
holomorphic on `B(c, r)`, `φ = ψ⁻¹`, `0 < γ`, `f` a bump function, and `g` a distribution on `B(c, r)` with local
regularity `C^{-1/2}_loc`. If the smooth approximations of `g` with the variable radius `2^{-k} |φ'(ψ z)|` converge
vaguely in `B(c, r)` to `μ`, then the smooth approximations of `g ∘ φ + Q log |φ'|` at the fixed scales `2^{-k}`
converge vaguely in `ψ(B(c, r))` to the measure `ν` with `ν(A) = μ(B(c, r) ∩ ψ⁻¹ A)` (Sheffield–Wang (2016),
Theorem 1.4, at fixed scale). -/
theorem isVagueLimitOn_smoothApprox_pullbackPairing (hψ : DifferentiableOn ℂ ψ (ball c r))
    (hinj : InjOn ψ (ball c r)) {γ : ℝ} (hγ : 0 < γ) (hf : IsMollifier f) {g : LQGMetric.DistOn (disc c r)}
    (hg : HasLocalRegularity g (-(1 / 2))) {μ : Measure ℂ}
    (hvar : QuantumZipper.IsVagueLimitOn (ball c r) (fun k => volume.withDensity fun z =>
      if closedBall z (HarmonicBalls.dyadicScale k * ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖) ⊆
          ball c r then
        ENNReal.ofReal (Real.exp (smoothExponent γ f (pairFun g)
          (HarmonicBalls.dyadicScale k * ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖) z))
      else 0) μ) :
    ∃ ν : Measure ℂ,
      QuantumZipper.IsVagueLimitOn (ψ '' ball c r)
        (fun k => smoothApprox γ f (ψ '' ball c r) (pullbackPairing γ g ψ) (HarmonicBalls.dyadicScale k)) ν ∧
      ∀ A : Set ℂ, MeasurableSet A → A ⊆ ψ '' ball c r → ν A = μ (ball c r ∩ ψ ⁻¹' A) := by
  have hW := isOpen_image hψ hinj
  have hψm := measurable_piecewise_ball hψ
  refine ⟨Measure.map ((ball c r).piecewise ψ fun _ => (0 : ℂ)) (μ.restrict (ball c r)), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Measure.map_apply hψm hW.measurableSet.compl, Measure.restrict_apply (hψm hW.measurableSet.compl),
      piecewise_preimage_inter]
    have h0 : ball c r ∩ ψ ⁻¹' (ψ '' ball c r)ᶜ = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
        not_not]
      exact fun hz => mem_image_of_mem ψ hz
    rw [h0, measure_empty]
  · intro K hK hKW
    rw [Measure.map_apply hψm hK.measurableSet, Measure.restrict_apply (hψm hK.measurableSet),
      piecewise_preimage_inter]
    have hKx : IsCompact (Function.invFunOn ψ (ball c r) '' K) :=
      hK.image_of_continuousOn ((differentiableOn_invFunOn hψ hinj).continuousOn.mono hKW)
    have hKxS : Function.invFunOn ψ (ball c r) '' K ⊆ ball c r := by
      rintro _ ⟨w, hw, rfl⟩
      exact invFunOn_mem (hKW hw)
    refine lt_of_le_of_lt (measure_mono ?_) (hvar.2.1 _ hKx hKxS)
    rintro z ⟨hz, hzK⟩
    exact ⟨ψ z, hzK, invFunOn_apply hinj hz⟩
  · intro u hu hus husW
    have h1 : ∫ z, u z ∂(Measure.map ((ball c r).piecewise ψ fun _ => (0 : ℂ)) (μ.restrict (ball c r))) =
        ∫ z, (ball c r).indicator (fun z => u (ψ z)) z ∂μ := by
      rw [integral_map hψm.aemeasurable hu.aestronglyMeasurable,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball c r)
          (fun z hz => indicator_of_notMem hz _)]
      refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
      simp only [piecewise_eq_of_mem _ _ _ hz, indicator_of_mem hz]
    rw [h1]
    exact tendsto_integral_smoothApprox_pullback hψ hinj hγ hf hg hvar hu hus husW
  · intro A hA _
    rw [Measure.map_apply hψm hA, Measure.restrict_apply (hψm hA), piecewise_preimage_inter]

end

end MatedCRT
