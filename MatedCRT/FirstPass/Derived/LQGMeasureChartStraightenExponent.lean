import MatedCRT.FirstPass.Derived.LQGMeasureChartStraighten

/-!
# Straightening the transported bump: comparison of the smoothed fields

Let `ψ` be injective and holomorphic on `B(c, r)`, `φ = ψ⁻¹`, `f` a bump function of Sheffield–Wang, and `g` a
distribution on `B(c, r)` with the local regularity `C^{-1/2}_loc` in test-function form (`HasLocalRegularity g (-1/2)`:
on each compact set, `|⟨g, t⁻² η((· − x)/t)⟩| ≤ C t^{-1/2}` for small `t` and `η` smooth, supported in the unit disc,
with `|η|, ‖Dη‖ ≤ 1`; this is the conclusion of `ZeroBoundaryGFFLocalRegularity` for one field with `α = −1/2`).

For `w` in a compact subset of `ψ(B(c, r))`, `x = φ(w)`, `d = |φ'(w)|` (`pullbackPairing_mollScale_sub_le`):
`(g ∘ φ + Q log |φ'|) ∗ f_ε(w) = (g ∗ f_{ε d})(x) + Q log d + O(ε^{1/2})`, uniformly in `w`.
The first term comes from the profile estimate (`exists_profileErr_bounds`): the transported test is
`f_{ε d}(x − ·) + t⁻² P((· − x)/t)` with `|P|, ‖DP‖ = O(ε)` on a fixed disc, so the regularity bound at scale
`t ≍ ε` gives the error `O(ε · ε^{-1/2})`. The second term is the average of the continuously differentiable function
`log |φ'|` against `f_ε(w − ·)`, which differs from its value at `w` by `O(ε)` (Sheffield–Wang use the exact mean
value property of the harmonic function `log |φ'|`; the Lipschitz bound suffices here). Since `γ Q = 2 + γ²/2`, the
smoothed exponents satisfy (`smoothExponent_pullbackPairing_sub_le`)
`h̃_ε(w) = h̃_{ε d}(x) + 2 log d + O(ε^{1/2})` for the field `g ∘ φ + Q log |φ'|` on the left and `g` on the right.

This is the second half of the straightening step in the fixed-scale form of the coordinate change of
Sheffield–Wang (arXiv:1605.06171v2, Theorem 1.4); the local regularity is De Nitti–Schweiger (arXiv:2301.13781v4),
Proposition 2.1 (see `ZeroBoundaryGFFLocalRegularity`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT

namespace LQGMeasureChart

/-- **Local negative regularity `C^α_loc` of a distribution on `B(c, r)`, in test-function form** (the statement of
`ZeroBoundaryGFFLocalRegularity` for one field and one exponent `α`): on every compact `K ⊆ B(c, r)` and at small
scales `t`, the pairings with `t⁻² η((· − x)/t)`, `x ∈ K`, `η` smooth with support in the unit disc and
`|η|, ‖Dη‖ ≤ 1`, are at most `C t^α`. -/
def HasLocalRegularity {c : ℂ} {r : ℝ} (g : LQGMetric.DistOn (disc c r)) (α : ℝ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ ball c r →
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ x ∈ K, ∀ t ∈ Ioc 0 t₀, ∀ η : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η →
      tsupport η ⊆ ball 0 1 → (∀ z, |η z| ≤ 1) → (∀ z, ‖fderiv ℝ η z‖ ≤ 1) →
      |pairFun g (fun y => (t ^ 2)⁻¹ * η ((y - x) / (t : ℂ)))| ≤ C * t ^ α

namespace Straighten

variable {c : ℂ} {r : ℝ} {ψ : ℂ → ℂ} {f : ℂ → ℝ}

/-! ### Linearity of the pairing on admissible tests -/

theorem pairFun_add {V : TopologicalSpace.Opens ℂ} (g : LQGMetric.DistOn V) {u₁ u₂ : ℂ → ℝ}
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) u₁ ∧ HasCompactSupport u₁ ∧ tsupport u₁ ⊆ V)
    (h₂ : ContDiff ℝ (⊤ : ℕ∞) u₂ ∧ HasCompactSupport u₂ ∧ tsupport u₂ ⊆ V) :
    pairFun g (u₁ + u₂) = pairFun g u₁ + pairFun g u₂ := by
  have h₃ : ContDiff ℝ (⊤ : ℕ∞) (u₁ + u₂) ∧ HasCompactSupport (u₁ + u₂) ∧ tsupport (u₁ + u₂) ⊆ V :=
    ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, (tsupport_add u₁ u₂).trans (union_subset h₁.2.2 h₂.2.2)⟩
  unfold pairFun
  rw [dite_eq_left h₃, dite_eq_left h₁, dite_eq_left h₂, ← map_add]
  rfl

theorem pairFun_const_mul {V : TopologicalSpace.Opens ℂ} (g : LQGMetric.DistOn V) (a : ℝ) {u : ℂ → ℝ}
    (h : ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ V) :
    pairFun g (fun y => a * u y) = a * pairFun g u := by
  have h' : ContDiff ℝ (⊤ : ℕ∞) (fun y => a * u y) ∧ HasCompactSupport (fun y => a * u y) ∧
      tsupport (fun y => a * u y) ⊆ V :=
    ⟨contDiff_const.mul h.1, h.2.1.mul_left, tsupport_mul_subset_right.trans h.2.2⟩
  unfold pairFun
  rw [dite_eq_left h', dite_eq_left h, ← smul_eq_mul, ← map_smul]
  rfl

/-- A rescaled smooth profile `y ↦ a η((y − x)/s)` with `η` vanishing outside `B(0, ρ)` and `B̄(x, ρ s) ⊆ V` is an
admissible test on `V`. -/
theorem scaled_admissible {V : TopologicalSpace.Opens ℂ} {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) {ρ : ℝ}
    (hηρ : ∀ z, η z ≠ 0 → ‖z‖ < ρ) {x : ℂ} {s : ℝ} (hs : 0 < s) (hV : closedBall x (ρ * s) ⊆ V) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => a * η ((y - x) / (s : ℂ))) ∧
      HasCompactSupport (fun y => a * η ((y - x) / (s : ℂ))) ∧
      tsupport (fun y => a * η ((y - x) / (s : ℂ))) ⊆ V := by
  have hsupp : ∀ y, a * η ((y - x) / (s : ℂ)) ≠ 0 → y ∈ closedBall x (ρ * s) := by
    intro y hy
    have h1 := hηρ _ (right_ne_zero_of_mul hy)
    rw [norm_div, Complex.norm_of_nonneg hs.le, div_lt_iff₀ hs] at h1
    rw [mem_closedBall, dist_eq_norm]
    exact h1.le
  have hts : tsupport (fun y => a * η ((y - x) / (s : ℂ))) ⊆ closedBall x (ρ * s) :=
    closure_minimal (fun y hy => hsupp y hy) isClosed_closedBall
  refine ⟨contDiff_const.mul (hη.comp ((contDiff_id.sub contDiff_const).div_const _)), ?_, hts.trans hV⟩
  exact HasCompactSupport.intro (isCompact_closedBall x (ρ * s)) fun y hy => by
    by_contra h
    exact hy (hsupp y h)

/-! ### Averages of `log |φ'|` -/

theorem continuous_of_continuousOn_of_eq_zero {F : ℂ → ℝ} {U K : Set ℂ} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) (hF : ContinuousOn F U) (h0 : ∀ z, z ∉ K → F z = 0) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ U
  · exact hF.continuousAt (hU.mem_nhds hz)
  · have hzK : z ∉ K := fun h => hz (hKU h)
    have h1 : F =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds hzK] with y hy
      exact h0 y hy
    exact continuousAt_const.congr h1.symm

theorem mollScale_sub_eq_zero (hf : IsMollifier f) {ε : ℝ} (hε : 0 < ε) {w v : ℂ} (hv : v ∉ closedBall w ε) :
    mollScale f ε (w - v) = 0 := by
  rw [mem_closedBall, dist_eq_norm, not_le] at hv
  have h1 : 1 ≤ ‖(w - v) / (ε : ℂ)‖ := by
    rw [norm_div, Complex.norm_of_nonneg hε.le, one_le_div hε, norm_sub_rev]
    exact hv.le
  simp only [mollScale, mollifier_eq_zero_of_one_le hf h1, mul_zero]

theorem mollScale_nonneg (hf : IsMollifier f) (ε : ℝ) (z : ℂ) : 0 ≤ mollScale f ε z :=
  mul_nonneg (inv_nonneg.2 (sq_nonneg ε)) (hf.nonneg _)

theorem continuous_mollScale_sub (hf : IsMollifier f) (ε : ℝ) (w : ℂ) :
    Continuous fun v => mollScale f ε (w - v) :=
  continuous_const.mul (hf.contDiff.continuous.comp ((continuous_const.sub continuous_id).div_const _))

theorem integrable_mollScale_sub (hf : IsMollifier f) {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    Integrable fun v => mollScale f ε (w - v) :=
  (continuous_mollScale_sub hf ε w).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall w ε) fun _ hv => mollScale_sub_eq_zero hf hε hv)

/-- `∫ f_ε(w − v) dv = 1`. -/
theorem integral_mollScale_sub (hf : IsMollifier f) {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    ∫ v, mollScale f ε (w - v) = 1 := by
  have h1 : (fun v => mollScale f ε (w - v)) = fun v => (ε ^ 2)⁻¹ * f (ε⁻¹ • (v - w)) := by
    funext v
    simp only [mollScale]
    congr 1
    apply hf.radial
    rw [norm_div, Complex.norm_of_nonneg hε.le, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε),
      norm_sub_rev, div_eq_inv_mul]
  have h2 : ∫ v, f (ε⁻¹ • (v - w)) = ∫ v, f (ε⁻¹ • v) :=
    integral_sub_right_eq_self (fun z => f (ε⁻¹ • z)) w
  rw [h1, integral_const_mul, h2, Measure.integral_comp_inv_smul_of_nonneg volume f hε.le, hf.integral_eq_one,
    Complex.finrank_real_complex, smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_ne_zero 2 hε.ne')]

theorem abs_log_sub_log_le {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ m⁻¹ * |a - b| := by
  have key : ∀ {p q : ℝ}, m ≤ p → m ≤ q → Real.log q - Real.log p ≤ m⁻¹ * |p - q| := by
    intro p q hp hq
    have hp0 : 0 < p := hm.trans_le hp
    have hq0 : 0 < q := hm.trans_le hq
    rw [← Real.log_div hq0.ne' hp0.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hq0 hp0)
    have h2 : q / p - 1 = (q - p) / p := by rw [sub_div, div_self hp0.ne']
    have h3 : (q - p) / p ≤ m⁻¹ * |p - q| := by
      rw [div_le_iff₀ hp0]
      have h4 : 1 ≤ m⁻¹ * p := by rw [inv_mul_eq_div, le_div_iff₀ hm]; linarith
      have h5 : q - p ≤ |p - q| := by rw [abs_sub_comm]; exact le_abs_self _
      nlinarith [abs_nonneg (p - q)]
    linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have := key ha hb
    linarith
  · have := key hb ha
    rw [abs_sub_comm] at this
    linarith

/-- **The average of `log |φ'|` against `f_ε(w − ·)`** differs from `log |φ'(w)|` by `O(ε)`, uniformly for `w` in a
compact subset of `ψ(B(c, r))`. -/
theorem exists_integral_log_sub_le (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r))
    (hf : IsMollifier f) {K' : Set ℂ} (hK' : IsCompact K') (hK'W : K' ⊆ ψ '' ball c r) :
    ∃ L δ : ℝ, 0 ≤ L ∧ 0 < δ ∧ ∀ w ∈ K', ∀ ε ∈ Ioc 0 δ,
      |(∫ v, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ * mollScale f ε (w - v)) -
        Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖| ≤ L * ε := by
  have hW := isOpen_image hψ hinj
  obtain ⟨δ', hδ', hδ'W⟩ := hK'.exists_cthickening_subset_open hW hK'W
  have hL' : IsCompact (cthickening δ' K') := hK'.cthickening
  have hφd := differentiableOn_invFunOn hψ hinj
  have hφ'd : DifferentiableOn ℂ (deriv (Function.invFunOn ψ (ball c r))) (ψ '' ball c r) := hφd.deriv hW
  have hφ''c : ContinuousOn (deriv (deriv (Function.invFunOn ψ (ball c r)))) (ψ '' ball c r) :=
    (hφ'd.deriv hW).continuousOn
  obtain ⟨B3, hB3⟩ := hL'.exists_bound_of_continuousOn (hφ''c.mono hδ'W)
  have hK : IsCompact (Function.invFunOn ψ (ball c r) '' cthickening δ' K') :=
    hL'.image_of_continuousOn (hφd.continuousOn.mono hδ'W)
  have hKb : Function.invFunOn ψ (ball c r) '' cthickening δ' K' ⊆ ball c r := by
    rintro _ ⟨w, hw, rfl⟩
    exact invFunOn_mem (hδ'W hw)
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn ((hψ.deriv isOpen_ball).continuousOn.mono hKb)
  have hB1' : 0 < max B1 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlow : ∀ z ∈ cthickening δ' K', (max B1 1)⁻¹ ≤ ‖deriv (Function.invFunOn ψ (ball c r)) z‖ := by
    intro z hz
    rw [norm_deriv_invFunOn hψ hinj (hδ'W hz)]
    have hb := hB1 _ ⟨z, hz, rfl⟩
    have hpos : 0 < ‖deriv ψ (Function.invFunOn ψ (ball c r) z)‖ :=
      norm_pos_iff.2 (deriv_ne_zero hψ hinj (invFunOn_mem (hδ'W hz)))
    exact inv_anti₀ hpos (hb.trans (le_max_left _ _))
  have hne : ∀ z ∈ ψ '' ball c r, deriv (Function.invFunOn ψ (ball c r)) z ≠ 0 := by
    intro z hz
    rw [(hasDerivAt_invFunOn hψ hinj hz).deriv]
    exact inv_ne_zero (deriv_ne_zero hψ hinj (invFunOn_mem hz))
  have hbc : ContinuousOn (fun v => Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖) (ψ '' ball c r) :=
    hφ'd.continuousOn.norm.log fun z hz => norm_ne_zero_iff.2 (hne z hz)
  refine ⟨max B1 1 * max B3 0, δ', mul_nonneg hB1'.le (le_max_right _ _), hδ', fun w hw ε hε => ?_⟩
  have hεpos : 0 < ε := hε.1
  have hsub : closedBall w δ' ⊆ cthickening δ' K' := closedBall_subset_cthickening hw δ'
  have hwδ : w ∈ closedBall w δ' := mem_closedBall_self hδ'.le
  have hlip : ∀ v ∈ closedBall w δ',
      |Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ -
        Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖| ≤ max B1 1 * max B3 0 * ‖v - w‖ := by
    intro v hv
    have hd : ‖deriv (Function.invFunOn ψ (ball c r)) v - deriv (Function.invFunOn ψ (ball c r)) w‖ ≤
        max B3 0 * ‖v - w‖ :=
      (convex_closedBall w δ').norm_image_sub_le_of_norm_deriv_le
        (fun z hz => hφ'd.differentiableAt (hW.mem_nhds (hδ'W (hsub hz))))
        (fun z hz => (hB3 z (hsub hz)).trans (le_max_left _ _)) hwδ hv
    have h1 := abs_log_sub_log_le (inv_pos.2 hB1') (hlow v (hsub hv)) (hlow w (hsub hwδ))
    rw [inv_inv] at h1
    calc _ ≤ max B1 1 * |‖deriv (Function.invFunOn ψ (ball c r)) v‖ -
          ‖deriv (Function.invFunOn ψ (ball c r)) w‖| := h1
      _ ≤ max B1 1 * (max B3 0 * ‖v - w‖) :=
          mul_le_mul_of_nonneg_left ((abs_norm_sub_norm_le _ _).trans hd) hB1'.le
      _ = max B1 1 * max B3 0 * ‖v - w‖ := by ring
  have hεsub : closedBall w ε ⊆ ψ '' ball c r :=
    ((closedBall_subset_closedBall hε.2).trans hsub).trans hδ'W
  have hprod : Continuous fun v =>
      Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ * mollScale f ε (w - v) :=
    continuous_of_continuousOn_of_eq_zero hW isClosed_closedBall hεsub
      (hbc.mul (continuous_mollScale_sub hf ε w).continuousOn)
      fun v hv => by simp only [mollScale_sub_eq_zero hf hεpos hv, mul_zero]
  have hpi : Integrable fun v =>
      Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ * mollScale f ε (w - v) :=
    hprod.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall w ε)
      fun v hv => by simp only [mollScale_sub_eq_zero hf hεpos hv, mul_zero])
  have hmi := integrable_mollScale_sub hf hεpos w
  have e : (∫ v, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ * mollScale f ε (w - v)) -
      Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖ =
      ∫ v, (Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ -
        Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖) * mollScale f ε (w - v) := by
    have h1 : (fun v => (Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ -
        Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖) * mollScale f ε (w - v)) =
        fun v => Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ * mollScale f ε (w - v) -
          Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖ * mollScale f ε (w - v) := by
      funext v; ring
    rw [h1, integral_sub hpi (hmi.const_mul _), integral_const_mul, integral_mollScale_sub hf hεpos w, mul_one]
  rw [e]
  have hbound : ∀ v, ‖(Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ -
      Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖) * mollScale f ε (w - v)‖ ≤
      max B1 1 * max B3 0 * ε * mollScale f ε (w - v) := by
    intro v
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollScale_nonneg hf ε _)]
    by_cases hv : v ∈ closedBall w ε
    · refine mul_le_mul_of_nonneg_right ?_ (mollScale_nonneg hf ε _)
      have hvδ : v ∈ closedBall w δ' := closedBall_subset_closedBall hε.2 hv
      have hvw : ‖v - w‖ ≤ ε := by rwa [mem_closedBall, dist_eq_norm] at hv
      exact (hlip v hvδ).trans (mul_le_mul_of_nonneg_left hvw (mul_nonneg hB1'.le (le_max_right _ _)))
    · rw [mollScale_sub_eq_zero hf hεpos hv, mul_zero, mul_zero]
  have h2 := norm_integral_le_of_norm_le (hmi.const_mul (max B1 1 * max B3 0 * ε))
    (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs, integral_const_mul, integral_mollScale_sub hf hεpos w, mul_one] at h2
  exact h2

end Straighten

end LQGMeasureChart

section

variable {c : ℂ} {r : ℝ} {ψ : ℂ → ℂ} {f : ℂ → ℝ}

open LQGMeasureChart LQGMeasureChart.Straighten

/-! ### The comparison -/

/-- **Straightening the bump: the pulled-back smoothed field at scale `ε` is the smoothed field at scale `ε |φ'|`.**
For `ψ` injective and holomorphic on `B(c, r)`, `φ = ψ⁻¹`, a bump function `f`, a distribution `g` on `B(c, r)` with
local regularity `C^{-1/2}_loc` and a compact set `K' ⊆ ψ(B(c, r))`, there are `C` and `ε₀ > 0` such that for
`w ∈ K'` and `0 < ε ≤ ε₀`, with `x = φ(w)` and `d = |φ'(w)|`,
`|(g ∘ φ + Q log |φ'|) ∗ f_ε(w) − ((g ∗ f_{ε d})(x) + Q log d)| ≤ C ε^{1/2}`, `Q = 2/γ + γ/2`. -/
theorem pullbackPairing_mollScale_sub_le (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r))
    (γ : ℝ) (hf : IsMollifier f) {g : LQGMetric.DistOn (disc c r)} (hg : HasLocalRegularity g (-(1 / 2)))
    {K' : Set ℂ} (hK' : IsCompact K') (hK'W : K' ⊆ ψ '' ball c r) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ w ∈ K', ∀ ε ∈ Ioc 0 ε₀,
      |pullbackPairing γ g ψ (fun v => mollScale f ε (w - v)) -
        (pairFun g (fun y => mollScale f (ε * ‖deriv (Function.invFunOn ψ (ball c r)) w‖)
            (Function.invFunOn ψ (ball c r) w - y)) +
          (2 / γ + γ / 2) * Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖)| ≤ C * Real.sqrt ε := by
  obtain ⟨R, A, B, ε₀, hR, hA, hB, hε₀, H⟩ := exists_profileErr_bounds hψ hinj hf hK' hK'W
  obtain ⟨L, δL, hL0, hδL, HL⟩ := exists_integral_log_sub_le hψ hinj hf hK' hK'W
  have hφc : ContinuousOn (Function.invFunOn ψ (ball c r)) (ψ '' ball c r) :=
    (differentiableOn_invFunOn hψ hinj).continuousOn
  have hK : IsCompact (Function.invFunOn ψ (ball c r) '' K') := hK'.image_of_continuousOn (hφc.mono hK'W)
  have hKb : Function.invFunOn ψ (ball c r) '' K' ⊆ ball c r := by
    rintro _ ⟨w, hw, rfl⟩
    exact invFunOn_mem (hK'W hw)
  obtain ⟨C, t₀, ht₀, hC⟩ := hg _ hK hKb
  have hBpos : 0 < B := by linarith
  refine ⟨(R + 1) ^ 3 * A * |C| * Real.sqrt B + |2 / γ + γ / 2| * L,
    min (min ε₀ δL) (min (t₀ / ((R + 1) * B)) 1), lt_min (lt_min hε₀ hδL) (lt_min (by positivity) one_pos),
    ?_⟩
  intro w hw ε hε
  have hεpos : 0 < ε := hε.1
  have hεε₀ : ε ≤ ε₀ := hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεδL : ε ≤ δL := hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεt₀ : ε ≤ t₀ / ((R + 1) * B) := hε.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε ≤ 1 := hε.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hxb, hψx, hBd, hdB, hball, hPcd, hP0, hPsup, hPder⟩ := H w hw ε ⟨hεpos, hεε₀⟩ _ _ rfl rfl
  have hlog := HL w hw ε ⟨hεpos, hεδL⟩
  have hxK : Function.invFunOn ψ (ball c r) w ∈ Function.invFunOn ψ (ball c r) '' K' := ⟨w, hw, rfl⟩
  set x := Function.invFunOn ψ (ball c r) w with hx
  set d := ‖deriv (Function.invFunOn ψ (ball c r)) w‖ with hd
  set Q := 2 / γ + γ / 2 with hQ
  set P := profileErr c r ψ f ε x (ε * d) with hP
  have hd0 : 0 < d := lt_of_lt_of_le (inv_pos.2 hBpos) hBd
  have ht : 0 < ε * d := mul_pos hεpos hd0
  have hR1 : 0 < R + 1 := by linarith
  -- the pullback pairing is the pairing with the transported test plus the logarithmic term
  have hpb : pullbackPairing γ g ψ (fun v => mollScale f ε (w - v)) =
      pairFun g (transportTest c r ψ f ε w) +
        Q * ∫ v, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ * mollScale f ε (w - v) := rfl
  -- decomposition of the transported test
  have hT : transportTest c r ψ f ε w = (fun y => mollScale f (ε * d) (x - y)) +
      fun y => ((ε * d) ^ 2)⁻¹ * P ((y - x) / ((ε * d : ℝ) : ℂ)) := by
    rw [← hψx]
    exact transportTest_eq_add hf ht
  have hu1eq : (fun y => mollScale f (ε * d) (x - y)) =
      fun y => ((ε * d) ^ 2)⁻¹ * f ((y - x) / ((ε * d : ℝ) : ℂ)) := by
    funext y
    simp only [mollScale]
    congr 1
    apply hf.radial
    rw [← neg_sub, neg_div, norm_neg]
  have hu1 := scaled_admissible (V := disc c r) hf.contDiff (ρ := 1)
    (fun z hz => by
      by_contra h
      exact hz (mollifier_eq_zero_of_one_le hf (not_lt.1 h)))
    ht ((closedBall_subset_closedBall (by nlinarith)).trans hball) (((ε * d) ^ 2)⁻¹)
  have hu2 := scaled_admissible (V := disc c r) hPcd (ρ := R + 1)
    (fun z hz => by
      by_contra h
      exact hz (hP0 z (by linarith [not_lt.1 h])))
    ht hball (((ε * d) ^ 2)⁻¹)
  rw [← hu1eq] at hu1
  have hsplit : pairFun g (transportTest c r ψ f ε w) = pairFun g (fun y => mollScale f (ε * d) (x - y)) +
      pairFun g (fun y => ((ε * d) ^ 2)⁻¹ * P ((y - x) / ((ε * d : ℝ) : ℂ))) := by
    rw [hT]
    exact pairFun_add g hu1 hu2
  -- the error term: the regularity bound at scale `s = (R + 1) ε d`
  set M := (R + 1) * A * ε with hM_def
  have hM : 0 < M := by positivity
  set s := (R + 1) * (ε * d) with hs_def
  have hs : 0 < s := by positivity
  set η : ℂ → ℝ := fun z => M⁻¹ * P (((R + 1 : ℝ) : ℂ) * z) with hη_def
  have hηcd : ContDiff ℝ (⊤ : ℕ∞) η := contDiff_const.mul (hPcd.comp (contDiff_const.mul contDiff_id))
  have hηsupp : ∀ z, η z ≠ 0 → ‖z‖ < 1 := by
    intro z hz
    have h1 : P (((R + 1 : ℝ) : ℂ) * z) ≠ 0 := right_ne_zero_of_mul hz
    by_contra h2
    apply h1
    apply hP0
    rw [norm_ofReal_mul _ hR1.le]
    nlinarith [not_lt.1 h2]
  have hηts : tsupport η ⊆ ball 0 1 := by
    have h1 : Function.support η ⊆ closedBall 0 (R / (R + 1)) := by
      intro z hz
      have hz' : M⁻¹ * P (((R + 1 : ℝ) : ℂ) * z) ≠ 0 := hz
      rw [mem_closedBall_zero_iff, le_div_iff₀ hR1]
      by_contra h2
      apply hz'
      rw [hP0 _ (by rw [norm_ofReal_mul _ hR1.le]; linarith [not_le.1 h2]), mul_zero]
    exact (closure_minimal h1 isClosed_closedBall).trans
      (closedBall_subset_ball ((div_lt_one hR1).2 (by linarith)))
  have hη1 : ∀ z, |η z| ≤ 1 := by
    intro z
    show |M⁻¹ * P (((R + 1 : ℝ) : ℂ) * z)| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.2 hM)]
    calc M⁻¹ * |P (((R + 1 : ℝ) : ℂ) * z)| ≤ M⁻¹ * (A * ε) :=
          mul_le_mul_of_nonneg_left (hPsup _) (by positivity)
      _ = (R + 1)⁻¹ := by
          rw [hM_def, show (R + 1) * A * ε = (R + 1) * (A * ε) by ring, mul_inv, mul_assoc,
            inv_mul_cancel₀ (by positivity : A * ε ≠ 0), mul_one]
      _ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hPlip : ∀ a b : ℂ, |P a - P b| ≤ A * ε * ‖a - b‖ := by
    intro a b
    have := (convex_univ : Convex ℝ (univ : Set ℂ)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hPcd.differentiable (by simp)) z) (fun z _ => hPder z) (mem_univ b) (mem_univ a)
    rwa [Real.norm_eq_abs] at this
  have hηlip : LipschitzWith 1 η := by
    apply LipschitzWith.of_dist_le_mul
    intro z₁ z₂
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    show |M⁻¹ * P (((R + 1 : ℝ) : ℂ) * z₁) - M⁻¹ * P (((R + 1 : ℝ) : ℂ) * z₂)| ≤ ‖z₁ - z₂‖
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hM)]
    calc M⁻¹ * |P (((R + 1 : ℝ) : ℂ) * z₁) - P (((R + 1 : ℝ) : ℂ) * z₂)|
        ≤ M⁻¹ * (A * ε * ‖((R + 1 : ℝ) : ℂ) * z₁ - ((R + 1 : ℝ) : ℂ) * z₂‖) :=
          mul_le_mul_of_nonneg_left (hPlip _ _) (by positivity)
      _ = ‖z₁ - z₂‖ := by
          rw [← mul_sub, norm_ofReal_mul _ hR1.le,
            show A * ε * ((R + 1) * ‖z₁ - z₂‖) = M * ‖z₁ - z₂‖ by rw [hM_def]; ring, ← mul_assoc,
            inv_mul_cancel₀ hM.ne', one_mul]
  have hηd : ∀ z, ‖fderiv ℝ η z‖ ≤ 1 := by
    intro z
    have := norm_fderiv_le_of_lipschitz ℝ hηlip (x₀ := z)
    simpa using this
  have hu3 := scaled_admissible (V := disc c r) hηcd hηsupp hs (by rw [one_mul]; exact hball) ((s ^ 2)⁻¹)
  have hu2eq : (fun y => ((ε * d) ^ 2)⁻¹ * P ((y - x) / ((ε * d : ℝ) : ℂ))) =
      fun y => (M * (R + 1) ^ 2) * ((s ^ 2)⁻¹ * η ((y - x) / (s : ℂ))) := by
    funext y
    have hR' : ((R + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR1.ne'
    have e1 : ((R + 1 : ℝ) : ℂ) * ((y - x) / (s : ℂ)) = (y - x) / ((ε * d : ℝ) : ℂ) := by
      rw [hs_def, Complex.ofReal_mul (R + 1) (ε * d), mul_div_assoc', mul_div_mul_left _ _ hR']
    have e2 : (R + 1) ^ 2 * (s ^ 2)⁻¹ = ((ε * d) ^ 2)⁻¹ := by
      rw [hs_def, mul_pow (R + 1) (ε * d) 2, mul_inv ((R + 1) ^ 2) ((ε * d) ^ 2), ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero 2 hR1.ne'), one_mul]
    simp only [hη_def, e1]
    calc ((ε * d) ^ 2)⁻¹ * P ((y - x) / ((ε * d : ℝ) : ℂ))
        = (M * M⁻¹) * ((R + 1) ^ 2 * (s ^ 2)⁻¹) * P ((y - x) / ((ε * d : ℝ) : ℂ)) := by
          rw [mul_inv_cancel₀ hM.ne', e2, one_mul]
      _ = M * (R + 1) ^ 2 * ((s ^ 2)⁻¹ * (M⁻¹ * P ((y - x) / ((ε * d : ℝ) : ℂ)))) := by ring
  have hst₀ : s ≤ t₀ := by
    rw [hs_def]
    calc (R + 1) * (ε * d) ≤ (R + 1) * (ε * B) := by gcongr
      _ = ε * ((R + 1) * B) := by ring
      _ ≤ t₀ / ((R + 1) * B) * ((R + 1) * B) := by gcongr
      _ = t₀ := div_mul_cancel₀ _ (by positivity)
  have hreg := hC x hxK s ⟨hs, hst₀⟩ η hηcd hηts hη1 hηd
  have hpair2 : |pairFun g (fun y => ((ε * d) ^ 2)⁻¹ * P ((y - x) / ((ε * d : ℝ) : ℂ)))| ≤
      (R + 1) ^ 3 * A * |C| * Real.sqrt B * Real.sqrt ε := by
    have hMR : 0 < M * (R + 1) ^ 2 := by positivity
    rw [hu2eq, pairFun_const_mul g _ hu3, abs_mul, abs_of_pos hMR]
    have hrpow : s ^ (-(1 / 2 : ℝ)) = (Real.sqrt s)⁻¹ := by
      rw [Real.rpow_neg hs.le, ← Real.sqrt_eq_rpow]
    rw [hrpow] at hreg
    have hsq : ε ≤ Real.sqrt B * Real.sqrt ε * Real.sqrt s := by
      have hBd1 : 1 ≤ B * d := by
        have := mul_le_mul_of_nonneg_left hBd hBpos.le
        rwa [mul_inv_cancel₀ hBpos.ne'] at this
      have hBs : ε ≤ B * s := by
        calc ε = ε * 1 := (mul_one ε).symm
          _ ≤ ε * (B * d) := mul_le_mul_of_nonneg_left hBd1 hεpos.le
          _ = B * (ε * d) := by ring
          _ ≤ B * ((R + 1) * (ε * d)) :=
              mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ht.le (by linarith)) hBpos.le
      have h2 : Real.sqrt ε ≤ Real.sqrt B * Real.sqrt s := by
        rw [← Real.sqrt_mul hBpos.le]
        exact Real.sqrt_le_sqrt hBs
      calc ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hεpos.le).symm
        _ ≤ Real.sqrt ε * (Real.sqrt B * Real.sqrt s) :=
            mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
        _ = Real.sqrt B * Real.sqrt ε * Real.sqrt s := by ring
    have hsqs : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
    calc M * (R + 1) ^ 2 * |pairFun g (fun y => (s ^ 2)⁻¹ * η ((y - x) / (s : ℂ)))|
        ≤ M * (R + 1) ^ 2 * (|C| * (Real.sqrt s)⁻¹) := by
          refine mul_le_mul_of_nonneg_left (hreg.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = (R + 1) ^ 3 * A * |C| * (ε * (Real.sqrt s)⁻¹) := by rw [hM_def]; ring
      _ ≤ (R + 1) ^ 3 * A * |C| * (Real.sqrt B * Real.sqrt ε) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← div_eq_mul_inv, div_le_iff₀ hsqs]
          exact hsq
      _ = (R + 1) ^ 3 * A * |C| * Real.sqrt B * Real.sqrt ε := by ring
  -- the logarithmic term
  have hlog' : |Q * (∫ v, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ * mollScale f ε (w - v)) -
      Q * Real.log d| ≤ |Q| * L * Real.sqrt ε := by
    rw [← mul_sub, abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hlog.trans ?_) (abs_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hL0
    calc ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hεpos.le).symm
      _ ≤ Real.sqrt ε * 1 := mul_le_mul_of_nonneg_left (Real.sqrt_le_one.2 hε1) (Real.sqrt_nonneg _)
      _ = Real.sqrt ε := mul_one _
  rw [hpb, hsplit]
  calc |pairFun g (fun y => mollScale f (ε * d) (x - y)) +
        pairFun g (fun y => ((ε * d) ^ 2)⁻¹ * P ((y - x) / ((ε * d : ℝ) : ℂ))) +
        Q * (∫ v, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ * mollScale f ε (w - v)) -
        (pairFun g (fun y => mollScale f (ε * d) (x - y)) + Q * Real.log d)|
      = |pairFun g (fun y => ((ε * d) ^ 2)⁻¹ * P ((y - x) / ((ε * d : ℝ) : ℂ))) +
          (Q * (∫ v, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) v‖ * mollScale f ε (w - v)) -
            Q * Real.log d)| := by
        congr 1; ring
    _ ≤ (R + 1) ^ 3 * A * |C| * Real.sqrt B * Real.sqrt ε + |Q| * L * Real.sqrt ε :=
        (abs_add_le _ _).trans (add_le_add hpair2 hlog')
    _ = ((R + 1) ^ 3 * A * |C| * Real.sqrt B + |Q| * L) * Real.sqrt ε := by ring

/-- **The smoothed exponents of the pulled-back field and of the field** (Sheffield–Wang (2016), §3.2, after (3.4)):
under the hypotheses of `pullbackPairing_mollScale_sub_le` and `γ > 0`, with `x = φ(w)`, `d = |φ'(w)|`,
`|h̃_ε(w) − (h̃_{ε d}(x) + 2 log d)| ≤ C ε^{1/2}`, where `h̃` on the left is the exponent of `g ∘ φ + Q log |φ'|` and on
the right that of `g`; `γ Q = 2 + γ²/2` turns `γ Q log d` into `(γ²/2) log d + 2 log d`. -/
theorem smoothExponent_pullbackPairing_sub_le (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r))
    {γ : ℝ} (hγ : 0 < γ) (hf : IsMollifier f) {g : LQGMetric.DistOn (disc c r)}
    (hg : HasLocalRegularity g (-(1 / 2))) {K' : Set ℂ} (hK' : IsCompact K') (hK'W : K' ⊆ ψ '' ball c r) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ w ∈ K', ∀ ε ∈ Ioc 0 ε₀,
      |smoothExponent γ f (pullbackPairing γ g ψ) ε w -
        (smoothExponent γ f (pairFun g) (ε * ‖deriv (Function.invFunOn ψ (ball c r)) w‖)
            (Function.invFunOn ψ (ball c r) w) +
          2 * Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖)| ≤ C * Real.sqrt ε := by
  obtain ⟨C, ε₀, hε₀, H⟩ := pullbackPairing_mollScale_sub_le hψ hinj γ hf hg hK' hK'W
  refine ⟨γ * C, ε₀, hε₀, fun w hw ε hε => ?_⟩
  have hwW := hK'W hw
  have hd0 : 0 < ‖deriv (Function.invFunOn ψ (ball c r)) w‖ := by
    rw [norm_deriv_invFunOn hψ hinj hwW]
    exact inv_pos.2 (norm_pos_iff.2 (deriv_ne_zero hψ hinj (invFunOn_mem hwW)))
  have h1 := H w hw ε hε
  set d := ‖deriv (Function.invFunOn ψ (ball c r)) w‖ with hd
  have hlog : Real.log (ε * d) = Real.log ε + Real.log d := Real.log_mul hε.1.ne' hd0.ne'
  have hγQ : γ * (2 / γ + γ / 2) = 2 + γ ^ 2 / 2 := by
    have h2 : γ * (2 / γ) = 2 := by rw [mul_div_assoc', mul_div_cancel_left₀ 2 hγ.ne']
    rw [mul_add, h2]
    ring
  have e : smoothExponent γ f (pullbackPairing γ g ψ) ε w -
      (smoothExponent γ f (pairFun g) (ε * d) (Function.invFunOn ψ (ball c r) w) + 2 * Real.log d) =
      γ * (pullbackPairing γ g ψ (fun v => mollScale f ε (w - v)) -
        (pairFun g (fun y => mollScale f (ε * d) (Function.invFunOn ψ (ball c r) w - y)) +
          (2 / γ + γ / 2) * Real.log d)) := by
    simp only [smoothExponent, hlog]
    linear_combination (Real.log d) * hγQ
  rw [e, abs_mul, abs_of_pos hγ, mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 hγ.le

end

end MatedCRT
