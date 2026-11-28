import MatedCRT.FirstPass.Derived.LQGMeasureChartSmooth
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Straightening the transported bump: the profile estimate

Let `ψ` be injective and holomorphic on the disc `B(c, r)`, `φ = ψ⁻¹` on `ψ(B(c, r))`, and `f` a bump function of
Sheffield–Wang (`IsMollifier`). The pairing of the pulled-back field `h ∘ φ` with `f_ε(w − ·)` is the pairing of `h`
with the transported test `T(y) = f_ε(w − ψ y) |ψ'(y)|²` on `B(c, r)` (`transportTest`; Sheffield–Wang,
*Field-measure correspondence in Liouville quantum gravity almost surely commutes with all conformal maps
simultaneously*, arXiv:1605.06171v2, Proposition 2.3 and Remark 3.3).

Write `x = φ(w)`, `d = |φ'(w)| = |ψ'(x)|⁻¹` and `t = ε d`. In the coordinates `y = x + t v` the rescaled test is
`t² T(x + t v) = d² |ψ'(x + t v)|² f((w − ψ(x + t v))/ε)`. Taylor's formula on a compact set gives the prefactor
`1 + O(ε)` and the argument `−d ψ'(x) v + O(ε)`, both in `C¹`; the leading linear map `−d ψ'(x)` has modulus one, so
by the radial symmetry of `f` the leading profile is `f(v)`. Hence (`exists_profileErr_bounds`), uniformly for `w` in
a compact subset of `ψ(B(c, r))` and small `ε`,
`T = f_t(x − ·) + t⁻² P((· − x)/t)` (`transportTest_eq_add`), where `P = profileErr` is smooth, vanishes outside a
fixed disc `B(0, R)`, and satisfies `|P| ≤ A ε` and `‖DP‖ ≤ A ε`.

This is the first half of the straightening step in the fixed-scale form of the coordinate change of
Sheffield–Wang (2016), Theorem 1.4: after it, the local regularity `h ∈ C^{-1/2}_loc` bounds the pairing of `h` with
the error term by `O(ε^{1/2})` (`LQGMeasureChartStraightenExponent`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT

namespace LQGMeasureChart

/-- **The transported test** `y ↦ f_ε(w − ψ y) |ψ'(y)|²` on `B(c, r)`, extended by `0`: the test paired with the field
`h` in `(h ∘ φ) ∗ f_ε(w)` (Sheffield–Wang (2016), Proposition 2.3 and Remark 3.3; it is the first argument of
`pairFun` in `pullbackPairing γ h ψ (fun v => mollScale f ε (w - v))`). -/
def transportTest (c : ℂ) (r : ℝ) (ψ : ℂ → ℂ) (f : ℂ → ℝ) (ε : ℝ) (w : ℂ) : ℂ → ℝ :=
  (ball c r).indicator fun y => mollScale f ε (w - ψ y) * ‖deriv ψ y‖ ^ 2

/-- **The rescaled error profile** `P(v) = t² T(x + t v) − f(v)` of the transported test `T` centred at `w = ψ(x)`. -/
def profileErr (c : ℂ) (r : ℝ) (ψ : ℂ → ℂ) (f : ℂ → ℝ) (ε : ℝ) (x : ℂ) (t : ℝ) (v : ℂ) : ℝ :=
  t ^ 2 * transportTest c r ψ f ε (ψ x) (x + (t : ℂ) * v) - f v

namespace Straighten

/-- The main part `(d² |ψ'(x + t v)|² − 1) f(A v)` of the profile, `t = ε d`, `A v = (ψ x − ψ(x + t v))/ε`. -/
def profileMain (ψ : ℂ → ℂ) (f : ℂ → ℝ) (ε d : ℝ) (x v : ℂ) : ℝ :=
  (d ^ 2 * ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)‖ ^ 2 - 1) * f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ))

/-- The remaining part `f(A v) − f(−d ψ'(x) v)` of the profile. -/
def profileRest (ψ : ℂ → ℂ) (f : ℂ → ℝ) (ε d : ℝ) (x v : ℂ) : ℝ :=
  f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ)) - f (-((d : ℂ) * deriv ψ x) * v)

variable {c : ℂ} {r : ℝ} {ψ : ℂ → ℂ} {f : ℂ → ℝ}

/-! ### The inverse of an injective holomorphic map on a disc -/

theorem invFunOn_mem {w : ℂ} (hw : w ∈ ψ '' ball c r) : Function.invFunOn ψ (ball c r) w ∈ ball c r :=
  Function.invFunOn_mem hw

theorem apply_invFunOn {w : ℂ} (hw : w ∈ ψ '' ball c r) : ψ (Function.invFunOn ψ (ball c r) w) = w :=
  Function.invFunOn_eq hw

theorem invFunOn_apply (hinj : InjOn ψ (ball c r)) {x : ℂ} (hx : x ∈ ball c r) :
    Function.invFunOn ψ (ball c r) (ψ x) = x :=
  hinj.leftInvOn_invFunOn hx

theorem isOpen_image (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r)) :
    IsOpen (ψ '' ball c r) :=
  QuantumZipper.CA.isOpen_image_of_injOn' isOpen_ball hψ hinj

theorem deriv_ne_zero (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r)) {x : ℂ}
    (hx : x ∈ ball c r) : deriv ψ x ≠ 0 :=
  QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hψ hinj hx

theorem invFunOn_eq_symm (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r)) {w : ℂ}
    (hw : w ∈ ψ '' ball c r) :
    Function.invFunOn ψ (ball c r) w = (QuantumZipper.CA.univalentOPH isOpen_ball hψ hinj).symm w := by
  have hw' : w ∈ (QuantumZipper.CA.univalentOPH isOpen_ball hψ hinj).target := hw
  refine hinj (invFunOn_mem hw) ((QuantumZipper.CA.univalentOPH isOpen_ball hψ hinj).map_target hw') ?_
  rw [apply_invFunOn hw, QuantumZipper.CA.univalentOPH_apply_symm_apply isOpen_ball hψ hinj hw]

theorem hasDerivAt_invFunOn (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r)) {w : ℂ}
    (hw : w ∈ ψ '' ball c r) :
    HasDerivAt (Function.invFunOn ψ (ball c r)) (deriv ψ (Function.invFunOn ψ (ball c r) w))⁻¹ w := by
  have h := QuantumZipper.CA.hasDerivAt_univalentOPH_symm isOpen_ball hψ hinj hw
  rw [← invFunOn_eq_symm hψ hinj hw] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_image hψ hinj).mem_nhds hw] with w' hw'
  exact invFunOn_eq_symm hψ hinj hw'

theorem norm_deriv_invFunOn (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r)) {w : ℂ}
    (hw : w ∈ ψ '' ball c r) :
    ‖deriv (Function.invFunOn ψ (ball c r)) w‖ = ‖deriv ψ (Function.invFunOn ψ (ball c r) w)‖⁻¹ := by
  rw [(hasDerivAt_invFunOn hψ hinj hw).deriv, norm_inv]

theorem differentiableOn_invFunOn (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r)) :
    DifferentiableOn ℂ (Function.invFunOn ψ (ball c r)) (ψ '' ball c r) :=
  fun _ hw => (hasDerivAt_invFunOn hψ hinj hw).differentiableAt.differentiableWithinAt

/-! ### Bounds for the bump function -/

theorem mollifier_eq_zero_of_one_le (hf : IsMollifier f) {z : ℂ} (hz : 1 ≤ ‖z‖) : f z = 0 := by
  by_contra h
  have h1 : z ∈ ball (0 : ℂ) 1 := hf.tsupport_subset (subset_tsupport f h)
  rw [mem_ball_zero_iff] at h1
  linarith

theorem mollifier_exists_bound (hf : IsMollifier f) :
    ∃ B : ℝ, 1 ≤ B ∧ (∀ z, |f z| ≤ B) ∧ (∀ z₁ z₂, |f z₁ - f z₂| ≤ B * ‖z₁ - z₂‖) ∧
      (∀ z, ‖fderiv ℝ f z‖ ≤ B) ∧ (∀ z₁ z₂, ‖fderiv ℝ f z₁ - fderiv ℝ f z₂‖ ≤ B * ‖z₁ - z₂‖) := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨B₀, hB₀⟩ := hf.contDiff.continuous.bounded_above_of_compact_support hf.hasCompactSupport
  obtain ⟨L₀, hL₀⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hf.hasCompactSupport hf.contDiff hn
  obtain ⟨B₁, hB₁⟩ := (hf.contDiff.continuous_fderiv hn).bounded_above_of_compact_support
    (hf.hasCompactSupport.fderiv ℝ)
  obtain ⟨L₁, hL₁⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hf.hasCompactSupport.fderiv ℝ)
    (hf.contDiff.fderiv_right (m := 1)
      (show ((1 + 1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.2 le_top)) one_ne_zero
  have h0 : B₀ ≤ max 1 (max B₀ (max (L₀ : ℝ) (max B₁ (L₁ : ℝ)))) :=
    le_max_of_le_right (le_max_left _ _)
  have h1 : (L₀ : ℝ) ≤ max 1 (max B₀ (max (L₀ : ℝ) (max B₁ (L₁ : ℝ)))) :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have h2 : B₁ ≤ max 1 (max B₀ (max (L₀ : ℝ) (max B₁ (L₁ : ℝ)))) :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have h3 : (L₁ : ℝ) ≤ max 1 (max B₀ (max (L₀ : ℝ) (max B₁ (L₁ : ℝ)))) :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
  refine ⟨max 1 (max B₀ (max (L₀ : ℝ) (max B₁ (L₁ : ℝ)))), le_max_left _ _, fun z => ?_, fun z₁ z₂ => ?_,
    fun z => (hB₁ z).trans h2, fun z₁ z₂ => ?_⟩
  · have := hB₀ z
    rw [Real.norm_eq_abs] at this
    exact this.trans h0
  · have := hL₀.dist_le_mul z₁ z₂
    rw [Real.dist_eq, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  · have := hL₁.dist_le_mul z₁ z₂
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))

/-! ### Mean value and Taylor estimates on a closed disc -/

theorem norm_ofReal_mul (t : ℝ) (ht : 0 ≤ t) (v : ℂ) : ‖(t : ℂ) * v‖ = t * ‖v‖ := by
  rw [norm_mul, Complex.norm_of_nonneg ht]

theorem norm_sub_le_of_deriv (hψ : DifferentiableOn ℂ ψ (ball c r)) {s : Set ℂ} (hs : Convex ℝ s)
    (hsb : s ⊆ ball c r) {B : ℝ} (hB : ∀ z ∈ s, ‖deriv ψ z‖ ≤ B) {y₁ y₂ : ℂ} (h₁ : y₁ ∈ s) (h₂ : y₂ ∈ s) :
    ‖ψ y₁ - ψ y₂‖ ≤ B * ‖y₁ - y₂‖ :=
  hs.norm_image_sub_le_of_norm_deriv_le (fun _ hz => hψ.differentiableAt (isOpen_ball.mem_nhds (hsb hz))) hB
    h₂ h₁

theorem norm_deriv_sub_le (hψ : DifferentiableOn ℂ ψ (ball c r)) {s : Set ℂ} (hs : Convex ℝ s)
    (hsb : s ⊆ ball c r) {B : ℝ} (hB : ∀ z ∈ s, ‖deriv (deriv ψ) z‖ ≤ B) {y₁ y₂ : ℂ} (h₁ : y₁ ∈ s)
    (h₂ : y₂ ∈ s) : ‖deriv ψ y₁ - deriv ψ y₂‖ ≤ B * ‖y₁ - y₂‖ :=
  norm_sub_le_of_deriv (hψ.deriv isOpen_ball) hs hsb hB h₁ h₂

theorem norm_taylor_le (hψ : DifferentiableOn ℂ ψ (ball c r)) {x : ℂ} {δ B : ℝ}
    (hxδ : closedBall x δ ⊆ ball c r) (hB : ∀ z ∈ closedBall x δ, ‖deriv (deriv ψ) z‖ ≤ B) {y : ℂ}
    (hy : y ∈ closedBall x δ) : ‖ψ y - ψ x - deriv ψ x * (y - x)‖ ≤ B * ‖y - x‖ ^ 2 := by
  have hyx : ‖y - x‖ ≤ δ := by rwa [mem_closedBall, dist_eq_norm] at hy
  have hρδ : closedBall x ‖y - x‖ ⊆ closedBall x δ := closedBall_subset_closedBall hyx
  have hsb : closedBall x ‖y - x‖ ⊆ ball c r := hρδ.trans hxδ
  have hxρ : x ∈ closedBall x ‖y - x‖ := mem_closedBall_self (norm_nonneg _)
  have hyρ : y ∈ closedBall x ‖y - x‖ := mem_closedBall.2 (le_of_eq (dist_eq_norm y x))
  have hg : ∀ z ∈ closedBall x ‖y - x‖,
      HasDerivAt (fun z => ψ z - deriv ψ x * z) (deriv ψ z - deriv ψ x) z := by
    intro z hz
    have h1 := (hψ.differentiableAt (isOpen_ball.mem_nhds (hsb hz))).hasDerivAt
    exact (h1.sub ((hasDerivAt_id' z).const_mul (deriv ψ x))).congr_deriv (by rw [mul_one])
  have hbound : ∀ z ∈ closedBall x ‖y - x‖,
      ‖deriv (fun z => ψ z - deriv ψ x * z) z‖ ≤ B * ‖y - x‖ := by
    intro z hz
    rw [(hg z hz).deriv]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x (hρδ hxρ))
    have hzx : ‖z - x‖ ≤ ‖y - x‖ := by rwa [mem_closedBall, dist_eq_norm] at hz
    calc ‖deriv ψ z - deriv ψ x‖ ≤ B * ‖z - x‖ :=
          norm_deriv_sub_le hψ (convex_closedBall x δ) hxδ hB (hρδ hz) (hρδ hxρ)
      _ ≤ B * ‖y - x‖ := mul_le_mul_of_nonneg_left hzx hB0
  have key := (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hg z hz).differentiableAt) hbound hxρ hyρ
  calc ‖ψ y - ψ x - deriv ψ x * (y - x)‖ = ‖(ψ y - deriv ψ x * y) - (ψ x - deriv ψ x * x)‖ := by
        congr 1; ring
    _ ≤ B * ‖y - x‖ * ‖y - x‖ := key
    _ = B * ‖y - x‖ ^ 2 := by ring

theorem abs_sq_norm_deriv_sub_le (hψ : DifferentiableOn ℂ ψ (ball c r)) {x : ℂ} {δ B : ℝ}
    (hxδ : closedBall x δ ⊆ ball c r) (hM1 : ∀ z ∈ closedBall x δ, ‖deriv ψ z‖ ≤ B)
    (hM2 : ∀ z ∈ closedBall x δ, ‖deriv (deriv ψ) z‖ ≤ B) {y₁ y₂ : ℂ} (h₁ : y₁ ∈ closedBall x δ)
    (h₂ : y₂ ∈ closedBall x δ) :
    |‖deriv ψ y₁‖ ^ 2 - ‖deriv ψ y₂‖ ^ 2| ≤ 2 * B * (B * ‖y₁ - y₂‖) := by
  have e : ‖deriv ψ y₁‖ ^ 2 - ‖deriv ψ y₂‖ ^ 2 =
      (‖deriv ψ y₁‖ + ‖deriv ψ y₂‖) * (‖deriv ψ y₁‖ - ‖deriv ψ y₂‖) := by ring
  have hnn : 0 ≤ ‖deriv ψ y₁‖ + ‖deriv ψ y₂‖ := by positivity
  rw [e, abs_mul, abs_of_nonneg hnn]
  have hs : ‖deriv ψ y₁‖ + ‖deriv ψ y₂‖ ≤ 2 * B := by linarith [hM1 y₁ h₁, hM1 y₂ h₂]
  have hd : |‖deriv ψ y₁‖ - ‖deriv ψ y₂‖| ≤ B * ‖y₁ - y₂‖ :=
    (abs_norm_sub_norm_le _ _).trans (norm_deriv_sub_le hψ (convex_closedBall x δ) hxδ hM2 h₁ h₂)
  exact mul_le_mul hs hd (abs_nonneg _) (by linarith [norm_nonneg (deriv ψ y₁), hM1 y₁ h₁])

theorem norm_arg_sub_le (hψ : DifferentiableOn ℂ ψ (ball c r)) {x : ℂ} {δ B : ℝ}
    (hxδ : closedBall x δ ⊆ ball c r) (hM2 : ∀ z ∈ closedBall x δ, ‖deriv (deriv ψ) z‖ ≤ B) {ε d : ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) {v : ℂ} (hy : x + ((ε * d : ℝ) : ℂ) * v ∈ closedBall x δ) :
    ‖(ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ) - -((d : ℂ) * deriv ψ x) * v‖ ≤
      B * ε * (d * ‖v‖) ^ 2 := by
  have hε' : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε.ne'
  have e : (ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ) - -((d : ℂ) * deriv ψ x) * v =
      -(ψ (x + ((ε * d : ℝ) : ℂ) * v) - ψ x - deriv ψ x * (x + ((ε * d : ℝ) : ℂ) * v - x)) / (ε : ℂ) := by
    rw [eq_div_iff hε', sub_mul, div_mul_cancel₀ _ hε']
    push_cast
    ring
  rw [e, norm_div, norm_neg, Complex.norm_of_nonneg hε.le, div_le_iff₀ hε]
  calc ‖ψ (x + ((ε * d : ℝ) : ℂ) * v) - ψ x - deriv ψ x * (x + ((ε * d : ℝ) : ℂ) * v - x)‖
      ≤ B * ‖x + ((ε * d : ℝ) : ℂ) * v - x‖ ^ 2 := norm_taylor_le hψ hxδ hM2 hy
    _ = B * ε * (d * ‖v‖) ^ 2 * ε := by
      rw [add_sub_cancel_left, norm_ofReal_mul _ (mul_nonneg hε.le hd)]
      ring

theorem norm_arg_sub_arg_le (hψ : DifferentiableOn ℂ ψ (ball c r)) {x : ℂ} {δ B : ℝ}
    (hxδ : closedBall x δ ⊆ ball c r) (hM1 : ∀ z ∈ closedBall x δ, ‖deriv ψ z‖ ≤ B) {ε d : ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) {v₁ v₂ : ℂ} (h₁ : x + ((ε * d : ℝ) : ℂ) * v₁ ∈ closedBall x δ)
    (h₂ : x + ((ε * d : ℝ) : ℂ) * v₂ ∈ closedBall x δ) :
    ‖(ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v₁)) / (ε : ℂ) - (ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v₂)) / (ε : ℂ)‖ ≤
      B * d * ‖v₁ - v₂‖ := by
  rw [← sub_div, norm_div, Complex.norm_of_nonneg hε.le, div_le_iff₀ hε]
  have e : ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v₁) - (ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v₂)) =
      ψ (x + ((ε * d : ℝ) : ℂ) * v₂) - ψ (x + ((ε * d : ℝ) : ℂ) * v₁) := by ring
  have e2 : x + ((ε * d : ℝ) : ℂ) * v₂ - (x + ((ε * d : ℝ) : ℂ) * v₁) = ((ε * d : ℝ) : ℂ) * (v₂ - v₁) := by
    ring
  rw [e]
  calc ‖ψ (x + ((ε * d : ℝ) : ℂ) * v₂) - ψ (x + ((ε * d : ℝ) : ℂ) * v₁)‖
      ≤ B * ‖x + ((ε * d : ℝ) : ℂ) * v₂ - (x + ((ε * d : ℝ) : ℂ) * v₁)‖ :=
        norm_sub_le_of_deriv hψ (convex_closedBall x δ) hxδ hM1 h₂ h₁
    _ = B * d * ‖v₁ - v₂‖ * ε := by
        rw [e2, norm_ofReal_mul _ (mul_nonneg hε.le hd), norm_sub_rev]
        ring

/-- The derivative of the remaining part of the profile. -/
theorem norm_fderiv_profileRest_le (hψ : DifferentiableOn ℂ ψ (ball c r)) {x : ℂ} {δ B : ℝ}
    (hxδ : closedBall x δ ⊆ ball c r) (hM1 : ∀ z ∈ closedBall x δ, ‖deriv ψ z‖ ≤ B)
    (hM2 : ∀ z ∈ closedBall x δ, ‖deriv (deriv ψ) z‖ ≤ B) (hfd : ContDiff ℝ (⊤ : ℕ∞) f)
    (hF1 : ∀ z, ‖fderiv ℝ f z‖ ≤ B) (hF2 : ∀ z₁ z₂, ‖fderiv ℝ f z₁ - fderiv ℝ f z₂‖ ≤ B * ‖z₁ - z₂‖)
    {ε d : ℝ} (hε : 0 < ε) (hd : 0 ≤ d) {v : ℂ} (hy : x + ((ε * d : ℝ) : ℂ) * v ∈ closedBall x δ)
    (hxx : x ∈ closedBall x δ) :
    ‖fderiv ℝ (profileRest ψ f ε d x) v‖ ≤
      B * (B * ε * (d * ‖v‖) ^ 2) * (B * d) + B * (d * (B * (ε * d * ‖v‖))) := by
  have hyb : x + ((ε * d : ℝ) : ℂ) * v ∈ ball c r := hxδ hy
  have hε' : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε.ne'
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hM1 x hxx)
  have hin : HasDerivAt (fun v : ℂ => x + ((ε * d : ℝ) : ℂ) * v) ((ε * d : ℝ) : ℂ) v :=
    (((hasDerivAt_id' v).const_mul ((ε * d : ℝ) : ℂ)).const_add x).congr_deriv (mul_one _)
  have hA : HasDerivAt (fun v => (ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ))
      (-(deriv ψ (x + ((ε * d : ℝ) : ℂ) * v) * ((ε * d : ℝ) : ℂ)) / (ε : ℂ)) v :=
    (((hψ.differentiableAt (isOpen_ball.mem_nhds hyb)).hasDerivAt.comp v hin).const_sub (ψ x)).div_const _
  have hA' : HasDerivAt (fun v => (ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ))
      (-((d : ℂ) * deriv ψ (x + ((ε * d : ℝ) : ℂ) * v))) v := by
    refine hA.congr_deriv ?_
    rw [div_eq_iff hε']
    push_cast
    ring
  have hBd : HasDerivAt (fun v => -((d : ℂ) * deriv ψ x) * v) (-((d : ℂ) * deriv ψ x)) v :=
    ((hasDerivAt_id' v).const_mul (-((d : ℂ) * deriv ψ x))).congr_deriv (mul_one _)
  have hf' : Differentiable ℝ f := hfd.differentiable (by simp)
  set L₁ := fderiv ℝ f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ))
  set L₂ := fderiv ℝ f (-((d : ℂ) * deriv ψ x) * v)
  set a₁ : ℂ := -((d : ℂ) * deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)) with ha₁_def
  set a₂ : ℂ := -((d : ℂ) * deriv ψ x) with ha₂_def
  have hQ : HasFDerivAt (profileRest ψ f ε d x)
      (L₁.comp (a₁ • (1 : ℂ →L[ℝ] ℂ)) - L₂.comp (a₂ • (1 : ℂ →L[ℝ] ℂ))) v :=
    ((hf' _).hasFDerivAt.comp v hA'.complexToReal_fderiv).sub
      ((hf' _).hasFDerivAt.comp v hBd.complexToReal_fderiv)
  rw [hQ.fderiv]
  have ha₁ : ‖a₁‖ ≤ B * d := by
    rw [ha₁_def, norm_neg, norm_mul, Complex.norm_of_nonneg hd, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM1 _ hy) hd
  have ha₁₂ : ‖a₁ - a₂‖ ≤ d * (B * (ε * d * ‖v‖)) := by
    have e1 : a₁ - a₂ = (d : ℂ) * (deriv ψ x - deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)) := by
      rw [ha₁_def, ha₂_def]
      ring
    rw [e1, norm_mul, Complex.norm_of_nonneg hd]
    have := norm_deriv_sub_le hψ (convex_closedBall x δ) hxδ hM2 hxx hy
    rw [sub_add_cancel_left, norm_neg, norm_ofReal_mul _ (mul_nonneg hε.le hd)] at this
    exact mul_le_mul_of_nonneg_left this hd
  have hL : ‖L₁ - L₂‖ ≤ B * (B * ε * (d * ‖v‖) ^ 2) :=
    (hF2 _ _).trans (mul_le_mul_of_nonneg_left (norm_arg_sub_le hψ hxδ hM2 hε hd hy) hB0)
  have hnorm : ‖L₁.comp (a₁ • (1 : ℂ →L[ℝ] ℂ)) - L₂.comp (a₂ • (1 : ℂ →L[ℝ] ℂ))‖ ≤
      ‖L₁ - L₂‖ * ‖a₁‖ + ‖L₂‖ * ‖a₁ - a₂‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    have e : (L₁.comp (a₁ • (1 : ℂ →L[ℝ] ℂ)) - L₂.comp (a₂ • (1 : ℂ →L[ℝ] ℂ))) z =
        (L₁ - L₂) (a₁ * z) + L₂ ((a₁ - a₂) * z) := by
      show L₁ (a₁ * z) - L₂ (a₂ * z) = (L₁ (a₁ * z) - L₂ (a₁ * z)) + L₂ ((a₁ - a₂) * z)
      rw [sub_mul, map_sub]
      abel
    rw [e]
    calc ‖(L₁ - L₂) (a₁ * z) + L₂ ((a₁ - a₂) * z)‖
        ≤ ‖L₁ - L₂‖ * ‖a₁ * z‖ + ‖L₂‖ * ‖(a₁ - a₂) * z‖ :=
          (norm_add_le _ _).trans (add_le_add ((L₁ - L₂).le_opNorm _) (L₂.le_opNorm _))
      _ = (‖L₁ - L₂‖ * ‖a₁‖ + ‖L₂‖ * ‖a₁ - a₂‖) * ‖z‖ := by rw [norm_mul, norm_mul]; ring
  exact hnorm.trans (add_le_add (mul_le_mul hL ha₁ (norm_nonneg _) (by positivity))
    (mul_le_mul (hF1 _) ha₁₂ (norm_nonneg _) hB0))

/-! ### The profile -/

theorem profileErr_eq_zero (hf : IsMollifier f) {x : ℂ} {ε t R : ℝ} (hε : 0 < ε) (hR : 1 ≤ R) (ht : 0 ≤ t)
    (hsupp : ∀ y ∈ ball c r, ‖ψ y - ψ x‖ < ε → ‖y - x‖ < R * t) {v : ℂ} (hv : R ≤ ‖v‖) :
    profileErr c r ψ f ε x t v = 0 := by
  have hfv : f v = 0 := mollifier_eq_zero_of_one_le hf (hR.trans hv)
  have hT : transportTest c r ψ f ε (ψ x) (x + (t : ℂ) * v) = 0 := by
    unfold transportTest
    by_cases hy : x + (t : ℂ) * v ∈ ball c r
    · rw [indicator_of_mem hy]
      have hge : ε ≤ ‖ψ x - ψ (x + (t : ℂ) * v)‖ := by
        by_contra hlt'
        have hlt := not_le.1 hlt'
        rw [norm_sub_rev] at hlt
        have h1 := hsupp _ hy hlt
        rw [add_sub_cancel_left, norm_ofReal_mul _ ht] at h1
        nlinarith [mul_le_mul_of_nonneg_right hv ht]
      have h2 : 1 ≤ ‖(ψ x - ψ (x + (t : ℂ) * v)) / (ε : ℂ)‖ := by
        rw [norm_div, Complex.norm_of_nonneg hε.le, one_le_div hε]
        exact hge
      simp only [mollScale, mollifier_eq_zero_of_one_le hf h2, mul_zero, zero_mul]
    · exact indicator_of_notMem hy _
  simp only [profileErr, hT, hfv, mul_zero, sub_zero]

theorem profileErr_eq_of_mem (hf : IsMollifier f) {x : ℂ} {ε d : ℝ} (hε : 0 < ε) (hd : 0 ≤ d) {v : ℂ}
    (hy : x + ((ε * d : ℝ) : ℂ) * v ∈ ball c r) (hdψ : d * ‖deriv ψ x‖ = 1) :
    profileErr c r ψ f ε x (ε * d) v = profileMain ψ f ε d x v + profileRest ψ f ε d x v := by
  have hB : f (-((d : ℂ) * deriv ψ x) * v) = f v := by
    apply hf.radial
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_of_nonneg hd, hdψ, one_mul]
  have key : (ε * d) ^ 2 * (ε ^ 2)⁻¹ = d ^ 2 := by
    rw [mul_pow, mul_comm (ε ^ 2), mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hε.ne'), mul_one]
  simp only [profileErr, transportTest, mollScale, profileMain, profileRest, indicator_of_mem hy, hB]
  linear_combination (f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ)) *
    ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)‖ ^ 2) * key

/-- **The local profile estimate.** On a closed disc `B̄(x, δ) ⊆ B(c, r)` where `|ψ'|, |ψ''| ≤ B`, with `d |ψ'(x)| = 1`,
`t = ε d`, `(R + 1) t ≤ δ` and the support condition `|ψ y − ψ x| < ε ⇒ |y − x| < R t`, the profile `P` is smooth,
vanishes outside `B(0, R)`, and `|P|, ‖DP‖ ≤ 6 B⁹ ε`. -/
theorem profileErr_bounds (hψ : DifferentiableOn ℂ ψ (ball c r)) (hf : IsMollifier f) {x : ℂ}
    {δ ε d R B : ℝ} (hε : 0 < ε) (hB : 1 ≤ B) (hR : 1 ≤ R) (hRB : R + 1 ≤ B)
    (hxδ : closedBall x δ ⊆ ball c r) (hM1 : ∀ z ∈ closedBall x δ, ‖deriv ψ z‖ ≤ B)
    (hM2 : ∀ z ∈ closedBall x δ, ‖deriv (deriv ψ) z‖ ≤ B) (hd0 : 0 ≤ d) (hdB : d ≤ B)
    (hdψ : d * ‖deriv ψ x‖ = 1) (htδ : (R + 1) * (ε * d) ≤ δ)
    (hsupp : ∀ y ∈ ball c r, ‖ψ y - ψ x‖ < ε → ‖y - x‖ < R * (ε * d))
    (hF0 : ∀ z, |f z| ≤ B) (hF1 : ∀ z₁ z₂, |f z₁ - f z₂| ≤ B * ‖z₁ - z₂‖)
    (hF1' : ∀ z, ‖fderiv ℝ f z‖ ≤ B) (hF2 : ∀ z₁ z₂, ‖fderiv ℝ f z₁ - fderiv ℝ f z₂‖ ≤ B * ‖z₁ - z₂‖) :
    ContDiff ℝ (⊤ : ℕ∞) (profileErr c r ψ f ε x (ε * d)) ∧
      (∀ v, R ≤ ‖v‖ → profileErr c r ψ f ε x (ε * d) v = 0) ∧
      (∀ v, |profileErr c r ψ f ε x (ε * d) v| ≤ 6 * B ^ 9 * ε) ∧
      (∀ v, ‖fderiv ℝ (profileErr c r ψ f ε x (ε * d)) v‖ ≤ 6 * B ^ 9 * ε) := by
  have hB0 : 0 < B := by linarith
  have ht0 : 0 ≤ ε * d := mul_nonneg hε.le hd0
  have hδ0 : 0 ≤ δ := le_trans (by positivity) htδ
  have hxx : x ∈ closedBall x δ := mem_closedBall_self hδ0
  have h79 : B ^ 7 ≤ B ^ 9 := pow_le_pow_right₀ hB (by norm_num)
  have h69 : B ^ 6 ≤ B ^ 9 := pow_le_pow_right₀ hB (by norm_num)
  have h89 : B ^ 8 ≤ B ^ 9 := pow_le_pow_right₀ hB (by norm_num)
  have h59 : B ^ 5 ≤ B ^ 9 := pow_le_pow_right₀ hB (by norm_num)
  have hy : ∀ v : ℂ, ‖v‖ ≤ R + 1 → x + ((ε * d : ℝ) : ℂ) * v ∈ closedBall x δ := by
    intro v hv
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_ofReal_mul _ ht0]
    calc ε * d * ‖v‖ ≤ ε * d * (R + 1) := mul_le_mul_of_nonneg_left hv ht0
      _ = (R + 1) * (ε * d) := by ring
      _ ≤ δ := htδ
  have hzero : ∀ v, R ≤ ‖v‖ → profileErr c r ψ f ε x (ε * d) v = 0 :=
    fun v hv => profileErr_eq_zero hf hε hR ht0 hsupp hv
  have hPQ : ∀ v ∈ ball (0 : ℂ) (R + 1),
      profileErr c r ψ f ε x (ε * d) v = profileMain ψ f ε d x v + profileRest ψ f ε d x v := by
    intro v hv
    rw [mem_ball_zero_iff] at hv
    exact profileErr_eq_of_mem hf hε hd0 (hxδ (hy v hv.le)) hdψ
  -- the prefactor `d² |ψ'(x + t v)|²` is `1 + O(ε)`, and the argument is `−d ψ'(x) v + O(ε)`
  have ha : ∀ v : ℂ, ‖v‖ ≤ R + 1 →
      |d ^ 2 * ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)‖ ^ 2 - 1| ≤ 2 * B ^ 6 * ε := by
    intro v hv
    have hvB : ‖v‖ ≤ B := hv.trans hRB
    have e : d ^ 2 * ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)‖ ^ 2 - 1 =
        d ^ 2 * (‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)‖ ^ 2 - ‖deriv ψ x‖ ^ 2) := by
      have h1 : d ^ 2 * ‖deriv ψ x‖ ^ 2 = 1 := by rw [← mul_pow, hdψ, one_pow]
      linear_combination h1
    rw [e, abs_mul, abs_of_nonneg (sq_nonneg d)]
    have h2 := abs_sq_norm_deriv_sub_le hψ hxδ hM1 hM2 (hy v hv) hxx
    rw [add_sub_cancel_left, norm_ofReal_mul _ ht0] at h2
    calc d ^ 2 * |‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)‖ ^ 2 - ‖deriv ψ x‖ ^ 2|
        ≤ d ^ 2 * (2 * B * (B * (ε * d * ‖v‖))) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ B ^ 2 * (2 * B * (B * (ε * B * B))) := by gcongr
      _ = 2 * B ^ 6 * ε := by ring
  have hAB : ∀ v : ℂ, ‖v‖ ≤ R + 1 →
      ‖(ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ) - -((d : ℂ) * deriv ψ x) * v‖ ≤ B ^ 5 * ε := by
    intro v hv
    have hvB : ‖v‖ ≤ B := hv.trans hRB
    calc _ ≤ B * ε * (d * ‖v‖) ^ 2 := norm_arg_sub_le hψ hxδ hM2 hε hd0 (hy v hv)
      _ ≤ B * ε * (B * B) ^ 2 := by gcongr
      _ = B ^ 5 * ε := by ring
  -- smoothness
  have hψcd : ∀ y ∈ ball c r, ContDiffAt ℝ (⊤ : ℕ∞) ψ y := fun y hy =>
    ((hψ.contDiffOn isOpen_ball).restrict_scalars ℝ).contDiffAt (isOpen_ball.mem_nhds hy)
  have hψ'cd : ∀ y ∈ ball c r, ContDiffAt ℝ (⊤ : ℕ∞) (deriv ψ) y := fun y hy =>
    (((hψ.deriv isOpen_ball).contDiffOn isOpen_ball).restrict_scalars ℝ).contDiffAt (isOpen_ball.mem_nhds hy)
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℂ => x + ((ε * d : ℝ) : ℂ) * v) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  have hcdA : ∀ v ∈ ball (0 : ℂ) (R + 1),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun v => f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ))) v := by
    intro v hv
    rw [mem_ball_zero_iff] at hv
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => ψ (x + ((ε * d : ℝ) : ℂ) * v)) v := by
      have h := (hψcd _ (hxδ (hy v hv.le))).comp v hlin.contDiffAt
      exact h
    exact hf.contDiff.contDiffAt.comp v ((contDiffAt_const.sub h1).div_const _)
  have hcdMain : ∀ v ∈ ball (0 : ℂ) (R + 1), ContDiffAt ℝ (⊤ : ℕ∞) (profileMain ψ f ε d x) v := by
    intro v hv
    have hv' := hv
    rw [mem_ball_zero_iff] at hv'
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)) v := by
      have h := (hψ'cd _ (hxδ (hy v hv'.le))).comp v hlin.contDiffAt
      exact h
    have ha' : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => d ^ 2 * ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)‖ ^ 2) v :=
      contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp v h2)
    exact (ha'.sub contDiffAt_const).mul (hcdA v hv)
  have hcdRest : ∀ v ∈ ball (0 : ℂ) (R + 1), ContDiffAt ℝ (⊤ : ℕ∞) (profileRest ψ f ε d x) v := by
    intro v hv
    have hBv : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => f (-((d : ℂ) * deriv ψ x) * v)) v :=
      (hf.contDiff.comp (contDiff_const.mul contDiff_id)).contDiffAt
    exact (hcdA v hv).sub hBv
  have hev : ∀ v ∈ ball (0 : ℂ) (R + 1), profileErr c r ψ f ε x (ε * d) =ᶠ[𝓝 v]
      fun v => profileMain ψ f ε d x v + profileRest ψ f ε d x v :=
    fun v hv => Filter.eventually_of_mem (isOpen_ball.mem_nhds hv) hPQ
  have hout : ∀ v : ℂ, R + 1 ≤ ‖v‖ → profileErr c r ψ f ε x (ε * d) =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
    intro v hv
    have hopen : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds (show R < ‖v‖ by linarith)] with z hz
    exact hzero z (le_of_lt hz)
  refine ⟨?_, hzero, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : ‖v‖ < R + 1
    · have hvb : v ∈ ball (0 : ℂ) (R + 1) := mem_ball_zero_iff.2 hv
      exact ((hcdMain v hvb).add (hcdRest v hvb)).congr_of_eventuallyEq (hev v hvb)
    · exact contDiffAt_const.congr_of_eventuallyEq (hout v (not_lt.1 hv))
  · intro v
    by_cases hv : ‖v‖ < R + 1
    · rw [hPQ v (mem_ball_zero_iff.2 hv)]
      simp only [profileMain, profileRest]
      have h1 := ha v hv.le
      have h2 := hAB v hv.le
      calc |(d ^ 2 * ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)‖ ^ 2 - 1) *
              f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ)) +
            (f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ)) - f (-((d : ℂ) * deriv ψ x) * v))|
          ≤ |d ^ 2 * ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v)‖ ^ 2 - 1| *
              |f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ))| +
            |f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v)) / (ε : ℂ)) - f (-((d : ℂ) * deriv ψ x) * v)| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ 2 * B ^ 6 * ε * B + B * (B ^ 5 * ε) :=
            add_le_add (mul_le_mul h1 (hF0 _) (abs_nonneg _) (by positivity))
              ((hF1 _ _).trans (mul_le_mul_of_nonneg_left h2 hB0.le))
        _ ≤ 6 * B ^ 9 * ε := by
            nlinarith [mul_le_mul_of_nonneg_right h79 hε.le, mul_le_mul_of_nonneg_right h69 hε.le,
              mul_pos (pow_pos hB0 9) hε]
    · rw [hzero v (by linarith [not_lt.1 hv]), abs_zero]
      positivity
  · intro v
    by_cases hv : ‖v‖ < R + 1
    · have hvb : v ∈ ball (0 : ℂ) (R + 1) := mem_ball_zero_iff.2 hv
      have hvB : ‖v‖ ≤ B := hv.le.trans hRB
      rw [(hev v hvb).fderiv_eq, fderiv_fun_add ((hcdMain v hvb).differentiableAt (by simp))
        ((hcdRest v hvb).differentiableAt (by simp))]
      -- the main part is Lipschitz with constant `4 B⁹ ε` on `B(0, R + 1)`
      have hlip : LipschitzOnWith (Real.toNNReal (4 * B ^ 9 * ε)) (profileMain ψ f ε d x)
          (ball (0 : ℂ) (R + 1)) := by
        apply LipschitzOnWith.of_dist_le'
        intro v₁ h₁ v₂ h₂
        rw [mem_ball_zero_iff] at h₁ h₂
        rw [Real.dist_eq, dist_eq_norm]
        have hy₁ := hy v₁ h₁.le
        have hy₂ := hy v₂ h₂.le
        have ha₁ := ha v₁ h₁.le
        have hA₁₂ := norm_arg_sub_arg_le hψ hxδ hM1 hε hd0 hy₁ hy₂
        have ha₁₂ : |d ^ 2 * ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v₁)‖ ^ 2 -
            d ^ 2 * ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v₂)‖ ^ 2| ≤ 2 * B ^ 5 * ε * ‖v₁ - v₂‖ := by
          rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg d)]
          have h3 := abs_sq_norm_deriv_sub_le hψ hxδ hM1 hM2 hy₁ hy₂
          have e3 : x + ((ε * d : ℝ) : ℂ) * v₁ - (x + ((ε * d : ℝ) : ℂ) * v₂) =
              ((ε * d : ℝ) : ℂ) * (v₁ - v₂) := by ring
          rw [e3, norm_ofReal_mul _ ht0] at h3
          calc d ^ 2 * |‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v₁)‖ ^ 2 -
                ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v₂)‖ ^ 2|
              ≤ d ^ 2 * (2 * B * (B * (ε * d * ‖v₁ - v₂‖))) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ ≤ B ^ 2 * (2 * B * (B * (ε * B * ‖v₁ - v₂‖))) := by gcongr
            _ = 2 * B ^ 5 * ε * ‖v₁ - v₂‖ := by ring
        simp only [profileMain]
        set a₁ := d ^ 2 * ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v₁)‖ ^ 2
        set a₂ := d ^ 2 * ‖deriv ψ (x + ((ε * d : ℝ) : ℂ) * v₂)‖ ^ 2
        set F₁ := f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v₁)) / (ε : ℂ))
        set F₂ := f ((ψ x - ψ (x + ((ε * d : ℝ) : ℂ) * v₂)) / (ε : ℂ))
        have hF₁₂ : |F₁ - F₂| ≤ B * (B * d * ‖v₁ - v₂‖) :=
          (hF1 _ _).trans (mul_le_mul_of_nonneg_left hA₁₂ hB0.le)
        have e4 : (a₁ - 1) * F₁ - (a₂ - 1) * F₂ = (a₁ - 1) * (F₁ - F₂) + F₂ * (a₁ - a₂) := by ring
        rw [e4]
        calc |(a₁ - 1) * (F₁ - F₂) + F₂ * (a₁ - a₂)| ≤ |a₁ - 1| * |F₁ - F₂| + |F₂| * |a₁ - a₂| := by
              rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ 2 * B ^ 6 * ε * (B * (B * d * ‖v₁ - v₂‖)) + B * (2 * B ^ 5 * ε * ‖v₁ - v₂‖) :=
              add_le_add (mul_le_mul ha₁ hF₁₂ (abs_nonneg _) (by positivity))
                (mul_le_mul (hF0 _) ha₁₂ (abs_nonneg _) hB0.le)
          _ ≤ 2 * B ^ 6 * ε * (B * (B * B * ‖v₁ - v₂‖)) + B * (2 * B ^ 5 * ε * ‖v₁ - v₂‖) := by gcongr
          _ = (2 * B ^ 9 + 2 * B ^ 6) * ε * ‖v₁ - v₂‖ := by ring
          _ ≤ 4 * B ^ 9 * ε * ‖v₁ - v₂‖ := by
              have : 0 ≤ ε * ‖v₁ - v₂‖ := by positivity
              nlinarith [mul_le_mul_of_nonneg_right h69 this, mul_nonneg (pow_pos hB0 9).le this]
      have h1 := norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hvb) hlip
      have h49 : 0 ≤ 4 * B ^ 9 * ε := by positivity
      rw [Real.coe_toNNReal', max_eq_left h49] at h1
      have h2 := norm_fderiv_profileRest_le hψ hxδ hM1 hM2 hf.contDiff hF1' hF2 hε hd0 (hy v hv.le) hxx
      have h3 : B * (B * ε * (d * ‖v‖) ^ 2) * (B * d) + B * (d * (B * (ε * d * ‖v‖))) ≤
          B * (B * ε * (B * B) ^ 2) * (B * B) + B * (B * (B * (ε * B * B))) := by gcongr
      calc ‖fderiv ℝ (profileMain ψ f ε d x) v + fderiv ℝ (profileRest ψ f ε d x) v‖
          ≤ ‖fderiv ℝ (profileMain ψ f ε d x) v‖ + ‖fderiv ℝ (profileRest ψ f ε d x) v‖ := norm_add_le _ _
        _ ≤ 4 * B ^ 9 * ε + (B * (B * ε * (B * B) ^ 2) * (B * B) + B * (B * (B * (ε * B * B)))) :=
            add_le_add h1 (h2.trans h3)
        _ ≤ 6 * B ^ 9 * ε := by
            nlinarith [mul_le_mul_of_nonneg_right h89 hε.le, mul_le_mul_of_nonneg_right h59 hε.le,
              mul_pos (pow_pos hB0 9) hε]
    · rw [(hout v (not_lt.1 hv)).fderiv_eq, fderiv_const_apply, norm_zero]
      positivity

/-! ### The profile estimate, uniformly on compact sets -/

/-- **The transported test is the dilated bump plus a rescaled error profile**: for `t > 0`,
`T = f_t(x − ·) + t⁻² P((· − x)/t)` with `T = transportTest c r ψ f ε (ψ x)` and `P = profileErr c r ψ f ε x t`. -/
theorem transportTest_eq_add (hf : IsMollifier f) {x : ℂ} {ε t : ℝ} (ht : 0 < t) :
    transportTest c r ψ f ε (ψ x) = (fun y => mollScale f t (x - y)) +
      fun y => (t ^ 2)⁻¹ * profileErr c r ψ f ε x t ((y - x) / (t : ℂ)) := by
  funext y
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hy : x + (t : ℂ) * ((y - x) / (t : ℂ)) = y := by rw [mul_div_assoc', mul_div_cancel_left₀ _ ht']; ring
  have hrad : f ((x - y) / (t : ℂ)) = f ((y - x) / (t : ℂ)) := by
    apply hf.radial
    rw [← neg_sub, neg_div, norm_neg]
  have ht0 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht.ne'
  simp only [Pi.add_apply, profileErr, hy, mollScale, hrad]
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
  ring

end Straighten

end LQGMeasureChart

section

variable {c : ℂ} {r : ℝ} {ψ : ℂ → ℂ} {f : ℂ → ℝ}

open LQGMeasureChart LQGMeasureChart.Straighten

/-- **The profile estimate** (Taylor expansion of the transported bump, uniformly on compact sets). For `ψ` injective
and holomorphic on `B(c, r)`, a bump function `f` and a compact set `K' ⊆ ψ(B(c, r))`, there are `R ≥ 1`, `A > 0`,
`B ≥ 1` and `ε₀ > 0` such that for `w ∈ K'`, `0 < ε ≤ ε₀`, `x = φ(w)` and `d = |φ'(w)|` (`φ = ψ⁻¹`):
`x ∈ B(c, r)`, `ψ(x) = w`, `B⁻¹ ≤ d ≤ B`, `B̄(x, (R + 1) ε d) ⊆ B(c, r)`, and the profile
`P = profileErr c r ψ f ε x (ε d)` is smooth, vanishes outside `B(0, R)`, and satisfies `|P| ≤ A ε` and
`‖DP‖ ≤ A ε`. -/
theorem exists_profileErr_bounds (hψ : DifferentiableOn ℂ ψ (ball c r)) (hinj : InjOn ψ (ball c r))
    (hf : IsMollifier f) {K' : Set ℂ} (hK' : IsCompact K') (hK'W : K' ⊆ ψ '' ball c r) :
    ∃ R A B ε₀ : ℝ, 1 ≤ R ∧ 0 < A ∧ 1 ≤ B ∧ 0 < ε₀ ∧ ∀ w ∈ K', ∀ ε ∈ Ioc 0 ε₀, ∀ (x : ℂ) (d : ℝ),
      x = Function.invFunOn ψ (ball c r) w → d = ‖deriv (Function.invFunOn ψ (ball c r)) w‖ →
      x ∈ ball c r ∧ ψ x = w ∧ B⁻¹ ≤ d ∧ d ≤ B ∧ closedBall x ((R + 1) * (ε * d)) ⊆ ball c r ∧
      ContDiff ℝ (⊤ : ℕ∞) (profileErr c r ψ f ε x (ε * d)) ∧
      (∀ v, R ≤ ‖v‖ → profileErr c r ψ f ε x (ε * d) v = 0) ∧
      (∀ v, |profileErr c r ψ f ε x (ε * d) v| ≤ A * ε) ∧
      ∀ v, ‖fderiv ℝ (profileErr c r ψ f ε x (ε * d)) v‖ ≤ A * ε := by
  have hW := isOpen_image hψ hinj
  obtain ⟨δ', hδ', hδ'W⟩ := hK'.exists_cthickening_subset_open hW hK'W
  have hL' : IsCompact (cthickening δ' K') := hK'.cthickening
  have hφc : ContinuousOn (Function.invFunOn ψ (ball c r)) (ψ '' ball c r) :=
    (differentiableOn_invFunOn hψ hinj).continuousOn
  set K := Function.invFunOn ψ (ball c r) '' cthickening δ' K' with hK_def
  have hK : IsCompact K := hL'.image_of_continuousOn (hφc.mono hδ'W)
  have hKb : K ⊆ ball c r := by
    rintro _ ⟨w, hw, rfl⟩
    exact invFunOn_mem (hδ'W hw)
  obtain ⟨δ, hδ, hδb⟩ := hK.exists_cthickening_subset_open isOpen_ball hKb
  have hL : IsCompact (cthickening δ K) := hK.cthickening
  have hd1 : DifferentiableOn ℂ (deriv ψ) (ball c r) := hψ.deriv isOpen_ball
  have hd2 : DifferentiableOn ℂ (deriv (deriv ψ)) (ball c r) := hd1.deriv isOpen_ball
  obtain ⟨B1, hB1⟩ := hL.exists_bound_of_continuousOn (hd1.continuousOn.mono hδb)
  obtain ⟨B2, hB2⟩ := hL.exists_bound_of_continuousOn (hd2.continuousOn.mono hδb)
  obtain ⟨B0, hB0⟩ := hL.exists_bound_of_continuousOn
    ((hd1.continuousOn.inv₀ fun z hz => deriv_ne_zero hψ hinj hz).mono hδb)
  obtain ⟨Bf, -, hF0, hF1, hF1', hF2⟩ := mollifier_exists_bound hf
  set B0' := max B0 0 with hB0'_def
  set B1' := max B1 1 with hB1'_def
  set R := B0' * B1' + 1 with hR_def
  set B := max (R + 1) (max Bf (max B0' (max B1' B2))) with hB_def
  have hB0'0 : 0 ≤ B0' := le_max_right _ _
  have hB1'1 : 1 ≤ B1' := le_max_right _ _
  have hR1 : 1 ≤ R := by
    have : 0 ≤ B0' * B1' := mul_nonneg hB0'0 (by linarith)
    linarith
  have hRB : R + 1 ≤ B := le_max_left _ _
  have hBfB : Bf ≤ B := le_max_of_le_right (le_max_left _ _)
  have hB0B : B0' ≤ B := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hB1B : B1' ≤ B := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hB2B : B2 ≤ B := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
  have hBone : 1 ≤ B := by linarith
  have hBpos : 0 < B := by linarith
  refine ⟨R, 6 * B ^ 9, B, min δ' (δ / (B * B)), hR1, by positivity, hBone,
    lt_min hδ' (by positivity), ?_⟩
  intro w hw ε hε x d hx hd
  have hεpos : 0 < ε := hε.1
  have hεδ' : ε ≤ δ' := hε.2.trans (min_le_left _ _)
  have hεδ : ε ≤ δ / (B * B) := hε.2.trans (min_le_right _ _)
  have hwW : w ∈ ψ '' ball c r := hK'W hw
  have hxb : x ∈ ball c r := by rw [hx]; exact invFunOn_mem hwW
  have hψx : ψ x = w := by rw [hx]; exact apply_invFunOn hwW
  have hxK : x ∈ K := ⟨w, self_subset_cthickening _ hw, hx.symm⟩
  have hxL : closedBall x δ ⊆ cthickening δ K := closedBall_subset_cthickening hxK δ
  have hxL' : x ∈ cthickening δ K := hxL (mem_closedBall_self hδ.le)
  have hψ'x0 : deriv ψ x ≠ 0 := deriv_ne_zero hψ hinj hxb
  have hnpos : 0 < ‖deriv ψ x‖ := norm_pos_iff.2 hψ'x0
  have hdeq : d = ‖deriv ψ x‖⁻¹ := by rw [hd, norm_deriv_invFunOn hψ hinj hwW, ← hx]
  have hdpos : 0 < d := by rw [hdeq]; positivity
  have hdψ : d * ‖deriv ψ x‖ = 1 := by rw [hdeq, inv_mul_cancel₀ hnpos.ne']
  have hψ'xB : ‖deriv ψ x‖ ≤ B1' := (hB1 x hxL').trans (le_max_left _ _)
  have hdB0 : d ≤ B0' := by
    have := hB0 x hxL'
    simp only [Pi.inv_apply, norm_inv] at this
    rw [hdeq]
    exact this.trans (le_max_left _ _)
  have hdB : d ≤ B := hdB0.trans hB0B
  have hBinv : B⁻¹ ≤ d := by
    rw [hdeq]
    exact inv_anti₀ hnpos (hψ'xB.trans hB1B)
  have hB1d : 1 ≤ B1' * d := by
    rw [← hdψ, mul_comm d]
    exact mul_le_mul_of_nonneg_right hψ'xB hdpos.le
  have htδ : (R + 1) * (ε * d) ≤ δ := by
    calc (R + 1) * (ε * d) ≤ B * (ε * B) := by gcongr
      _ = ε * (B * B) := by ring
      _ ≤ δ / (B * B) * (B * B) := by gcongr
      _ = δ := div_mul_cancel₀ _ (by positivity)
  have hsupp : ∀ y ∈ ball c r, ‖ψ y - ψ x‖ < ε → ‖y - x‖ < R * (ε * d) := by
    intro y hy hlt
    rw [hψx] at hlt
    have hsub : closedBall w δ' ⊆ cthickening δ' K' := closedBall_subset_cthickening hw δ'
    have hψyB : ψ y ∈ closedBall w δ' := by
      rw [mem_closedBall, dist_eq_norm]
      linarith
    have hbound : ∀ z ∈ closedBall w δ', ‖deriv (Function.invFunOn ψ (ball c r)) z‖ ≤ B0 := by
      intro z hz
      have hzW : z ∈ ψ '' ball c r := hδ'W (hsub hz)
      rw [norm_deriv_invFunOn hψ hinj hzW, ← norm_inv]
      exact hB0 _ (self_subset_cthickening _ ⟨z, hsub hz, rfl⟩)
    have hmvt := (convex_closedBall w δ').norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hasDerivAt_invFunOn hψ hinj (hδ'W (hsub hz))).differentiableAt) hbound
      (mem_closedBall_self hδ'.le) hψyB
    rw [invFunOn_apply hinj hy, ← hx] at hmvt
    have hεd : 0 < ε * d := by positivity
    have h4 : B0' * ε ≤ B0' * ε * (B1' * d) := le_mul_of_one_le_right (by positivity) hB1d
    calc ‖y - x‖ ≤ B0 * ‖ψ y - w‖ := hmvt
      _ ≤ B0' * ‖ψ y - w‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ B0' * ε := mul_le_mul_of_nonneg_left hlt.le hB0'0
      _ < B0' * ε * (B1' * d) + ε * d := by linarith
      _ = R * (ε * d) := by rw [hR_def]; ring
  have hM1 : ∀ z ∈ closedBall x δ, ‖deriv ψ z‖ ≤ B :=
    fun z hz => ((hB1 z (hxL hz)).trans (le_max_left _ _)).trans hB1B
  have hM2 : ∀ z ∈ closedBall x δ, ‖deriv (deriv ψ) z‖ ≤ B := fun z hz => (hB2 z (hxL hz)).trans hB2B
  obtain ⟨h1, h2, h3, h4⟩ := profileErr_bounds hψ hf hεpos hBone hR1 hRB (hxL.trans hδb) hM1 hM2 hdpos.le hdB
    hdψ htδ hsupp (fun z => (hF0 z).trans hBfB)
    (fun z₁ z₂ => (hF1 z₁ z₂).trans (mul_le_mul_of_nonneg_right hBfB (norm_nonneg _)))
    (fun z => (hF1' z).trans hBfB)
    (fun z₁ z₂ => (hF2 z₁ z₂).trans (mul_le_mul_of_nonneg_right hBfB (norm_nonneg _)))
  exact ⟨hxb, hψx, hBinv, hdB, (closedBall_subset_closedBall htδ).trans (hxL.trans hδb), h1, h2, h3, h4⟩

end

end MatedCRT
