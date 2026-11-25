import MatedCRT.FirstPass.Derived.WindowDiscMapBorel
import LatticeProb.Topology.MeasurableCurveComponent

/-!
# Normalized conformal maps of the open disc onto a window domain

For times `a, u, b` and a curve `η`, the window domain `U = windowDomain η a u b` is the component at `η(u)` of the
interior of `η([a, b])`. A conformal map of the open unit disc onto `U` (`IsOpenDiscMap U φ`: holomorphic and
injective on the open disc, with image `U`) is unique up to a rotation of the disc once `φ(0)` is fixed (Schwarz
lemma), and unique once moreover `φ'(0) > 0` (`IsNormalizedOpenDiscMap`). No boundary behaviour is required: this is
the conformal structure of `U` alone, which is what an intrinsic re-embedding of the curve-decorated quantum surface
carries (Gwynne–Miller, arXiv:1701.05174, Definition 2.1).

The map is encoded by the continuous map `Φ = φ ∘ planeToDisc` of the plane, where `planeToDisc x = x / (1 + |x|)` is
a homeomorphism of `ℂ` onto the open disc with inverse `discToPlane w = w / (1 - |w|)`. The pairs `(η, Φ)` with
`Φ ∘ discToPlane` the normalized conformal map of the window form a Borel set (`measurableSet_openWindowDiscMapGraph`):
injectivity of `Φ` is `G_δ`, holomorphy with `φ'(0) ∈ [0, ∞)` is closed, the image is contained in `U` iff `Φ` takes
values in `η([a, b])` (an open connected subset of `η([a, b])` through `η(u)` lies in `U`), and it contains `U` iff each
rational closed disc contained in `U` is covered by the image of a closed disc of integer radius. The choice
`openWindowDiscCode` is Borel (`measurable_graphChoice`), and so is the inverse map (`invCode`).

## Main statements

* `IsOpenDiscMap.exists_rotation`, `IsNormalizedOpenDiscMap.eqOn`.
* `measurableSet_openWindowDiscMapGraph`, `measurable_openWindowDiscCode`,
  `isNormalizedOpenDiscMap_openWindowDiscMap`.
* `invCode`, `measurable_invCode`.
-/

set_option autoImplicit false

open Set Metric Filter Topology MeasureTheory Function

namespace MatedCRT

/-! ### Conformal maps of the open disc -/

/-- `φ` is a conformal map of the open unit disc onto `U`: holomorphic and injective on the open disc, with image
`U`. -/
structure IsOpenDiscMap (U : Set ℂ) (φ : ℂ → ℂ) : Prop where
  differentiableOn : DifferentiableOn ℂ φ (ball 0 1)
  injOn : InjOn φ (ball 0 1)
  image_ball : φ '' ball 0 1 = U

namespace IsOpenDiscMap

variable {U : Set ℂ} {φ : ℂ → ℂ}

theorem isOpen (h : IsOpenDiscMap U φ) : IsOpen U := by
  rw [← h.image_ball]
  exact QuantumZipper.CA.isOpen_image_of_injOn' isOpen_ball h.differentiableOn h.injOn

theorem apply_mem (h : IsOpenDiscMap U φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : φ w ∈ U :=
  h.image_ball ▸ mem_image_of_mem φ hw

theorem continuousOn (h : IsOpenDiscMap U φ) : ContinuousOn φ (ball 0 1) :=
  h.differentiableOn.continuousOn

/-- A conformal map has non-vanishing derivative on the open disc. -/
theorem deriv_ne_zero (h : IsOpenDiscMap U φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : deriv φ w ≠ 0 :=
  QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball h.differentiableOn h.injOn hw

/-- Precomposing a conformal map with a rotation gives a conformal map. -/
theorem comp_mul (h : IsOpenDiscMap U φ) {c : ℂ} (hc : ‖c‖ = 1) : IsOpenDiscMap U (fun w => φ (c * w)) := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  have hmapsb : MapsTo (fun w => c * w) (ball (0 : ℂ) 1) (ball 0 1) := fun w hw => by
    rw [mem_ball_zero_iff, norm_mul, hc, one_mul]
    exact mem_ball_zero_iff.1 hw
  refine ⟨h.differentiableOn.comp (differentiable_id.const_mul c).differentiableOn hmapsb,
    fun w hw w' hw' hww => mul_left_cancel₀ hc0 (h.injOn (hmapsb hw) (hmapsb hw') hww), ?_⟩
  show (φ ∘ fun w => c * w) '' ball 0 1 = U
  rw [image_comp, image_mul_eq_of_norm_eq_one hc (fun r => r < 1) (fun w => mem_ball_zero_iff), h.image_ball]

/-- The derivative at `0` of a conformal map precomposed with `w ↦ c w`. -/
theorem hasDerivAt_comp_mul (h : IsOpenDiscMap U φ) (c : ℂ) :
    HasDerivAt (fun w => φ (c * w)) (deriv φ 0 * c) 0 := by
  have hd : HasDerivAt φ (deriv φ (c * 0)) (c * 0) := by
    rw [mul_zero]
    exact (h.differentiableOn.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))).hasDerivAt
  have := hd.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul c)
  simpa only [mul_zero, mul_one, Function.comp_def, id_eq] using this

/-- **Normalization of the derivative.** Precomposing a conformal map with a rotation gives a conformal map whose
derivative at `0` is a positive real number. -/
theorem exists_normalized (h : IsOpenDiscMap U φ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ IsOpenDiscMap U (fun w => φ (c * w)) ∧ 0 < (deriv (fun w => φ (c * w)) 0).re ∧
      (deriv (fun w => φ (c * w)) 0).im = 0 := by
  have hd0 : deriv φ 0 ≠ 0 := h.deriv_ne_zero (mem_ball_self one_pos)
  have hc : ‖((‖deriv φ 0‖ : ℂ) / deriv φ 0)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hd0)]
  have hderiv : deriv (fun w => φ (((‖deriv φ 0‖ : ℂ) / deriv φ 0) * w)) 0 = (‖deriv φ 0‖ : ℂ) := by
    rw [(h.hasDerivAt_comp_mul _).deriv, mul_comm, div_mul_cancel₀ _ hd0]
  refine ⟨_, hc, h.comp_mul hc, ?_, ?_⟩
  · rw [hderiv, Complex.ofReal_re]
    exact norm_pos_iff.2 hd0
  · rw [hderiv, Complex.ofReal_im]

/-- **Two conformal maps of the disc onto the same set with the same value at `0` differ by a rotation of the disc**
(Schwarz lemma: the conformal automorphisms of the disc fixing `0` are the rotations). -/
theorem exists_rotation {φ₁ φ₂ : ℂ → ℂ} (h₁ : IsOpenDiscMap U φ₁) (h₂ : IsOpenDiscMap U φ₂) (h0 : φ₁ 0 = φ₂ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ w ∈ ball (0 : ℂ) 1, φ₁ w = φ₂ (c * w) := by
  set e := QuantumZipper.CA.univalentOPH isOpen_ball h₂.differentiableOn h₂.injOn
  have htarget : ∀ w ∈ ball (0 : ℂ) 1, φ₁ w ∈ φ₂ '' ball 0 1 := fun w hw => by
    rw [h₂.image_ball, ← h₁.image_ball]
    exact mem_image_of_mem φ₁ hw
  have hφ₂f : ∀ w ∈ ball (0 : ℂ) 1, φ₂ (e.symm (φ₁ w)) = φ₁ w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply isOpen_ball h₂.differentiableOn h₂.injOn (htarget w hw)
  have hfball : ∀ w ∈ ball (0 : ℂ) 1, e.symm (φ₁ w) ∈ ball (0 : ℂ) 1 := fun w hw =>
    e.map_target (htarget w hw)
  have hfd : DifferentiableOn ℂ (fun w => e.symm (φ₁ w)) (ball 0 1) :=
    (QuantumZipper.CA.differentiableOn_univalentOPH_symm isOpen_ball h₂.differentiableOn h₂.injOn).comp
      h₁.differentiableOn htarget
  have hbij : BijOn (fun w => e.symm (φ₁ w)) (ball 0 1) (ball 0 1) := by
    refine ⟨hfball, fun w hw w' hw' hww => ?_, fun v hv => ?_⟩
    · have h2 : φ₂ (e.symm (φ₁ w)) = φ₂ (e.symm (φ₁ w')) := congrArg φ₂ hww
      rw [hφ₂f w hw, hφ₂f w' hw'] at h2
      exact h₁.injOn hw hw' h2
    · have hv' : φ₂ v ∈ φ₁ '' ball 0 1 := by
        rw [h₁.image_ball, ← h₂.image_ball]
        exact mem_image_of_mem φ₂ hv
      obtain ⟨w, hw, hwv⟩ := hv'
      refine ⟨w, hw, ?_⟩
      show e.symm (φ₁ w) = v
      rw [hwv]
      exact QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball h₂.differentiableOn h₂.injOn hv
  have hf0 : e.symm (φ₁ 0) = 0 := by
    rw [h0]
    exact QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball h₂.differentiableOn h₂.injOn
      (mem_ball_self one_pos)
  obtain ⟨c, hc, hrot⟩ := QuantumZipper.CA.exists_rotation_of_bijOn_ball hfd hbij hf0
  refine ⟨c, hc, fun w hw => ?_⟩
  have h1 : e.symm (φ₁ w) = c * w := hrot hw
  rw [← h1, hφ₂f w hw]

end IsOpenDiscMap

/-- `φ` is the normalized conformal map of the open disc onto `U` at `z`: `φ 0 = z` and `φ'(0)` is a positive real
number. -/
structure IsNormalizedOpenDiscMap (U : Set ℂ) (z : ℂ) (φ : ℂ → ℂ) : Prop where
  isOpenDiscMap : IsOpenDiscMap U φ
  apply_zero : φ 0 = z
  deriv_re_pos : 0 < (deriv φ 0).re
  deriv_im : (deriv φ 0).im = 0

/-- **Uniqueness of the normalized conformal map of the open disc.** -/
theorem IsNormalizedOpenDiscMap.eqOn {U : Set ℂ} {z : ℂ} {φ₁ φ₂ : ℂ → ℂ} (h₁ : IsNormalizedOpenDiscMap U z φ₁)
    (h₂ : IsNormalizedOpenDiscMap U z φ₂) : EqOn φ₁ φ₂ (ball 0 1) := by
  obtain ⟨c, hc, hφ₁⟩ :=
    h₁.isOpenDiscMap.exists_rotation h₂.isOpenDiscMap (h₁.apply_zero.trans h₂.apply_zero.symm)
  have hev : φ₁ =ᶠ[𝓝 0] fun w => φ₂ (c * w) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) hφ₁
  have hd : deriv φ₁ 0 = deriv φ₂ 0 * c := by
    rw [hev.deriv_eq]
    exact (h₂.isOpenDiscMap.hasDerivAt_comp_mul c).deriv
  obtain ⟨r₁, hr₁'⟩ : ∃ r : ℝ, deriv φ₁ 0 = r :=
    ⟨(deriv φ₁ 0).re, Complex.ext (by simp) (by simp [h₁.deriv_im])⟩
  obtain ⟨r₂, hr₂'⟩ : ∃ r : ℝ, deriv φ₂ 0 = r :=
    ⟨(deriv φ₂ 0).re, Complex.ext (by simp) (by simp [h₂.deriv_im])⟩
  have hr₁ := h₁.deriv_re_pos
  have hr₂ := h₂.deriv_re_pos
  rw [hr₁', Complex.ofReal_re] at hr₁
  rw [hr₂', Complex.ofReal_re] at hr₂
  rw [hr₁', hr₂'] at hd
  have hn : ‖(r₁ : ℂ)‖ = ‖(r₂ : ℂ) * c‖ := by rw [hd]
  rw [norm_mul, hc, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr₁.le,
    Real.norm_of_nonneg hr₂.le] at hn
  rw [hn] at hd
  have hr0 : (r₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr₂.ne'
  have hc1 : c = 1 := mul_left_cancel₀ hr0 (hd.symm.trans (mul_one _).symm)
  subst hc1
  intro w hw
  rw [hφ₁ w hw, one_mul]

/-- A map agreeing on the open disc with a normalized conformal map is a normalized conformal map. -/
theorem IsNormalizedOpenDiscMap.congr {U : Set ℂ} {z : ℂ} {φ φ' : ℂ → ℂ} (h : IsNormalizedOpenDiscMap U z φ)
    (hE : EqOn φ φ' (ball 0 1)) : IsNormalizedOpenDiscMap U z φ' := by
  have hev : φ' =ᶠ[𝓝 0] φ :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) fun w hw => (hE hw).symm
  refine ⟨⟨h.isOpenDiscMap.differentiableOn.congr fun w hw => (hE hw).symm, h.isOpenDiscMap.injOn.congr hE, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [← hE.image_eq]
    exact h.isOpenDiscMap.image_ball
  · rw [← hE (mem_ball_self one_pos)]
    exact h.apply_zero
  · rw [hev.deriv_eq]
    exact h.deriv_re_pos
  · rw [hev.deriv_eq]
    exact h.deriv_im

/-- Every conformal map of the open disc onto `U` is a rotation of the normalized one at its value at `0`. -/
theorem IsOpenDiscMap.exists_isNormalizedOpenDiscMap {U : Set ℂ} {φ : ℂ → ℂ} (h : IsOpenDiscMap U φ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ IsNormalizedOpenDiscMap U (φ 0) (fun w => φ (c * w)) := by
  obtain ⟨c, hc, hO, hre, him⟩ := h.exists_normalized
  exact ⟨c, hc, hO, by simp only [mul_zero], hre, him⟩

/-- A conformal map of the closed disc is a conformal map of the open disc. -/
theorem IsDiscMap.isOpenDiscMap {U : Set ℂ} {φ : ℂ → ℂ} (h : IsDiscMap U φ) : IsOpenDiscMap U φ :=
  ⟨h.differentiableOn, h.injOn.mono ball_subset_closedBall, h.image_ball⟩

theorem IsNormalizedDiscMap.isNormalizedOpenDiscMap {U : Set ℂ} {z : ℂ} {φ : ℂ → ℂ}
    (h : IsNormalizedDiscMap U z φ) : IsNormalizedOpenDiscMap U z φ :=
  ⟨h.isDiscMap.isOpenDiscMap, h.apply_zero, h.deriv_re_pos, h.deriv_im⟩

/-! ### The plane as the open disc -/

/-- The homeomorphism `x ↦ x / (1 + |x|)` of `ℂ` onto the open unit disc. -/
noncomputable def planeToDisc : C(ℂ, ℂ) :=
  ⟨fun x => (1 + ‖x‖)⁻¹ • x, ((continuous_const.add continuous_norm).inv₀ fun x =>
    (add_pos_of_pos_of_nonneg one_pos (norm_nonneg x)).ne').smul continuous_id⟩

/-- The inverse of `planeToDisc` on the open disc, `w ↦ w / (1 - |w|)`. -/
noncomputable def discToPlane (w : ℂ) : ℂ :=
  (1 - ‖w‖)⁻¹ • w

theorem planeToDisc_apply (x : ℂ) : planeToDisc x = (1 + ‖x‖)⁻¹ • x :=
  rfl

theorem norm_planeToDisc (x : ℂ) : ‖planeToDisc x‖ = ‖x‖ / (1 + ‖x‖) := by
  have hpos : 0 < 1 + ‖x‖ := add_pos_of_pos_of_nonneg one_pos (norm_nonneg x)
  rw [planeToDisc_apply, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_eq_div]

theorem planeToDisc_mem_ball (x : ℂ) : planeToDisc x ∈ ball (0 : ℂ) 1 := by
  have hpos : 0 < 1 + ‖x‖ := add_pos_of_pos_of_nonneg one_pos (norm_nonneg x)
  rw [mem_ball_zero_iff, norm_planeToDisc, div_lt_one hpos]
  linarith

theorem discToPlane_planeToDisc (x : ℂ) : discToPlane (planeToDisc x) = x := by
  have hpos : 0 < 1 + ‖x‖ := add_pos_of_pos_of_nonneg one_pos (norm_nonneg x)
  have h1 : 1 - ‖planeToDisc x‖ = (1 + ‖x‖)⁻¹ := by
    rw [norm_planeToDisc, one_sub_div hpos.ne', add_sub_cancel_right, one_div]
  rw [discToPlane, h1, planeToDisc_apply, smul_smul, inv_inv, mul_inv_cancel₀ hpos.ne', one_smul]

theorem planeToDisc_discToPlane {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : planeToDisc (discToPlane w) = w := by
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have hpos : 0 < 1 - ‖w‖ := sub_pos.2 hw'
  have hn : ‖discToPlane w‖ = ‖w‖ / (1 - ‖w‖) := by
    rw [discToPlane, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_eq_div]
  have h1 : 1 + ‖discToPlane w‖ = (1 - ‖w‖)⁻¹ := by
    rw [hn, one_add_div hpos.ne', sub_add_cancel, one_div]
  rw [planeToDisc_apply, h1, inv_inv, discToPlane, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

theorem discToPlane_zero : discToPlane 0 = 0 := by
  simp [discToPlane]

theorem continuousOn_discToPlane : ContinuousOn discToPlane (ball 0 1) :=
  ((continuous_const.sub continuous_norm).continuousOn.inv₀ fun _ hw =>
    (sub_pos.2 (mem_ball_zero_iff.1 hw)).ne').smul continuousOn_id

theorem image_comp_discToPlane (Φ : ℂ → ℂ) : (Φ ∘ discToPlane) '' ball 0 1 = range Φ := by
  ext y
  constructor
  · rintro ⟨w, -, rfl⟩
    exact mem_range_self _
  · rintro ⟨x, rfl⟩
    exact ⟨planeToDisc x, planeToDisc_mem_ball x, by rw [Function.comp_apply, discToPlane_planeToDisc]⟩

theorem injOn_comp_discToPlane_iff (Φ : ℂ → ℂ) : InjOn (Φ ∘ discToPlane) (ball 0 1) ↔ Injective Φ := by
  constructor
  · intro h x x' hxx
    have h1 : (Φ ∘ discToPlane) (planeToDisc x) = (Φ ∘ discToPlane) (planeToDisc x') := by
      rw [Function.comp_apply, Function.comp_apply, discToPlane_planeToDisc, discToPlane_planeToDisc, hxx]
    have h2 := h (planeToDisc_mem_ball x) (planeToDisc_mem_ball x') h1
    rw [← discToPlane_planeToDisc x, ← discToPlane_planeToDisc x', h2]
  · intro h w hw w' hw' hww
    have h1 := h hww
    rw [← planeToDisc_discToPlane hw, ← planeToDisc_discToPlane hw', h1]

/-- The image of an open set under the encoding of a conformal map of the disc is open. -/
theorem isOpen_image_of_isOpenDiscMap {U : Set ℂ} {Φ : ℂ → ℂ} (h : IsOpenDiscMap U (Φ ∘ discToPlane))
    {V : Set ℂ} (hV : IsOpen V) : IsOpen (Φ '' V) := by
  have hW : IsOpen (ball (0 : ℂ) 1 ∩ discToPlane ⁻¹' V) := continuousOn_discToPlane.isOpen_inter_preimage isOpen_ball hV
  have heq : Φ '' V = (Φ ∘ discToPlane) '' (ball (0 : ℂ) 1 ∩ discToPlane ⁻¹' V) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨planeToDisc x, ⟨planeToDisc_mem_ball x, ?_⟩, ?_⟩
      · rw [mem_preimage, discToPlane_planeToDisc]
        exact hx
      · rw [Function.comp_apply, discToPlane_planeToDisc]
    · rintro ⟨w, ⟨-, hw⟩, rfl⟩
      exact ⟨discToPlane w, hw, rfl⟩
  rw [heq]
  exact QuantumZipper.CA.isOpen_image_of_injOn' hW (h.differentiableOn.mono inter_subset_left)
    (h.injOn.mono inter_subset_left)

/-! ### Rational discs -/

/-- The center of the rational disc of index `i`. -/
noncomputable def discRatCenter (i : (ℚ × ℚ) × ℕ) : ℂ :=
  ⟨(i.1.1 : ℝ), (i.1.2 : ℝ)⟩

/-- The radius `1 / (k + 1)` of the rational disc of index `i = (c, k)`. -/
noncomputable def discRatRadius (i : (ℚ × ℚ) × ℕ) : ℝ :=
  1 / ((i.2 : ℝ) + 1)

theorem discRatRadius_pos (i : (ℚ × ℚ) × ℕ) : 0 < discRatRadius i :=
  Nat.one_div_pos_of_nat

/-- Every point of an open set lies in a rational open disc whose closure lies in the set. -/
theorem exists_ratBall {V : Set ℂ} (hV : IsOpen V) {y : ℂ} (hy : y ∈ V) :
    ∃ i : (ℚ × ℚ) × ℕ, y ∈ ball (discRatCenter i) (discRatRadius i) ∧ closedBall (discRatCenter i) (discRatRadius i) ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV y hy
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
  set r : ℝ := 1 / ((k : ℝ) + 1) with hr
  have hr0 : 0 < r := Nat.one_div_pos_of_nat
  obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show y.re - r / 2 < y.re + r / 2 by linarith)
  obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show y.im - r / 2 < y.im + r / 2 by linarith)
  set i : (ℚ × ℚ) × ℕ := ((q₁, q₂), k)
  have hre : (discRatCenter i).re = (q₁ : ℝ) := rfl
  have him : (discRatCenter i).im = (q₂ : ℝ) := rfl
  have hdist : dist y (discRatCenter i) < r := by
    rw [dist_eq_norm]
    calc ‖y - discRatCenter i‖ ≤ |(y - discRatCenter i).re| + |(y - discRatCenter i).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < r / 2 + r / 2 := by
        rw [Complex.sub_re, Complex.sub_im, hre, him]
        refine add_lt_add ?_ ?_
        · rw [abs_lt]
          constructor <;> linarith [hq₁.1, hq₁.2]
        · rw [abs_lt]
          constructor <;> linarith [hq₂.1, hq₂.2]
      _ = r := by ring
  refine ⟨i, hdist, fun x hx => hball ?_⟩
  rw [mem_ball]
  have hx' : dist x (discRatCenter i) ≤ r := hx
  calc dist x y ≤ dist x (discRatCenter i) + dist (discRatCenter i) y := dist_triangle _ _ _
    _ < r + r := by
        rw [dist_comm (discRatCenter i) y]
        exact add_lt_add_of_le_of_lt hx' hdist
    _ < ε := by linarith

/-! ### The Borel graph -/

/-- Injectivity is a Borel (`G_δ`) condition on `C(ℂ, ℂ)`. -/
theorem measurableSet_setOf_injective : MeasurableSet {Φ : C(ℂ, ℂ) | Injective Φ} := by
  have h : {Φ : C(ℂ, ℂ) | Injective Φ} = ⋂ n : ℕ, {Φ : C(ℂ, ℂ) | ∃ p ∈
      (closedBall (0 : ℂ) (n : ℝ) ×ˢ closedBall (0 : ℂ) (n : ℝ)) ∩
        {p : ℂ × ℂ | 1 / ((n : ℝ) + 1) ≤ dist p.1 p.2}, Φ p.1 = Φ p.2}ᶜ := by
    ext Φ
    simp only [mem_iInter, mem_compl_iff, mem_ofPred_eq]
    constructor
    · intro hΦ n hex
      obtain ⟨p, hp, hpe⟩ := hex
      have hd : 1 / ((n : ℝ) + 1) ≤ dist p.1 p.2 := hp.2
      rw [hΦ hpe, dist_self] at hd
      exact absurd hd (not_le.2 Nat.one_div_pos_of_nat)
    · intro hΦ w w' hww
      by_contra hne
      obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt (dist_pos.2 hne)
      obtain ⟨n₂, hn₂⟩ := exists_nat_ge (max ‖w‖ ‖w'‖)
      have hle₂ : (n₂ : ℝ) ≤ (max n₁ n₂ : ℕ) := Nat.cast_le.2 (le_max_right _ _)
      have hle₁ : (n₁ : ℝ) + 1 ≤ ((max n₁ n₂ : ℕ) : ℝ) + 1 := by
        have : (n₁ : ℝ) ≤ (max n₁ n₂ : ℕ) := Nat.cast_le.2 (le_max_left _ _)
        linarith
      refine hΦ (max n₁ n₂) ⟨(w, w'), ⟨⟨?_, ?_⟩, ?_⟩, hww⟩
      · exact mem_closedBall_zero_iff.2 (((le_max_left _ _).trans hn₂).trans hle₂)
      · exact mem_closedBall_zero_iff.2 (((le_max_right _ _).trans hn₂).trans hle₂)
      · show 1 / (((max n₁ n₂ : ℕ) : ℝ) + 1) ≤ dist w w'
        exact (one_div_le_one_div_of_le (by positivity) hle₁).trans hn₁.le
  rw [h]
  refine MeasurableSet.iInter fun n => (IsClosed.measurableSet ?_).compl
  refine isClosed_setOf_exists_mem_of_isCompact (((isCompact_closedBall 0 _).prod
    (isCompact_closedBall 0 _)).inter_right (isClosed_le continuous_const continuous_dist)) ?_
  exact isClosed_eq (continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
    (continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

/-- Holomorphy of `Φ ∘ discToPlane` on the open disc together with `φ'(0) ∈ [0, ∞)` is a closed condition on
`C(ℂ, ℂ)` (locally uniform limits of holomorphic maps are holomorphic, with the limit derivatives). -/
theorem isClosed_setOf_differentiableOn_comp_discToPlane :
    IsClosed {Φ : C(ℂ, ℂ) | DifferentiableOn ℂ (Φ ∘ discToPlane) (ball 0 1) ∧
      0 ≤ (deriv (Φ ∘ discToPlane) 0).re ∧ (deriv (Φ ∘ discToPlane) 0).im = 0} := by
  set S := {Φ : C(ℂ, ℂ) | DifferentiableOn ℂ (Φ ∘ discToPlane) (ball 0 1) ∧
      0 ≤ (deriv (Φ ∘ discToPlane) 0).re ∧ (deriv (Φ ∘ discToPlane) 0).im = 0}
  refine isClosed_iff_clusterPt.2 fun Φ hΦ => ?_
  have hl : (𝓝 Φ ⊓ 𝓟 S).NeBot := hΦ
  have ht : Tendsto (fun g : C(ℂ, ℂ) => g) (𝓝 Φ ⊓ 𝓟 S) (𝓝 Φ) := tendsto_id.mono_left inf_le_left
  have hlu₀ : TendstoLocallyUniformlyOn (fun (g : C(ℂ, ℂ)) (z : ℂ) => g z) Φ (𝓝 Φ ⊓ 𝓟 S) univ :=
    (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 ht).tendstoLocallyUniformlyOn
  have hlu : TendstoLocallyUniformlyOn (fun (g : C(ℂ, ℂ)) => (fun z => g z) ∘ discToPlane)
      (Φ ∘ discToPlane) (𝓝 Φ ⊓ 𝓟 S) (ball 0 1) :=
    hlu₀.comp discToPlane (mapsTo_univ _ _) continuousOn_discToPlane
  have hev : ∀ᶠ g in 𝓝 Φ ⊓ 𝓟 S, g ∈ S := mem_inf_of_right (mem_principal_self S)
  have hd : ∀ᶠ g in 𝓝 Φ ⊓ 𝓟 S, DifferentiableOn ℂ ((fun z => (g : C(ℂ, ℂ)) z) ∘ discToPlane) (ball 0 1) :=
    hev.mono fun g hg => hg.1
  have hΦd : DifferentiableOn ℂ (Φ ∘ discToPlane) (ball 0 1) := hlu.differentiableOn hd isOpen_ball
  have hder := (hlu.deriv hd isOpen_ball).tendsto_at (mem_ball_self one_pos)
  have hT : IsClosed {w : ℂ | 0 ≤ w.re ∧ w.im = 0} :=
    (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_eq Complex.continuous_im continuous_const)
  exact ⟨hΦd, hT.mem_of_tendsto hder (hev.mono fun g hg => hg.2)⟩

/-- A rational closed disc lies in the window domain iff its center does and a slightly larger open disc lies in
`η([a, b])`. -/
theorem closedBall_subset_windowDomain_iff {η : C(ℝ, ℂ)} {a u b : ℝ} {c : ℂ} {r : ℝ} (hr : 0 < r) :
    closedBall c r ⊆ windowDomain η a u b ↔
      c ∈ windowDomain η a u b ∧ ∃ q : {q : ℚ // r < q}, ball c (q : ℝ) ⊆ η '' Icc a b := by
  constructor
  · intro h
    refine ⟨h (mem_closedBall_self hr.le), ?_⟩
    have hsub : closedBall c r ⊆ interior (η '' Icc a b) := h.trans (connectedComponentIn_subset _ _)
    obtain ⟨δ, hδ, hthick⟩ := (isCompact_closedBall c r).exists_thickening_subset_open isOpen_interior hsub
    rw [thickening_closedBall hδ hr.le] at hthick
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show r < δ + r by linarith)
    exact ⟨⟨q, hq₁⟩, (ball_subset_ball hq₂.le).trans (hthick.trans interior_subset)⟩
  · rintro ⟨hc, ⟨q, hq⟩, hball⟩
    have hint : closedBall c r ⊆ interior (η '' Icc a b) :=
      (closedBall_subset_ball hq).trans (interior_maximal hball isOpen_ball)
    have h := (convex_closedBall c r).isPreconnected.subset_connectedComponentIn (mem_closedBall_self hr.le) hint
    unfold windowDomain at hc ⊢
    rwa [← connectedComponentIn_eq hc] at h

/-- The curves whose window domain contains a given closed disc form a Borel set. -/
theorem measurableSet_setOf_closedBall_subset_windowDomain (a u b : ℝ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    MeasurableSet {η : C(ℝ, ℂ) | closedBall c r ⊆ windowDomain η a u b} := by
  have heq : {η : C(ℝ, ℂ) | closedBall c r ⊆ windowDomain η a u b} =
      {η : C(ℝ, ℂ) | c ∈ windowDomain η a u b} ∩
        ⋃ q : {q : ℚ // r < q}, {η : C(ℝ, ℂ) | ball c (q : ℝ) ⊆ η '' Icc a b} := by
    ext η
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    exact closedBall_subset_windowDomain_iff hr
  rw [heq]
  refine MeasurableSet.inter ?_ (MeasurableSet.iUnion fun q =>
    ContinuousMap.measurableSet_setOf_subset_image isOpen_ball isCompact_Icc)
  exact LatticeProb.measurableSet_mem_connectedComponentIn_interior_image
    (fun i : (ℚ × ℚ) × ℕ => ball (discRatCenter i) (discRatRadius i)) (fun η : C(ℝ, ℂ) => η) (fun η => η u)
    (fun _ => c) isCompact_Icc measurable_id (continuous_eval_const u).measurable measurable_const
    (fun _ => isOpen_ball) (fun _ => (convex_ball _ _).isPreconnected)
    (fun V hV z hz => by
      obtain ⟨i, hi, hiV⟩ := exists_ratBall hV hz
      exact ⟨i, hi, ball_subset_closedBall.trans hiV⟩)

/-- Covering a closed disc by the image of a compact set is a closed condition on `C(ℂ, ℂ)`. -/
theorem isClosed_setOf_closedBall_subset_image (c : ℂ) (r : ℝ) {K : Set ℂ} (hK : IsCompact K) :
    IsClosed {Φ : C(ℂ, ℂ) | closedBall c r ⊆ Φ '' K} := by
  have heq : {Φ : C(ℂ, ℂ) | closedBall c r ⊆ Φ '' K} = ⋂ y ∈ closedBall c r, {Φ : C(ℂ, ℂ) | ∃ x ∈ K, Φ x = y} := by
    ext Φ
    simp only [mem_ofPred_eq, mem_iInter, subset_def, mem_image]
  rw [heq]
  exact isClosed_biInter fun y _ => isClosed_setOf_exists_mem_of_isCompact hK
    (P := fun (Φ : C(ℂ, ℂ)) (x : ℂ) => Φ x = y) (isClosed_eq continuous_eval continuous_const)

/-- The graph of the normalized conformal maps of the open disc onto the windows `(a, u, b)`, encoded by
`Φ = φ ∘ planeToDisc`. -/
def openWindowDiscMapGraph (a u b : ℝ) : Set (C(ℝ, ℂ) × C(ℂ, ℂ)) :=
  {p | IsNormalizedOpenDiscMap (windowDomain p.1 a u b) (p.1 u) (p.2 ∘ discToPlane)}

theorem mem_openWindowDiscMapGraph_iff {a u b : ℝ} {η : C(ℝ, ℂ)} {Φ : C(ℂ, ℂ)} :
    (η, Φ) ∈ openWindowDiscMapGraph a u b ↔
      Injective Φ ∧ (DifferentiableOn ℂ (Φ ∘ discToPlane) (ball 0 1) ∧ 0 ≤ (deriv (Φ ∘ discToPlane) 0).re ∧
        (deriv (Φ ∘ discToPlane) 0).im = 0) ∧ Φ 0 = η u ∧ (∀ x, Φ x ∈ η '' Icc a b) ∧
        ∀ i : (ℚ × ℚ) × ℕ, closedBall (discRatCenter i) (discRatRadius i) ⊆ windowDomain η a u b →
          ∃ n : ℕ, closedBall (discRatCenter i) (discRatRadius i) ⊆ Φ '' closedBall 0 (n : ℝ) := by
  constructor
  · intro h
    have hO := h.isOpenDiscMap
    have hrange : range Φ = windowDomain η a u b := by
      rw [← image_comp_discToPlane]
      exact hO.image_ball
    refine ⟨(injOn_comp_discToPlane_iff Φ).1 hO.injOn, ⟨hO.differentiableOn, h.deriv_re_pos.le, h.deriv_im⟩,
      ?_, ?_, ?_⟩
    · have h0 := h.apply_zero
      rwa [Function.comp_apply, discToPlane_zero] at h0
    · intro x
      have hx : Φ x ∈ windowDomain η a u b := by
        rw [← hrange]
        exact mem_range_self x
      exact interior_subset (connectedComponentIn_subset _ _ hx)
    · intro i hi
      have hcov : closedBall (discRatCenter i) (discRatRadius i) ⊆ ⋃ n : ℕ, Φ '' ball 0 (n : ℝ) := by
        intro y hy
        have hy' : y ∈ range Φ := by
          rw [hrange]
          exact hi hy
        obtain ⟨x, rfl⟩ := hy'
        obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
        exact mem_iUnion.2 ⟨n, x, mem_ball_zero_iff.2 hn, rfl⟩
      obtain ⟨n, hn⟩ := (isCompact_closedBall _ _).elim_directed_cover (fun n : ℕ => Φ '' ball 0 (n : ℝ))
        (fun n => isOpen_image_of_isOpenDiscMap hO isOpen_ball) hcov
        (Monotone.directed_le fun m n hmn => image_mono (ball_subset_ball (Nat.cast_le.2 hmn)))
      exact ⟨n, hn.trans (image_mono ball_subset_closedBall)⟩
  · rintro ⟨hinj, ⟨hd, hre, him⟩, h0, hK, hball⟩
    have hinjOn : InjOn (Φ ∘ discToPlane) (ball 0 1) := (injOn_comp_discToPlane_iff Φ).2 hinj
    have hopen : IsOpen (range Φ) := by
      rw [← image_comp_discToPlane]
      exact QuantumZipper.CA.isOpen_image_of_injOn' isOpen_ball hd hinjOn
    have hsubK : range Φ ⊆ interior (η '' Icc a b) :=
      interior_maximal (range_subset_iff.2 hK) hopen
    have hsubU : range Φ ⊆ windowDomain η a u b :=
      (isPreconnected_range Φ.continuous).subset_connectedComponentIn ⟨0, h0⟩ hsubK
    have hsupU : windowDomain η a u b ⊆ range Φ := by
      intro y hy
      obtain ⟨i, hyi, hi⟩ := exists_ratBall (isOpen_windowDomain η a u b) hy
      obtain ⟨n, hn⟩ := hball i hi
      obtain ⟨x, -, rfl⟩ := hn (ball_subset_closedBall hyi)
      exact mem_range_self x
    have himage : (Φ ∘ discToPlane) '' ball 0 1 = windowDomain η a u b := by
      rw [image_comp_discToPlane]
      exact Subset.antisymm hsubU hsupU
    have hO : IsOpenDiscMap (windowDomain η a u b) (Φ ∘ discToPlane) := ⟨hd, hinjOn, himage⟩
    refine ⟨hO, ?_, lt_of_le_of_ne hre ?_, him⟩
    · rw [Function.comp_apply, discToPlane_zero]
      exact h0
    · intro hre0
      apply hO.deriv_ne_zero (mem_ball_self one_pos)
      refine Complex.ext ?_ ?_
      · rw [Complex.zero_re]
        exact hre0.symm
      · rw [Complex.zero_im]
        exact him

/-- **The graph is Borel.** -/
theorem measurableSet_openWindowDiscMapGraph (a u b : ℝ) : MeasurableSet (openWindowDiscMapGraph a u b) := by
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have : PolishSpace C(ℂ, ℂ) := LatticeProb.polishSpace_continuousMap ℂ ℂ
  have heq : openWindowDiscMapGraph a u b = {p : C(ℝ, ℂ) × C(ℂ, ℂ) | Injective p.2} ∩
      ({p : C(ℝ, ℂ) × C(ℂ, ℂ) | DifferentiableOn ℂ (p.2 ∘ discToPlane) (ball 0 1) ∧
        0 ≤ (deriv (p.2 ∘ discToPlane) 0).re ∧ (deriv (p.2 ∘ discToPlane) 0).im = 0} ∩
      ({p : C(ℝ, ℂ) × C(ℂ, ℂ) | p.2 0 = p.1 u} ∩
      ({p : C(ℝ, ℂ) × C(ℂ, ℂ) | ∀ x, p.2 x ∈ p.1 '' Icc a b} ∩
      ⋂ i : (ℚ × ℚ) × ℕ, ({p : C(ℝ, ℂ) × C(ℂ, ℂ) |
        closedBall (discRatCenter i) (discRatRadius i) ⊆ windowDomain p.1 a u b}ᶜ ∪
        ⋃ n : ℕ, {p : C(ℝ, ℂ) × C(ℂ, ℂ) | closedBall (discRatCenter i) (discRatRadius i) ⊆ p.2 '' closedBall 0 (n : ℝ)})))) := by
    ext ⟨η, Φ⟩
    rw [mem_openWindowDiscMapGraph_iff]
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, mem_iUnion, imp_iff_not_or]
  rw [heq]
  refine (measurableSet_setOf_injective.preimage measurable_snd).inter
    (((isClosed_setOf_differentiableOn_comp_discToPlane.preimage continuous_snd).measurableSet).inter
    ((isClosed_eq ((continuous_eval_const 0).comp continuous_snd)
      ((continuous_eval_const u).comp continuous_fst)).measurableSet.inter
    (IsClosed.measurableSet ?_ |>.inter (MeasurableSet.iInter fun i => ?_))))
  · simp only [ofPred_forall]
    exact isClosed_iInter fun x => (isClosed_setOf_mem_image_Icc_prod a b).preimage
      (continuous_fst.prodMk ((continuous_eval_const x).comp continuous_snd))
  · refine (((measurableSet_setOf_closedBall_subset_windowDomain a u b _ (discRatRadius_pos i)).preimage
      measurable_fst).compl).union (MeasurableSet.iUnion fun n => ?_)
    exact ((isClosed_setOf_closedBall_subset_image _ _ (isCompact_closedBall 0 (n : ℝ))).preimage
      continuous_snd).measurableSet

/-- Uniqueness: the graph is the graph of a function. -/
theorem eq_of_mem_openWindowDiscMapGraph {a u b : ℝ} {η : C(ℝ, ℂ)} {Φ₁ Φ₂ : C(ℂ, ℂ)}
    (h₁ : (η, Φ₁) ∈ openWindowDiscMapGraph a u b) (h₂ : (η, Φ₂) ∈ openWindowDiscMapGraph a u b) : Φ₁ = Φ₂ := by
  have hE := IsNormalizedOpenDiscMap.eqOn h₁ h₂
  ext x
  have h := hE (planeToDisc_mem_ball x)
  rwa [Function.comp_apply, Function.comp_apply, discToPlane_planeToDisc] at h

/-- A window with a conformal map of the open disc taking `0` to `η(u)` has its normalized one in the graph. -/
theorem exists_mem_openWindowDiscMapGraph {a u b : ℝ} {η : C(ℝ, ℂ)} {φ : ℂ → ℂ}
    (hφ : IsOpenDiscMap (windowDomain η a u b) φ) (h0 : φ 0 = η u) :
    ∃ Φ, (η, Φ) ∈ openWindowDiscMapGraph a u b := by
  obtain ⟨c, -, hN⟩ := hφ.exists_isNormalizedOpenDiscMap
  rw [h0] at hN
  have hcont : Continuous ((fun w => φ (c * w)) ∘ planeToDisc) :=
    hN.isOpenDiscMap.continuousOn.comp_continuous planeToDisc.continuous planeToDisc_mem_ball
  refine ⟨⟨_, hcont⟩, hN.congr fun w hw => ?_⟩
  show φ (c * w) = φ (c * planeToDisc (discToPlane w))
  rw [planeToDisc_discToPlane hw]

/-! ### The Borel choice -/

open Classical in
/-- **The code of the normalized conformal map of the open disc onto the window `(a, u, b)` of `η`** at `η(u)` (`0`
when there is none). -/
noncomputable def openWindowDiscCode (a u b : ℝ) (η : C(ℝ, ℂ)) : C(ℂ, ℂ) :=
  if h : ∃ Φ, (η, Φ) ∈ openWindowDiscMapGraph a u b then h.choose else 0

/-- **The code is a Borel function of the curve.** -/
theorem measurable_openWindowDiscCode (a u b : ℝ) : Measurable (openWindowDiscCode a u b) := by
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have : PolishSpace C(ℂ, ℂ) := LatticeProb.polishSpace_continuousMap ℂ ℂ
  exact measurable_graphChoice (measurableSet_openWindowDiscMapGraph a u b)
    (fun _ _ _ h₁ h₂ => eq_of_mem_openWindowDiscMapGraph h₁ h₂) 0

theorem openWindowDiscCode_mem {a u b : ℝ} {η : C(ℝ, ℂ)} (h : ∃ Φ, (η, Φ) ∈ openWindowDiscMapGraph a u b) :
    (η, openWindowDiscCode a u b η) ∈ openWindowDiscMapGraph a u b := by
  unfold openWindowDiscCode
  rw [dite_eq_left h]
  exact h.choose_spec

/-- **The normalized conformal map of the open disc onto the window `(a, u, b)` of `η`.** -/
noncomputable def openWindowDiscMap (a u b : ℝ) (η : C(ℝ, ℂ)) : ℂ → ℂ :=
  openWindowDiscCode a u b η ∘ discToPlane

theorem isNormalizedOpenDiscMap_openWindowDiscMap {a u b : ℝ} {η : C(ℝ, ℂ)}
    (h : ∃ Φ, (η, Φ) ∈ openWindowDiscMapGraph a u b) :
    IsNormalizedOpenDiscMap (windowDomain η a u b) (η u) (openWindowDiscMap a u b η) :=
  openWindowDiscCode_mem h

/-! ### The Borel inverse -/

/-- The pairs `((Φ, x), y)` with `Φ` injective and `Φ y = x`. -/
def invGraph : Set ((C(ℂ, ℂ) × ℂ) × ℂ) :=
  {p | Injective p.1.1 ∧ p.1.1 p.2 = p.1.2}

theorem measurableSet_invGraph : MeasurableSet invGraph :=
  (measurableSet_setOf_injective.preimage (measurable_fst.comp measurable_fst)).inter
    (isClosed_eq (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      (continuous_snd.comp continuous_fst)).measurableSet

open Classical in
/-- **The inverse of an injective continuous map at a point of its range** (`0` otherwise). -/
noncomputable def invCode (p : C(ℂ, ℂ) × ℂ) : ℂ :=
  if h : ∃ y, (p, y) ∈ invGraph then h.choose else 0

theorem measurable_invCode : Measurable invCode := by
  have : PolishSpace C(ℂ, ℂ) := LatticeProb.polishSpace_continuousMap ℂ ℂ
  exact measurable_graphChoice measurableSet_invGraph (fun p y y' h₁ h₂ => h₁.1 (h₁.2.trans h₂.2.symm)) 0

theorem apply_invCode {Φ : C(ℂ, ℂ)} (hΦ : Injective Φ) {x : ℂ} (hx : x ∈ range Φ) : Φ (invCode (Φ, x)) = x := by
  obtain ⟨y, rfl⟩ := hx
  have h : ∃ y', ((Φ, Φ y), y') ∈ invGraph := ⟨y, hΦ, rfl⟩
  unfold invCode
  rw [dite_eq_left h]
  exact h.choose_spec.2

theorem invCode_apply {Φ : C(ℂ, ℂ)} (hΦ : Injective Φ) (y : ℂ) : invCode (Φ, Φ y) = y :=
  hΦ (apply_invCode hΦ (mem_range_self y))

end MatedCRT
