import MatedCRT.FirstPass.Derived.InverseChartOfJordan
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsAutomorphisms

/-!
# Normalized conformal maps of the closed disc onto a window domain

For a bounded open set `U` with an inverse chart `ψ` at `z` (`IsInverseChart U z ψ`), the inverse map on the closure
of `U` is a conformal map `φ` of the open unit disc onto `U`, extended homeomorphically to the closed disc
(`IsDiscMap U φ`). Conversely a conformal map of the closed disc gives an inverse chart (Tietze's extension
theorem). Precomposing with a rotation makes `φ'(0)` a positive real number, and the normalized map is unique
(Schwarz lemma: the conformal automorphisms of the disc fixing `0` are the rotations). This is the normalization of
the conformal map `φ : 𝔻 → U` used by Berestycki–Gwynne (2020) in the proof of Lemma 7.18; uniqueness is what makes
a Borel choice of the inverse chart in the joint-limit sample possible.

## Main statements

* `IsDiscMap`, `IsDiscMap.exists_isInverseChart`, `IsInverseChart.exists_isDiscMap`.
* `IsDiscMap.exists_normalized`: normalization of `φ'(0)` by a rotation.
* `IsDiscMap.eqOn_of_deriv_pos`: uniqueness of the normalized conformal map on the closed disc.
* `IsNormalizedDiscMap`, `exists_isNormalizedDiscMap_of_isInverseChart`, `IsNormalizedDiscMap.exists_isInverseChart`,
  `IsNormalizedDiscMap.eqOn`.
-/

set_option autoImplicit false

open Set Metric Filter Topology

namespace MatedCRT

/-- `φ` is a conformal map of the open unit disc onto `U` extended homeomorphically to the closed disc: continuous and
injective on the closed unit disc, holomorphic on the open disc, mapping the open disc onto `U` and the unit circle
onto the frontier of `U`. -/
structure IsDiscMap (U : Set ℂ) (φ : ℂ → ℂ) : Prop where
  continuousOn : ContinuousOn φ (closedBall 0 1)
  injOn : InjOn φ (closedBall 0 1)
  differentiableOn : DifferentiableOn ℂ φ (ball 0 1)
  image_ball : φ '' ball 0 1 = U
  image_sphere : φ '' sphere 0 1 = frontier U

/-- Multiplication by a complex number of modulus one preserves every set defined by a condition on the modulus. -/
theorem image_mul_eq_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) {s : Set ℂ} (P : ℝ → Prop)
    (hs : ∀ w, w ∈ s ↔ P ‖w‖) : (fun w => c * w) '' s = s := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [hs, norm_mul, hc, one_mul, ← hs]
    exact hw
  · intro hv
    refine ⟨c⁻¹ * v, ?_, ?_⟩
    · rw [hs, norm_mul, norm_inv, hc, inv_one, one_mul, ← hs]
      exact hv
    · show c * (c⁻¹ * v) = v
      rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

namespace IsDiscMap

variable {U : Set ℂ} {φ : ℂ → ℂ}

theorem image_closedBall (h : IsDiscMap U φ) : φ '' closedBall 0 1 = closure U := by
  rw [← ball_union_sphere, image_union, h.image_ball, h.image_sphere, closure_eq_self_union_frontier]

theorem isOpen (h : IsDiscMap U φ) : IsOpen U := by
  rw [← h.image_ball]
  exact QuantumZipper.CA.isOpen_image_of_injOn' isOpen_ball h.differentiableOn
    (h.injOn.mono ball_subset_closedBall)

theorem apply_zero_mem (h : IsDiscMap U φ) : φ 0 ∈ U :=
  h.image_ball ▸ mem_image_of_mem φ (mem_ball_self one_pos)

/-- A conformal map has non-vanishing derivative on the open disc. -/
theorem deriv_ne_zero (h : IsDiscMap U φ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : deriv φ w ≠ 0 :=
  QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball h.differentiableOn (h.injOn.mono ball_subset_closedBall) hw

/-- **The inverse chart of a conformal map.** A conformal map `φ` of the closed disc onto the closure of `U` gives an
inverse chart of `U` at `φ 0`: a continuous extension to `ℂ` (Tietze) of the inverse map on the closure of `U`. -/
theorem exists_isInverseChart (h : IsDiscMap U φ) :
    ∃ ψ : C(ℂ, ℂ), IsInverseChart U (φ 0) ψ ∧ ∀ w ∈ closedBall (0 : ℂ) 1, ψ (φ w) = w := by
  have hcl := h.image_closedBall
  have hbij : BijOn φ (closedBall 0 1) (closure U) :=
    ⟨fun w hw => hcl ▸ mem_image_of_mem φ hw, h.injOn, by rw [← hcl]; exact surjOn_image φ _⟩
  let e : closedBall (0 : ℂ) 1 ≃ closure U := hbij.equiv φ
  have he : Continuous e := h.continuousOn.domRestrict.subtype_mk _
  have : CompactSpace (closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  let k : closedBall (0 : ℂ) 1 ≃ₜ closure U := he.homeoOfEquivCompactToT2
  have hk : ∀ x, (k x : ℂ) = φ x := fun _ => rfl
  let g : C(closure U, ℂ) := ⟨fun y => (k.symm y : ℂ), continuous_subtype_val.comp k.symm.continuous⟩
  obtain ⟨ψ, hψ⟩ := ContinuousMap.exists_restrict_eq isClosed_closure g
  have hψy : ∀ y (hy : y ∈ closure U), ψ y = (k.symm ⟨y, hy⟩ : ℂ) := fun y hy =>
    DFunLike.congr_fun hψ ⟨y, hy⟩
  have hφψ : ∀ y ∈ closure U, φ (ψ y) = y := fun y hy => by
    rw [hψy y hy, ← hk, k.apply_symm_apply]
  have hψφ : ∀ w ∈ closedBall (0 : ℂ) 1, ψ (φ w) = w := fun w hw => by
    have hmem : φ w ∈ closure U := hbij.mapsTo hw
    rw [hψy _ hmem]
    have : (⟨φ w, hmem⟩ : closure U) = k ⟨w, hw⟩ := rfl
    rw [this, k.symm_apply_apply]
  have hinj : InjOn φ (ball 0 1) := h.injOn.mono ball_subset_closedBall
  let eU := QuantumZipper.CA.univalentOPH isOpen_ball h.differentiableOn hinj
  have heU : DifferentiableOn ℂ eU.symm (φ '' ball 0 1) :=
    QuantumZipper.CA.differentiableOn_univalentOPH_symm isOpen_ball h.differentiableOn hinj
  refine ⟨ψ, ⟨h.apply_zero_mem, hψφ 0 (mem_closedBall_self zero_le_one), ?_, ?_, ?_, ?_⟩, hψφ⟩
  · intro y hy y' hy' hyy
    rw [← hφψ y hy, ← hφψ y' hy', hyy]
  · rw [← h.image_ball]
    refine heU.congr fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := hy
    rw [hψφ w (ball_subset_closedBall hw)]
    exact (QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball h.differentiableOn hinj hw).symm
  · ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w', hw', rfl⟩ := h.image_ball.symm ▸ hy
      rw [hψφ w' (ball_subset_closedBall hw')]
      exact hw'
    · intro hw
      exact ⟨φ w, h.image_ball ▸ mem_image_of_mem φ hw, hψφ w (ball_subset_closedBall hw)⟩
  · ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w', hw', rfl⟩ := h.image_sphere.symm ▸ hy
      rw [hψφ w' (sphere_subset_closedBall hw')]
      exact hw'
    · intro hw
      exact ⟨φ w, h.image_sphere ▸ mem_image_of_mem φ hw, hψφ w (sphere_subset_closedBall hw)⟩

/-- Precomposing a conformal map with a rotation gives a conformal map. -/
theorem comp_mul (h : IsDiscMap U φ) {c : ℂ} (hc : ‖c‖ = 1) : IsDiscMap U (fun w => φ (c * w)) := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  have hmaps : MapsTo (fun w => c * w) (closedBall (0 : ℂ) 1) (closedBall 0 1) := fun w hw => by
    rw [mem_closedBall_zero_iff, norm_mul, hc, one_mul]
    exact mem_closedBall_zero_iff.1 hw
  have hmapsb : MapsTo (fun w => c * w) (ball (0 : ℂ) 1) (ball 0 1) := fun w hw => by
    rw [mem_ball_zero_iff, norm_mul, hc, one_mul]
    exact mem_ball_zero_iff.1 hw
  refine ⟨h.continuousOn.comp (continuous_const.mul continuous_id).continuousOn hmaps,
    fun w hw w' hw' hww => mul_left_cancel₀ hc0 (h.injOn (hmaps hw) (hmaps hw') hww),
    h.differentiableOn.comp (differentiable_id.const_mul c).differentiableOn hmapsb, ?_, ?_⟩
  · show (φ ∘ fun w => c * w) '' ball 0 1 = U
    rw [image_comp, image_mul_eq_of_norm_eq_one hc (fun r => r < 1) (fun w => mem_ball_zero_iff), h.image_ball]
  · show (φ ∘ fun w => c * w) '' sphere 0 1 = frontier U
    rw [image_comp, image_mul_eq_of_norm_eq_one hc (fun r => r = 1) (fun w => mem_sphere_zero_iff_norm),
      h.image_sphere]

/-- The derivative at `0` of a conformal map precomposed with `w ↦ c w`. -/
theorem hasDerivAt_comp_mul (h : IsDiscMap U φ) (c : ℂ) :
    HasDerivAt (fun w => φ (c * w)) (deriv φ 0 * c) 0 := by
  have hd : HasDerivAt φ (deriv φ (c * 0)) (c * 0) := by
    rw [mul_zero]
    exact (h.differentiableOn.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))).hasDerivAt
  have := hd.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul c)
  simpa only [mul_zero, mul_one, Function.comp_def, id_eq] using this

/-- **Normalization of the derivative.** Precomposing a conformal map with a rotation gives a conformal map whose
derivative at `0` is a positive real number. -/
theorem exists_normalized (h : IsDiscMap U φ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ IsDiscMap U (fun w => φ (c * w)) ∧ 0 < (deriv (fun w => φ (c * w)) 0).re ∧
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

/-- **Uniqueness of the normalized conformal map** (Schwarz lemma: the conformal automorphisms of the disc fixing `0`
are the rotations). Two conformal maps of the closed disc onto the closure of `U` with the same value at `0` and
positive real derivatives at `0` agree on the closed disc. -/
theorem eqOn_of_deriv_pos {φ₁ φ₂ : ℂ → ℂ} (h₁ : IsDiscMap U φ₁) (h₂ : IsDiscMap U φ₂) (h0 : φ₁ 0 = φ₂ 0)
    (hr₁ : 0 < (deriv φ₁ 0).re) (hi₁ : (deriv φ₁ 0).im = 0) (hr₂ : 0 < (deriv φ₂ 0).re)
    (hi₂ : (deriv φ₂ 0).im = 0) : EqOn φ₁ φ₂ (closedBall 0 1) := by
  have hinj₂ : InjOn φ₂ (ball 0 1) := h₂.injOn.mono ball_subset_closedBall
  set e := QuantumZipper.CA.univalentOPH isOpen_ball h₂.differentiableOn hinj₂
  have htarget : ∀ w ∈ ball (0 : ℂ) 1, φ₁ w ∈ φ₂ '' ball 0 1 := fun w hw => by
    rw [h₂.image_ball, ← h₁.image_ball]
    exact mem_image_of_mem φ₁ hw
  have hφ₂f : ∀ w ∈ ball (0 : ℂ) 1, φ₂ (e.symm (φ₁ w)) = φ₁ w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply isOpen_ball h₂.differentiableOn hinj₂ (htarget w hw)
  have hfball : ∀ w ∈ ball (0 : ℂ) 1, e.symm (φ₁ w) ∈ ball (0 : ℂ) 1 := fun w hw =>
    e.map_target (htarget w hw)
  have hfd : DifferentiableOn ℂ (fun w => e.symm (φ₁ w)) (ball 0 1) :=
    (QuantumZipper.CA.differentiableOn_univalentOPH_symm isOpen_ball h₂.differentiableOn hinj₂).comp
      h₁.differentiableOn htarget
  have hbij : BijOn (fun w => e.symm (φ₁ w)) (ball 0 1) (ball 0 1) := by
    refine ⟨hfball, fun w hw w' hw' hww => ?_, fun v hv => ?_⟩
    · have h2 : φ₂ (e.symm (φ₁ w)) = φ₂ (e.symm (φ₁ w')) := congrArg φ₂ hww
      rw [hφ₂f w hw, hφ₂f w' hw'] at h2
      exact h₁.injOn (ball_subset_closedBall hw) (ball_subset_closedBall hw') h2
    · have hv' : φ₂ v ∈ φ₁ '' ball 0 1 := by
        rw [h₁.image_ball, ← h₂.image_ball]
        exact mem_image_of_mem φ₂ hv
      obtain ⟨w, hw, hwv⟩ := hv'
      refine ⟨w, hw, ?_⟩
      show e.symm (φ₁ w) = v
      rw [hwv]
      exact QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball h₂.differentiableOn hinj₂ hv
  have hf0 : e.symm (φ₁ 0) = 0 := by
    rw [h0]
    exact QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball h₂.differentiableOn hinj₂
      (mem_ball_self one_pos)
  obtain ⟨c, hc, hrot⟩ := QuantumZipper.CA.exists_rotation_of_bijOn_ball hfd hbij hf0
  have hφ₁ : ∀ w ∈ ball (0 : ℂ) 1, φ₁ w = φ₂ (c * w) := fun w hw => by
    have h1 : e.symm (φ₁ w) = c * w := hrot hw
    rw [← h1, hφ₂f w hw]
  have hev : φ₁ =ᶠ[𝓝 0] fun w => φ₂ (c * w) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) hφ₁
  have hd : deriv φ₁ 0 = deriv φ₂ 0 * c := by
    rw [hev.deriv_eq]
    exact (h₂.hasDerivAt_comp_mul c).deriv
  obtain ⟨r₁, hr₁'⟩ : ∃ r : ℝ, deriv φ₁ 0 = r :=
    ⟨(deriv φ₁ 0).re, Complex.ext (by simp) (by simp [hi₁])⟩
  obtain ⟨r₂, hr₂'⟩ : ∃ r : ℝ, deriv φ₂ 0 = r :=
    ⟨(deriv φ₂ 0).re, Complex.ext (by simp) (by simp [hi₂])⟩
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
  have hball : EqOn φ₁ φ₂ (ball 0 1) := fun w hw => by rw [hφ₁ w hw, one_mul]
  exact hball.of_subset_closure h₁.continuousOn h₂.continuousOn ball_subset_closedBall
    (closure_ball (0 : ℂ) one_ne_zero).symm.subset

end IsDiscMap

/-- **The inverse map of an inverse chart.** For an inverse chart `ψ` of a bounded open set `U`, the inverse of `ψ`
on the closure of `U`, extended continuously to `ℂ` (Tietze), is a conformal map of the closed disc onto the closure
of `U`. -/
theorem IsInverseChart.exists_isDiscMap {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)} (hψ : IsInverseChart U z ψ)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ φ : C(ℂ, ℂ), IsDiscMap U φ ∧ φ 0 = z ∧ ∀ y ∈ closure U, φ (ψ y) = y := by
  have hcl : ψ '' closure U = closedBall 0 1 := by
    rw [closure_eq_self_union_frontier, image_union, hψ.image_eq, hψ.image_frontier, ball_union_sphere]
  have hbij : BijOn ψ (closure U) (closedBall 0 1) :=
    ⟨fun y hy => hcl ▸ mem_image_of_mem ψ hy, hψ.injOn, by rw [← hcl]; exact surjOn_image ψ _⟩
  let e : closure U ≃ closedBall (0 : ℂ) 1 := hbij.equiv ψ
  have he : Continuous e := ψ.continuous.continuousOn.domRestrict.subtype_mk _
  have : CompactSpace (closure U) := isCompact_iff_compactSpace.1 hUb.isCompact_closure
  let k : closure U ≃ₜ closedBall (0 : ℂ) 1 := he.homeoOfEquivCompactToT2
  have hk : ∀ y, (k y : ℂ) = ψ y := fun _ => rfl
  let g : C(closedBall (0 : ℂ) 1, ℂ) := ⟨fun w => (k.symm w : ℂ), continuous_subtype_val.comp k.symm.continuous⟩
  obtain ⟨φ, hφ⟩ := ContinuousMap.exists_restrict_eq isClosed_closedBall g
  have hφw : ∀ w (hw : w ∈ closedBall (0 : ℂ) 1), φ w = (k.symm ⟨w, hw⟩ : ℂ) := fun w hw =>
    DFunLike.congr_fun hφ ⟨w, hw⟩
  have hψφ : ∀ w ∈ closedBall (0 : ℂ) 1, ψ (φ w) = w := fun w hw => by
    rw [hφw w hw, ← hk, k.apply_symm_apply]
  have hφψ : ∀ y ∈ closure U, φ (ψ y) = y := fun y hy => by
    have hmem : ψ y ∈ closedBall (0 : ℂ) 1 := hbij.mapsTo hy
    rw [hφw _ hmem]
    have : (⟨ψ y, hmem⟩ : closedBall (0 : ℂ) 1) = k ⟨y, hy⟩ := rfl
    rw [this, k.symm_apply_apply]
  have hinj : InjOn ψ U := hψ.injOn.mono subset_closure
  have heU := QuantumZipper.CA.differentiableOn_univalentOPH_symm hU hψ.differentiableOn hinj
  rw [hψ.image_eq] at heU
  refine ⟨φ, ⟨φ.continuous.continuousOn, fun w hw w' hw' hww => ?_, ?_, ?_, ?_⟩, ?_, hφψ⟩
  · rw [← hψφ w hw, ← hψφ w' hw', hww]
  · refine heU.congr fun w hw => ?_
    obtain ⟨y, hy, rfl⟩ := hψ.image_eq.symm ▸ hw
    rw [hφψ y (subset_closure hy)]
    exact (QuantumZipper.CA.univalentOPH_symm_apply_apply hU hψ.differentiableOn hinj hy).symm
  · ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨y', hy', rfl⟩ := hψ.image_eq.symm ▸ hw
      rw [hφψ y' (subset_closure hy')]
      exact hy'
    · intro hy
      exact ⟨ψ y, hψ.image_eq ▸ mem_image_of_mem ψ hy, hφψ y (subset_closure hy)⟩
  · ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨y', hy', rfl⟩ := hψ.image_frontier.symm ▸ hw
      rw [hφψ y' (frontier_subset_closure hy')]
      exact hy'
    · intro hy
      exact ⟨ψ y, hψ.image_frontier ▸ mem_image_of_mem ψ hy, hφψ y (frontier_subset_closure hy)⟩
  · rw [← hψ.apply_point, hφψ z (subset_closure hψ.mem)]

/-- `φ` is the normalized conformal map of `U` at `z`: a conformal map of the closed disc onto the closure of `U` with
`φ 0 = z` and `φ'(0)` a positive real number. -/
structure IsNormalizedDiscMap (U : Set ℂ) (z : ℂ) (φ : ℂ → ℂ) : Prop where
  isDiscMap : IsDiscMap U φ
  apply_zero : φ 0 = z
  deriv_re_pos : 0 < (deriv φ 0).re
  deriv_im : (deriv φ 0).im = 0

/-- **Uniqueness of the normalized conformal map** on the closed disc. -/
theorem IsNormalizedDiscMap.eqOn {U : Set ℂ} {z : ℂ} {φ₁ φ₂ : ℂ → ℂ} (h₁ : IsNormalizedDiscMap U z φ₁)
    (h₂ : IsNormalizedDiscMap U z φ₂) : EqOn φ₁ φ₂ (closedBall 0 1) :=
  h₁.isDiscMap.eqOn_of_deriv_pos h₂.isDiscMap (h₁.apply_zero.trans h₂.apply_zero.symm) h₁.deriv_re_pos
    h₁.deriv_im h₂.deriv_re_pos h₂.deriv_im

/-- A normalized conformal map gives an inverse chart at `z`. -/
theorem IsNormalizedDiscMap.exists_isInverseChart {U : Set ℂ} {z : ℂ} {φ : ℂ → ℂ}
    (h : IsNormalizedDiscMap U z φ) :
    ∃ ψ : C(ℂ, ℂ), IsInverseChart U z ψ ∧ ∀ w ∈ closedBall (0 : ℂ) 1, ψ (φ w) = w := by
  obtain ⟨ψ, hψ, hψφ⟩ := h.isDiscMap.exists_isInverseChart
  rw [h.apply_zero] at hψ
  exact ⟨ψ, hψ, hψφ⟩

/-- **Existence of the normalized conformal map.** A bounded open set with an inverse chart at `z` has a normalized
conformal map at `z`. -/
theorem exists_isNormalizedDiscMap_of_isInverseChart {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ φ : C(ℂ, ℂ), IsNormalizedDiscMap U z φ := by
  obtain ⟨φ, hφ, hφ0, -⟩ := hψ.exists_isDiscMap hU hUb
  obtain ⟨c, hc, hφc, hre, him⟩ := hφ.exists_normalized
  refine ⟨φ.comp ⟨fun w => c * w, continuous_const.mul continuous_id⟩, hφc, ?_, hre, him⟩
  show φ (c * 0) = z
  rw [mul_zero, hφ0]

end MatedCRT
