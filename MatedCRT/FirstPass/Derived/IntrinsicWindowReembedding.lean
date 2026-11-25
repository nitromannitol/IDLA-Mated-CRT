import MatedCRT.FirstPass.Derived.OpenDiscMap
import MatedCRT.External.DMSIntrinsicPastFutureIndependence

/-!
# Windows under intrinsic re-embeddings of a curve-decorated quantum surface

Let `f` be an intrinsic re-embedding over the times `T` of the curve-decorated quantum surface `(h₂, η₂)` onto
`(h₁, η₁)` (`IsIntrinsicCurveDecoratedReembedding`; Gwynne–Miller, arXiv:1701.05174, Definition 2.1): `f` is conformal
and injective on the interior `O₂` of `η₂(T)`, maps it onto the interior `O₁` of `η₁(T)`, matches the curves at the
times of `T` at which they are in these interiors, and these times are the same for both curves. For a window
`(a, u, b)` with `[a, b] ⊆ T` this file shows:

* `f` maps the interior of `η₂([a, b])` onto the interior of `η₁([a, b])`;
* it maps the window domain of `η₂` onto the window domain of `η₁` (the components at `η(u)`), and the times of `T` at
  which the curves visit the window domains are the same;
* it carries conformal maps of the open disc onto the window domain of `η₂` to those of `η₁` and back, and the
  normalized ones differ by a rotation of the disc after composition with `f`.

## Main statements

* `IsIntrinsicCurveDecoratedReembedding.image_interior_image`, `.image_windowDomain`, `.mem_windowDomain_iff`.
* `.exists_openDiscMap_iff`, `.exists_rotation_openWindowDiscMap`.
-/

set_option autoImplicit false

open Set Metric Filter Topology Function

namespace MatedCRT

namespace IsIntrinsicCurveDecoratedReembedding

variable {γ : ℝ} {T : Set ℝ} {h₁ h₂ : LQGMetric.DistC} {η₁ η₂ : C(ℝ, ℂ)} {f : ℂ → ℂ}

/-- The inverse of `f` on the interior of `η₁(T)`. -/
noncomputable def inv (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) : ℂ → ℂ :=
  (QuantumZipper.CA.univalentOPH isOpen_interior hf.2.2.2.1 hf.2.2.1).symm

theorem inv_apply (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) {x : ℂ}
    (hx : x ∈ interior (η₂ '' T)) : hf.inv (f x) = x :=
  QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_interior hf.2.2.2.1 hf.2.2.1 hx

theorem apply_inv (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) {y : ℂ}
    (hy : y ∈ interior (η₁ '' T)) : f (hf.inv y) = y := by
  rw [← hf.2.2.2.2.1] at hy
  exact QuantumZipper.CA.univalentOPH_apply_symm_apply isOpen_interior hf.2.2.2.1 hf.2.2.1 hy

theorem inv_mem (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) {y : ℂ}
    (hy : y ∈ interior (η₁ '' T)) : hf.inv y ∈ interior (η₂ '' T) := by
  rw [← hf.2.2.2.2.1] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [hf.inv_apply hx]
  exact hx

theorem differentiableOn_inv (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) :
    DifferentiableOn ℂ hf.inv (interior (η₁ '' T)) := by
  rw [← hf.2.2.2.2.1]
  exact QuantumZipper.CA.differentiableOn_univalentOPH_symm isOpen_interior hf.2.2.2.1 hf.2.2.1

theorem injOn_inv (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) :
    InjOn hf.inv (interior (η₁ '' T)) := fun y hy y' hy' hyy => by
  rw [← hf.apply_inv hy, ← hf.apply_inv hy', hyy]

/-- A point of `f(W)`, for `W` in the interior of `η₂(T)`, on the curve `η₁` at a time of `T` is the image of the point
of `η₂` at that time, which lies in `W`. -/
theorem mem_image_iff (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) {W : Set ℂ}
    (hW : W ⊆ interior (η₂ '' T)) {t : ℝ} (ht : t ∈ T) : η₁ t ∈ f '' W ↔ η₂ t ∈ W := by
  constructor
  · rintro ⟨x, hxW, hx⟩
    have hO₁ : η₁ t ∈ interior (η₁ '' T) := by
      rw [← hf.2.2.2.2.1, ← hx]
      exact mem_image_of_mem f (hW hxW)
    have hO₂ := hf.2.1 t ht hO₁
    have h1 : f (η₂ t) = f x := (hf.1 t ht hO₂).trans hx.symm
    rw [hf.2.2.1 hO₂ (hW hxW) h1]
    exact hxW
  · intro h
    exact ⟨η₂ t, h, hf.1 t ht (hW h)⟩

/-- **`f` maps the interior of `η₂(J)` onto the interior of `η₁(J)`** for `J ⊆ T`. -/
theorem image_interior_image (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) {J : Set ℝ}
    (hJ : J ⊆ T) : f '' interior (η₂ '' J) = interior (η₁ '' J) := by
  have hsub₂ : interior (η₂ '' J) ⊆ interior (η₂ '' T) := interior_mono (image_mono hJ)
  have hsub₁ : interior (η₁ '' J) ⊆ interior (η₁ '' T) := interior_mono (image_mono hJ)
  apply Subset.antisymm
  · refine interior_maximal ?_ (QuantumZipper.CA.isOpen_image_of_injOn' isOpen_interior
      (hf.2.2.2.1.mono hsub₂) (hf.2.2.1.mono hsub₂))
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, htJ, rfl⟩ := interior_subset hx
    rw [hf.1 t (hJ htJ) (hsub₂ hx)]
    exact mem_image_of_mem η₁ htJ
  · have hopen : IsOpen (hf.inv '' interior (η₁ '' J)) :=
      QuantumZipper.CA.isOpen_image_of_injOn' isOpen_interior (hf.differentiableOn_inv.mono hsub₁)
        (hf.injOn_inv.mono hsub₁)
    have hsub : hf.inv '' interior (η₁ '' J) ⊆ interior (η₂ '' J) := by
      refine interior_maximal ?_ hopen
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨t, htJ, rfl⟩ := interior_subset hy
      have hO₂ := hf.2.1 t (hJ htJ) (hsub₁ hy)
      rw [← hf.1 t (hJ htJ) hO₂, hf.inv_apply hO₂]
      exact mem_image_of_mem η₂ htJ
    intro y hy
    exact ⟨hf.inv y, hsub (mem_image_of_mem _ hy), hf.apply_inv (hsub₁ hy)⟩

/-- **`f` maps the window domain of `η₂` onto the window domain of `η₁`.** -/
theorem image_windowDomain (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) {a u b : ℝ}
    (hJ : Icc a b ⊆ T) (hu : u ∈ Icc a b) : f '' windowDomain η₂ a u b = windowDomain η₁ a u b := by
  have hI := hf.image_interior_image hJ
  have hsub₂ : interior (η₂ '' Icc a b) ⊆ interior (η₂ '' T) := interior_mono (image_mono hJ)
  have hsub₁ : interior (η₁ '' Icc a b) ⊆ interior (η₁ '' T) := interior_mono (image_mono hJ)
  by_cases hc : η₂ u ∈ interior (η₂ '' Icc a b)
  · have hfu : f (η₂ u) = η₁ u := hf.1 u (hJ hu) (hsub₂ hc)
    apply Subset.antisymm
    · have hpre : IsPreconnected (f '' windowDomain η₂ a u b) :=
        isPreconnected_connectedComponentIn.image f ((hf.2.2.2.1.continuousOn.mono hsub₂).mono
          (connectedComponentIn_subset _ _))
      refine hpre.subset_connectedComponentIn ⟨η₂ u, mem_connectedComponentIn hc, hfu⟩ ?_
      rw [← hI]
      exact image_mono (connectedComponentIn_subset _ _)
    · have hc₁ : η₁ u ∈ interior (η₁ '' Icc a b) := by
        rw [← hI, ← hfu]
        exact mem_image_of_mem f hc
      have hinvu : hf.inv (η₁ u) = η₂ u := by
        rw [← hfu, hf.inv_apply (hsub₂ hc)]
      have hpre : IsPreconnected (hf.inv '' windowDomain η₁ a u b) :=
        isPreconnected_connectedComponentIn.image hf.inv ((hf.differentiableOn_inv.continuousOn.mono hsub₁).mono
          (connectedComponentIn_subset _ _))
      have hsub : hf.inv '' windowDomain η₁ a u b ⊆ windowDomain η₂ a u b := by
        refine hpre.subset_connectedComponentIn ⟨η₁ u, mem_connectedComponentIn hc₁, hinvu⟩ ?_
        rintro _ ⟨y, hy, rfl⟩
        have hy' : y ∈ interior (η₁ '' Icc a b) := connectedComponentIn_subset _ _ hy
        rw [← hI] at hy'
        obtain ⟨x, hx, rfl⟩ := hy'
        rw [hf.inv_apply (hsub₂ hx)]
        exact hx
      intro y hy
      have hy' : y ∈ interior (η₁ '' T) := hsub₁ (connectedComponentIn_subset _ _ hy)
      exact ⟨hf.inv y, hsub (mem_image_of_mem _ hy), hf.apply_inv hy'⟩
  · have hc₁ : η₁ u ∉ interior (η₁ '' Icc a b) := by
      intro h
      rw [← hI] at h
      exact hc ((hf.mem_image_iff hsub₂ (hJ hu)).1 h)
    unfold windowDomain
    rw [connectedComponentIn_eq_empty hc, connectedComponentIn_eq_empty hc₁, image_empty]

/-- **The times of `T` at which the curves visit the window domains are the same.** -/
theorem mem_windowDomain_iff (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) {a u b : ℝ}
    (hJ : Icc a b ⊆ T) (hu : u ∈ Icc a b) {t : ℝ} (ht : t ∈ T) :
    η₁ t ∈ windowDomain η₁ a u b ↔ η₂ t ∈ windowDomain η₂ a u b := by
  rw [← hf.image_windowDomain hJ hu]
  exact hf.mem_image_iff ((connectedComponentIn_subset _ _).trans (interior_mono (image_mono hJ))) ht

theorem windowDomain_subset {a b : ℝ} (hJ : Icc a b ⊆ T) (η : C(ℝ, ℂ)) (u : ℝ) :
    windowDomain η a u b ⊆ interior (η '' T) :=
  (connectedComponentIn_subset _ _).trans (interior_mono (image_mono hJ))

/-- **Conformal maps of the open disc onto the window domains** correspond under `f`. -/
theorem exists_openDiscMap_iff (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) {a u b : ℝ}
    (hJ : Icc a b ⊆ T) (hu : u ∈ Icc a b) :
    (∃ φ, IsOpenDiscMap (windowDomain η₁ a u b) φ ∧ φ 0 = η₁ u) ↔
      ∃ φ, IsOpenDiscMap (windowDomain η₂ a u b) φ ∧ φ 0 = η₂ u := by
  have hW := hf.image_windowDomain hJ hu
  have hsub₂ := windowDomain_subset hJ η₂ u
  have hsub₁ := windowDomain_subset hJ η₁ u
  constructor
  · rintro ⟨φ, hφ, h0⟩
    have hmaps : MapsTo φ (ball 0 1) (interior (η₁ '' T)) := fun w hw => hsub₁ (hφ.apply_mem hw)
    refine ⟨hf.inv ∘ φ, ⟨hf.differentiableOn_inv.comp hφ.differentiableOn hmaps,
      fun w hw w' hw' hww => hφ.injOn hw hw' (hf.injOn_inv (hmaps hw) (hmaps hw') hww), ?_⟩, ?_⟩
    · rw [image_comp, hφ.image_ball, ← hW]
      ext x
      constructor
      · rintro ⟨_, ⟨x', hx', rfl⟩, rfl⟩
        rw [hf.inv_apply (hsub₂ hx')]
        exact hx'
      · intro hx
        exact ⟨f x, mem_image_of_mem f hx, hf.inv_apply (hsub₂ hx)⟩
    · have hc : η₁ u ∈ windowDomain η₁ a u b := h0 ▸ hφ.apply_mem (mem_ball_self one_pos)
      rw [← hW] at hc
      obtain ⟨x, hx, hfx⟩ := hc
      have hu₂ : η₂ u ∈ windowDomain η₂ a u b := by
        rw [← hf.mem_image_iff hsub₂ (hJ hu)]
        exact ⟨x, hx, hfx⟩
      rw [Function.comp_apply, h0, ← hf.1 u (hJ hu) (hsub₂ hu₂), hf.inv_apply (hsub₂ hu₂)]
  · rintro ⟨φ, hφ, h0⟩
    have hmaps : MapsTo φ (ball 0 1) (interior (η₂ '' T)) := fun w hw => hsub₂ (hφ.apply_mem hw)
    refine ⟨f ∘ φ, ⟨hf.2.2.2.1.comp hφ.differentiableOn hmaps,
      fun w hw w' hw' hww => hφ.injOn hw hw' (hf.2.2.1 (hmaps hw) (hmaps hw') hww), ?_⟩, ?_⟩
    · rw [image_comp, hφ.image_ball, hW]
    · have hu₂ : η₂ u ∈ windowDomain η₂ a u b := h0 ▸ hφ.apply_mem (mem_ball_self one_pos)
      rw [Function.comp_apply, h0, hf.1 u (hJ hu) (hsub₂ hu₂)]

/-- **The normalized conformal maps of the open disc onto the window domains differ by a rotation after composition
with `f`.** -/
theorem exists_rotation_of_normalized (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) {a u b : ℝ}
    (hJ : Icc a b ⊆ T) (hu : u ∈ Icc a b) {φ₁ φ₂ : ℂ → ℂ}
    (h₁ : IsNormalizedOpenDiscMap (windowDomain η₁ a u b) (η₁ u) φ₁)
    (h₂ : IsNormalizedOpenDiscMap (windowDomain η₂ a u b) (η₂ u) φ₂) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ w ∈ ball (0 : ℂ) 1, f (φ₂ w) = φ₁ (c * w) := by
  have hW := hf.image_windowDomain hJ hu
  have hsub₂ := windowDomain_subset hJ η₂ u
  have hmaps : MapsTo φ₂ (ball 0 1) (interior (η₂ '' T)) := fun w hw => hsub₂ (h₂.isOpenDiscMap.apply_mem hw)
  have hO : IsOpenDiscMap (windowDomain η₁ a u b) (f ∘ φ₂) :=
    ⟨hf.2.2.2.1.comp h₂.isOpenDiscMap.differentiableOn hmaps,
      fun w hw w' hw' hww => h₂.isOpenDiscMap.injOn hw hw' (hf.2.2.1 (hmaps hw) (hmaps hw') hww),
      by rw [image_comp, h₂.isOpenDiscMap.image_ball, hW]⟩
  have hu₂ : η₂ u ∈ windowDomain η₂ a u b := h₂.apply_zero ▸ h₂.isOpenDiscMap.apply_mem (mem_ball_self one_pos)
  have h0 : (f ∘ φ₂) 0 = φ₁ 0 := by
    rw [Function.comp_apply, h₂.apply_zero, h₁.apply_zero, hf.1 u (hJ hu) (hsub₂ hu₂)]
  exact hO.exists_rotation h₁.isOpenDiscMap h0

end IsIntrinsicCurveDecoratedReembedding

end MatedCRT
