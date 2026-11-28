import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Order.IntermediateValue
import MatedCRT.FirstPass.Derived.CellSideMult

/-!
# Sets covered by countably many compact totally disconnected sets contain no continuum

* `isTotallyDisconnected_of_interior_eq_empty`: a subset of the line with empty interior is totally disconnected (a
  connected subset of the line with two points contains the interval between them).
* `isTotallyDisconnected_image_of_injOn`: a continuous injective image of a compact totally disconnected subset of the
  line in the plane is totally disconnected (the map is a homeomorphism onto its image).
* `not_containsNondegenerateContinuum_of_subset_biUnion`: a subset of the plane covered by countably many compact
  totally disconnected sets contains no continuum of positive diameter. By Baire's theorem on the continuum `K`, one
  member `F` of the cover contains a relatively open part of `K` around some `x`; a clopen neighbourhood of `x` in `F`
  inside a small ball around `x` then cuts out a nonempty proper clopen subset of `K`.
-/

set_option autoImplicit false

open Set Metric Topology TopologicalSpace

namespace MatedCRT.PeanosphereTriplePoints

/-- A subset of the line with empty interior is totally disconnected. -/
theorem isTotallyDisconnected_of_interior_eq_empty {E : Set ℝ} (hE : interior E = ∅) :
    IsTotallyDisconnected E := by
  intro t hts ht x hx y hy
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have hsub : Icc x y ⊆ E := (ht.ordConnected.out hx hy).trans hts
    have hint : Ioo x y ⊆ interior E := interior_maximal (Ioo_subset_Icc_self.trans hsub) isOpen_Ioo
    rw [hE] at hint
    exact (nonempty_Ioo.2 hlt).ne_empty (subset_empty_iff.1 hint)
  · have hsub : Icc y x ⊆ E := (ht.ordConnected.out hy hx).trans hts
    have hint : Ioo y x ⊆ interior E := interior_maximal (Ioo_subset_Icc_self.trans hsub) isOpen_Ioo
    rw [hE] at hint
    exact (nonempty_Ioo.2 hlt).ne_empty (subset_empty_iff.1 hint)

/-- A continuous injective image of a compact totally disconnected subset of the line in the plane is totally
disconnected. -/
theorem isTotallyDisconnected_image_of_injOn {E : Set ℝ} (hE : IsCompact E) (hd : IsTotallyDisconnected E)
    {f : ℝ → ℂ} (hf : ContinuousOn f E) (hinj : InjOn f E) : IsTotallyDisconnected (f '' E) := by
  have : CompactSpace E := isCompact_iff_compactSpace.1 hE
  have : TotallyDisconnectedSpace E := totallyDisconnectedSpace_subtype_iff.2 hd
  have hemb : IsEmbedding (E.domRestrict f) :=
    (hf.domRestrict.isClosedEmbedding hinj.injective).isEmbedding
  have h : IsTotallyDisconnected (range (E.domRestrict f)) :=
    hemb.isTotallyDisconnected_range.2 inferInstance
  rw [Set.image_eq_range]
  exact h

/-- **A subset of the plane covered by countably many compact totally disconnected sets contains no continuum of
positive diameter.** -/
theorem not_containsNondegenerateContinuum_of_subset_biUnion {C : Set ℂ} {S : Set (Set ℂ)}
    (hS : S.Countable) (hF : ∀ F ∈ S, IsCompact F ∧ IsTotallyDisconnected F)
    (hC : C ⊆ ⋃ F ∈ S, F) : ¬ ContainsNondegenerateContinuum C := by
  rintro ⟨K, hKC, hKc, hKconn, hdiam⟩
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have : Nonempty K := hKconn.nonempty.to_subtype
  have : ConnectedSpace K := isConnected_iff_connectedSpace.1 hKconn
  have : Countable S := hS.to_subtype
  -- Baire: one member of the cover contains a relatively open part of `K`
  let g : S → Set K := fun F => (Subtype.val : K → ℂ) ⁻¹' (F : Set ℂ)
  have hg_closed : ∀ F, IsClosed (g F) := fun F =>
    (hF F F.2).1.isClosed.preimage continuous_subtype_val
  have hg_cover : ⋃ F, g F = univ := by
    refine eq_univ_of_forall fun k => ?_
    obtain ⟨F, hFS, hkF⟩ := mem_iUnion₂.1 (hC (hKC k.2))
    exact mem_iUnion.2 ⟨⟨F, hFS⟩, hkF⟩
  obtain ⟨⟨F, hFS⟩, k₀, hk₀⟩ := nonempty_interior_of_iUnion_of_closed hg_closed hg_cover
  obtain ⟨O, hOsub, hOopen, hk₀O⟩ := mem_interior.1 hk₀
  obtain ⟨O', hO'open, rfl⟩ := isOpen_induced_iff.1 hOopen
  set x : ℂ := (k₀ : ℂ) with hx
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.1 hO'open x hk₀O
  -- a radius small enough for the part of `K` in the ball to lie in `F`, and for `K` to leave the ball
  set ε : ℝ := min ε₁ (diam K / 3) with hε
  have hε0 : 0 < ε := lt_min hε₁ (by positivity)
  have hKF : ∀ k : K, (k : ℂ) ∈ ball x ε → (k : ℂ) ∈ F := fun k hk =>
    hOsub (show k ∈ Subtype.val ⁻¹' O' from hball₁ (ball_subset_ball (min_le_left _ _) hk))
  have hleave : ∃ k : K, (k : ℂ) ∉ ball x ε := by
    by_contra hall
    push Not at hall
    have hsub : K ⊆ closedBall x ε := fun z hz => ball_subset_closedBall (hall ⟨z, hz⟩)
    have hle := (diam_mono hsub isBounded_closedBall).trans (diam_closedBall hε0.le)
    have : ε ≤ diam K / 3 := min_le_right _ _
    linarith
  -- a clopen neighbourhood of `x` in `F` inside the ball
  have hxF : x ∈ F := hKF k₀ (mem_ball_self hε0)
  have : CompactSpace F := isCompact_iff_compactSpace.1 (hF F hFS).1
  have : TotallyDisconnectedSpace F := totallyDisconnectedSpace_subtype_iff.2 (hF F hFS).2
  obtain ⟨V, hVmem, hxV, hVball⟩ := (isTopologicalBasis_isClopen (X := F)).exists_subset_of_mem_open
    (show (⟨x, hxF⟩ : F) ∈ (Subtype.val : F → ℂ) ⁻¹' ball x ε from mem_ball_self hε0)
    (isOpen_ball.preimage continuous_subtype_val)
  have hVclopen : IsClopen V := hVmem
  obtain ⟨U, hUopen, hUV⟩ := isOpen_induced_iff.1 hVclopen.isOpen
  -- the trace of `V` on `K` is clopen in `K`
  set W : Set ℂ := (Subtype.val : F → ℂ) '' V with hW
  have hWclosed : IsClosed W :=
    (hVclopen.isClosed.isCompact.image continuous_subtype_val).isClosed
  set A : Set K := (Subtype.val : K → ℂ) ⁻¹' W with hA
  have hAclosed : IsClosed A := hWclosed.preimage continuous_subtype_val
  have hAopen : IsOpen A := by
    have hAeq : A = (Subtype.val : K → ℂ) ⁻¹' (U ∩ ball x ε) := by
      ext k
      simp only [hA, hW, mem_preimage, mem_image, mem_inter_iff]
      constructor
      · rintro ⟨w, hwV, hwk⟩
        refine ⟨?_, ?_⟩
        · have : w ∈ (Subtype.val : F → ℂ) ⁻¹' U := by rw [hUV]; exact hwV
          rwa [mem_preimage, hwk] at this
        · have := hVball hwV
          rwa [mem_preimage, hwk] at this
      · rintro ⟨hkU, hkB⟩
        refine ⟨⟨k, hKF k hkB⟩, ?_, rfl⟩
        rw [← hUV]
        exact hkU
    rw [hAeq]
    exact (hUopen.inter isOpen_ball).preimage continuous_subtype_val
  have hAne : A.Nonempty := ⟨k₀, ⟨⟨x, hxF⟩, hxV, rfl⟩⟩
  have hAne' : A ≠ univ := by
    obtain ⟨k, hk⟩ := hleave
    intro hAu
    have hkA : k ∈ A := hAu ▸ mem_univ k
    obtain ⟨w, hwV, hwk⟩ := hkA
    exact hk (hwk ▸ hVball hwV)
  rcases isClopen_iff.1 ⟨hAclosed, hAopen⟩ with h | h
  · exact hAne.ne_empty h
  · exact hAne' h

end MatedCRT.PeanosphereTriplePoints
