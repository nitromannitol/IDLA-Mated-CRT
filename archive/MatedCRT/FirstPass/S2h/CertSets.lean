import MatedCRT.FirstPass.S2h.CertRel

/-!
# Certificate sets: a regular rational basis and the charged balls

A basis ball `U i` is charged by the certificate exactly when it lies in the closure of the contact set, and
the union of the charged balls is the interior of that closure. Everything here is generic (no Green function, no
measure): the contact set `C`, the dense sequence `z` and the predicate `R j` (raw positivity at `z j`) are parameters.
-/

namespace MatedCRT

open MeasureTheory Set Metric

/-- A countable regular basis of `ℂ`: nonempty open sets `U V`, indexed by `ℕ`, such that every open
neighbourhood `O` of a point `x` contains the closure of some `U V ∋ x`. It comes from a countable basis of `ℂ` with the
nonempty members enumerated (Mathlib `TopologicalSpace.exists_countable_basis`, `IsTopologicalBasis.exists_closure_subset`). -/
theorem exists_regular_basis_family :
    ∃ U : ℕ → Set ℂ, (∀ V, IsOpen (U V)) ∧ (∀ V, (U V).Nonempty) ∧
      ∀ O : Set ℂ, IsOpen O → ∀ x ∈ O, ∃ V, x ∈ U V ∧ closure (U V) ⊆ O := by
  obtain ⟨b, hbc, hb0, hbasis⟩ := TopologicalSpace.exists_countable_basis (α := ℂ)
  obtain ⟨t0, ht0, -, -⟩ := hbasis.exists_closure_subset (x := (0 : ℂ)) (s := univ) Filter.univ_mem
  obtain ⟨U, hU⟩ := hbc.exists_eq_range ⟨t0, ht0⟩
  have hmem : ∀ V, U V ∈ b := fun V => by
    rw [hU]
    exact mem_range_self V
  refine ⟨U, fun V => hbasis.isOpen (hmem V), fun V => nonempty_iff_ne_empty.2 fun h => ?_, ?_⟩
  · exact hb0 (by rw [← h]; exact hmem V)
  · intro O hO x hx
    obtain ⟨t, ht, hxt, htO⟩ := hbasis.exists_closure_subset (hO.mem_nhds hx)
    rw [hU] at ht
    obtain ⟨V, rfl⟩ := ht
    exact ⟨V, hxt, htO⟩

/-- **Charged balls.** Let `C` be the contact set, and let the dense sequence `z` carry
the predicates `R j` so that a positive raw value at `z j` puts `z j` in `C` (`hRC`), and every open set meeting `C`
contains some `z j` with `R j` (`hdense`). Then the charged-ball predicate of `U i` holds iff `U i ⊆ closure C`. -/
theorem charged_iff_subset_closure {U : ℕ → Set ℂ} (hopen : ∀ V, IsOpen (U V)) (hne : ∀ V, (U V).Nonempty)
    (hreg : ∀ O : Set ℂ, IsOpen O → ∀ x ∈ O, ∃ V, x ∈ U V ∧ closure (U V) ⊆ O)
    {C : Set ℂ} {z : ℕ → ℂ} {R : ℕ → Prop} (hRC : ∀ j, R j → z j ∈ C)
    (hdense : ∀ O : Set ℂ, IsOpen O → (O ∩ C).Nonempty → ∃ j, z j ∈ O ∧ R j) (i : ℕ) :
    (∀ V : ℕ, closure (U V) ⊆ U i → ∃ j, z j ∈ U V ∧ R j) ↔ U i ⊆ closure C := by
  constructor
  · intro h x hx
    by_contra hxC
    obtain ⟨V, hxV, hVsub⟩ :=
      hreg (U i ∩ (closure C)ᶜ) ((hopen i).inter isClosed_closure.isOpen_compl) x ⟨hx, hxC⟩
    obtain ⟨j, hjV, hRj⟩ := h V (hVsub.trans inter_subset_left)
    have hzcl : z j ∈ closure C := subset_closure (hRC j hRj)
    have hnot : z j ∉ closure C := (hVsub (subset_closure hjV)).2
    exact hnot hzcl
  · intro h V hV
    obtain ⟨x, hx⟩ := hne V
    have hxC : x ∈ closure C := h (hV (subset_closure hx))
    exact hdense (U V) (hopen V) (mem_closure_iff.1 hxC (U V) (hopen V) hx)

/-- **Open charged set.** The interior of the closure of the contact set `C` is the union of
the basis balls `U i` contained in `closure C` (a regular basis: every point of the interior lies in such a ball). -/
theorem interior_closure_eq_iUnion {U : ℕ → Set ℂ} (hopen : ∀ V, IsOpen (U V))
    (hreg : ∀ O : Set ℂ, IsOpen O → ∀ x ∈ O, ∃ V, x ∈ U V ∧ closure (U V) ⊆ O) (C : Set ℂ) :
    interior (closure C) = ⋃ (i : ℕ) (_ : U i ⊆ closure C), U i := by
  ext x
  constructor
  · intro hx
    obtain ⟨V, hxV, hsub⟩ := hreg (interior (closure C)) isOpen_interior x hx
    exact mem_iUnion₂.2 ⟨V, fun y hy => interior_subset (hsub (subset_closure hy)), hxV⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx
    exact interior_maximal hi (hopen i) hxi

end MatedCRT
