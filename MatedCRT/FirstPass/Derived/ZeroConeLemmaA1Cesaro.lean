import LatticeProb.Euclidean.CappedSquare

/-!
# Capped squares of the exterior mass

For the proof of Lemma A.1 of Gwynne–Miller–Sheffield (arXiv:1705.11161, Appendix A, Step 4; written answer 58,
section 3, fourth paragraph): once the capped square `Ŝ_{m+d}` of a mass `ν` contains a fixed set `K`, and the mass
`ν'` of every square containing `K` is `ν - d`, the capped square of `ν'` at level `m` is `Ŝ_{m+d}`
(`isCappedSquare_of_shift`). With `ν'` the mass outside the closed disc `K` and `d = ν(K)`, this is
`S^k_m = S_{m+d}` of the answer.
-/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace MatedCRT

open LatticeProb.CappedSquare

variable {E : Type*}

/-- **The capped square of the exterior mass is the shifted capped square of the full mass.** -/
theorem isCappedSquare_of_shift {𝒟 : Set (Set E)} {ν ν' : Set E → ℝ≥0∞} {m d : ℝ≥0∞} (hd : d ≠ ⊤) {w : E}
    {K S : Set E} (hnest : ∀ S₁ ∈ 𝒟, ∀ S₂ ∈ 𝒟, w ∈ S₁ → w ∈ S₂ → S₁ ⊆ S₂ ∨ S₂ ⊆ S₁)
    (hrel : ∀ S' ∈ 𝒟, K ⊆ S' → ν S' = ν' S' + d) (h : IsCappedSquare 𝒟 ν (m + d) w S) (hK : K ⊆ S) :
    IsCappedSquare 𝒟 ν' m w S := by
  refine ⟨⟨h.mem_family, h.mem, ?_⟩, fun S' hS' => ?_⟩
  · have hle := h.mass_le
    rw [hrel S h.mem_family hK] at hle
    exact (ENNReal.add_le_add_iff_right hd).1 hle
  · obtain ⟨hS'D, hwS', hS'm⟩ := hS'
    rcases hnest S' hS'D S h.mem_family hwS' h.mem with hsub | hsub
    · exact hsub
    · have hKS' : K ⊆ S' := hK.trans hsub
      refine h.subset hS'D hwS' ?_
      rw [hrel S' hS'D hKS']
      exact add_le_add_left hS'm d

end MatedCRT
