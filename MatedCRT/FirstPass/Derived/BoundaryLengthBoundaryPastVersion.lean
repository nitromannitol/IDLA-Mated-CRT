import MatedCRT.FirstPass.Derived.BoundaryLengthBoundaryAE
import MatedCRT.FirstPass.Derived.BoundaryLengthPastBoundaryMeasurable

/-!
# Past-measurable version of the inner boundary

The inner boundary of a random interval has a version measurable with respect
to any sigma-algebra observing its endpoints and the boundary-length path up
to the cutoff.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace MatedCRT

/-- For each fixed mesh vertex, inner-boundary membership has a past-measurable
version. The endpoint bound and the equality with this version hold almost
surely for the ambient measure. -/
theorem exists_past_measurable_innerBoundary_version
    {Ω : Type} [MeasurableSpace Ω] (mPast : MeasurableSpace Ω)
    {P : Measure Ω} {B : Ω → C(ℝ, ℝ × ℝ)} {γ : ℝ}
    (hB : AEMeasurable B P)
    (hBM : MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ (P.map B))
    (s ε : ℝ) (hε : 0 < ε) (j N : ℤ) (hN : ε * N ≤ s)
    (hPast : ∀ t ≤ s, @Measurable Ω (ℝ × ℝ) mPast _ (fun ω => B ω t))
    (α β : Ω → ℝ) (hα : @Measurable Ω ℝ mPast _ α)
    (hβ : @Measurable Ω ℝ mPast _ β)
    (hβN : ∀ᵐ ω ∂P, β ω < ε * ((N : ℝ) + 1)) :
    ∃ E : Set Ω, MeasurableSet[mPast] E ∧
      ∀ᵐ ω ∂P, ω ∈ E ↔
        (α ω ≤ ε * j ∧ ε * j ≤ β ω) ∧
        ∃ k : ℤ, ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
          bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k ≠ 0 := by
  by_cases hj : j ≤ N
  · let E : Set Ω := {ω |
      (α ω ≤ ε * j ∧ ε * j ≤ β ω) ∧
      ((∃ k : ℤ, k ≤ N ∧ ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
        bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k ≠ 0) ∨
      (∀ u ∈ Icc (ε * j) (ε * N),
        sInf ((fun t => (B ω t).1) '' Icc (ε * j - ε) (ε * j)) ≤ (B ω u).1) ∨
      (∀ u ∈ Icc (ε * j) (ε * N),
        sInf ((fun t => (B ω t).2) '' Icc (ε * j - ε) (ε * j)) ≤ (B ω u).2))}
    have hE : MeasurableSet[mPast] E := by
      let : MeasurableSpace Ω := mPast
      have hmem : MeasurableSet {ω | α ω ≤ ε * j ∧ ε * j ≤ β ω} :=
        (measurableSet_le hα measurable_const).inter (measurableSet_le measurable_const hβ)
      exact hmem.inter (measurableSet_pastBoundaryCandidate B s ε hPast hε.le j N hj hN α β hα hβ)
    refine ⟨E, hE, ?_⟩
    filter_upwards [ae_outside_bmEdge_iff_past_or_protected hB hBM, hβN] with ω hcrit hbound
    exact and_congr Iff.rfl (hcrit ε (α ω) (β ω) j N hε hj hbound).symm
  · refine ⟨∅, MeasurableSet.empty, ?_⟩
    have hNj : (N : ℝ) + 1 ≤ j := by
      exact_mod_cast (show N + 1 ≤ j by omega)
    have hmesh : ε * ((N : ℝ) + 1) ≤ ε * j :=
      mul_le_mul_of_nonneg_left hNj hε.le
    filter_upwards [hβN] with ω hbound
    simp only [mem_empty_iff_false, false_iff, not_and]
    intro hmem
    exact False.elim (not_le_of_gt (lt_of_lt_of_le hbound hmesh) hmem.2)

end MatedCRT
