import MatedCRT.FirstPass.Derived.BoundaryLengthBoundarySetVersion
import MatedCRT.FirstPass.Derived.BoundaryLengthRecenteredEdges

/-!
# Boundary determined by recentered boundary lengths

A random interval's inner boundary has a measurable version from recentered
past increments and the interval endpoints.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace MatedCRT

/-- A random interval's inner boundary has a version measurable from recentered
past increments and the interval endpoints. -/
theorem exists_increment_measurable_innerBoundary_set_version
    {Ω : Type} [MeasurableSpace Ω] (mPast : MeasurableSpace Ω)
    {P : Measure Ω} {B : Ω → C(ℝ, ℝ × ℝ)} {γ : ℝ}
    (hB : AEMeasurable B P)
    (hBM : MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ (P.map B))
    (s ε : ℝ) (hε : 0 < ε) (N : ℤ) (hN : ε * N ≤ s)
    (hPast : ∀ t ≤ s, @Measurable Ω (ℝ × ℝ) mPast _ (fun ω => B ω t - B ω s))
    (α β : Ω → ℝ) (hα : @Measurable Ω ℝ mPast _ α)
    (hβ : @Measurable Ω ℝ mPast _ β)
    (hβN : ∀ᵐ ω ∂P, β ω < ε * ((N : ℝ) + 1)) :
    ∃ S : Ω → Set ℤ, @Measurable Ω (Set ℤ) mPast _ S ∧
      ∀ᵐ ω ∂P, S ω = LatticeProb.Graph.innerBoundary
        (adjGraph (bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2)))
        {j : ℤ | α ω ≤ ε * j ∧ ε * j ≤ β ω} := by
  let D : Ω → C(ℝ, ℝ × ℝ) := fun ω =>
    ⟨fun t => B ω t - B ω s, (B ω).continuous.sub continuous_const⟩
  have hD : ∀ t ≤ s, @Measurable Ω (ℝ × ℝ) mPast _ (fun ω => D ω t) := hPast
  have hL := ae_of_ae_map hB (ae_exists_lrCoord_lt_of_isCorrelatedBM2 hBM 0)
  have hR := ae_of_ae_map hB (ae_exists_lrCoord_lt_of_isCorrelatedBM2 hBM 1)
  have hversions : ∀ j : ℤ, ∃ E : Set Ω, MeasurableSet[mPast] E ∧
      ∀ᵐ ω ∂P, ω ∈ E ↔
        (α ω ≤ ε * j ∧ ε * j ≤ β ω) ∧
        ∃ k : ℤ, ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
          bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k ≠ 0 := by
    intro j
    by_cases hj : j ≤ N
    · let E : Set Ω := {ω |
        (α ω ≤ ε * j ∧ ε * j ≤ β ω) ∧
        ((∃ k : ℤ, k ≤ N ∧ ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
          bmEdgeCount ε (fun t => (D ω t).1) (fun t => (D ω t).2) j k ≠ 0) ∨
        (∀ u ∈ Icc (ε * j) (ε * N),
          sInf ((fun t => (D ω t).1) '' Icc (ε * j - ε) (ε * j)) ≤ (D ω u).1) ∨
        (∀ u ∈ Icc (ε * j) (ε * N),
          sInf ((fun t => (D ω t).2) '' Icc (ε * j - ε) (ε * j)) ≤ (D ω u).2))}
      have hE : MeasurableSet[mPast] E := by
        let : MeasurableSpace Ω := mPast
        have hmem : MeasurableSet {ω | α ω ≤ ε * j ∧ ε * j ≤ β ω} :=
          (measurableSet_le hα measurable_const).inter (measurableSet_le measurable_const hβ)
        exact hmem.inter (measurableSet_pastBoundaryCandidate D s ε hD hε.le j N hj hN α β hα hβ)
      refine ⟨E, hE, ?_⟩
      filter_upwards [hL, hR, hβN] with ω hL hR hbound
      have hLdip : ∀ q a : ℝ, ∃ t ≥ a, (D ω t).1 < q := by
        intro q a
        obtain ⟨t, ht, hlt⟩ := (hL (q + (B ω s).1) a).1
        refine ⟨t, ht, ?_⟩
        change (B ω t).1 - (B ω s).1 < q
        change (B ω t).1 < q + (B ω s).1 at hlt
        linarith
      have hRdip : ∀ q a : ℝ, ∃ t ≥ a, (D ω t).2 < q := by
        intro q a
        obtain ⟨t, ht, hlt⟩ := (hR (q + (B ω s).2) a).1
        refine ⟨t, ht, ?_⟩
        change (B ω t).2 - (B ω s).2 < q
        change (B ω t).2 < q + (B ω s).2 at hlt
        linarith
      have hc := exists_outside_bmEdge_iff_past_or_protected (α := α ω) (β := β ω) hε
        (continuous_fst.comp (D ω).continuous) (continuous_snd.comp (D ω).continuous)
        hj hbound
        (hLdip _ _) (hRdip _ _)
      have hedge : ∀ k, bmEdgeCount ε (fun t => (D ω t).1) (fun t => (D ω t).2) j k =
          bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k := by
        intro k
        exact bmEdgeCount_sub_const hε (B ω).continuous.fst (B ω).continuous.snd
          (B ω s).1 (B ω s).2 j k
      simp only [E, mem_ofPred_eq]
      rw [and_congr_right_iff]
      intro _
      simp only [hedge]
      simp only [Function.comp_def, hedge] at hc
      exact hc.symm
    · refine ⟨∅, MeasurableSet.empty, ?_⟩
      have hNj : (N : ℝ) + 1 ≤ j := by
        exact_mod_cast (show N + 1 ≤ j by omega)
      have hmesh : ε * ((N : ℝ) + 1) ≤ ε * j :=
        mul_le_mul_of_nonneg_left hNj hε.le
      filter_upwards [hβN] with ω hbound
      simp only [mem_empty_iff_false, false_iff, not_and]
      intro hmem
      exact False.elim (not_le_of_gt (lt_of_lt_of_le hbound hmesh) hmem.2)
  choose E hEm hE using hversions
  refine ⟨fun ω => {j | ω ∈ E j}, ?_, ?_⟩
  · let : MeasurableSpace Ω := mPast
    exact measurable_pi_iff.2 fun j => measurableSet_setOfPred.1 (hEm j)
  · filter_upwards [ae_all_iff.2 hE] with ω hω
    ext j
    change (ω ∈ E j) ↔ j ∈ LatticeProb.Graph.innerBoundary
      (adjGraph (bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2)))
      {j : ℤ | α ω ≤ ε * j ∧ ε * j ≤ β ω}
    rw [hω j]
    change _ ↔ (α ω ≤ ε * j ∧ ε * j ≤ β ω) ∧
      ∃ k : ℤ, ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
        (adjGraph (bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2))).Adj j k
    simp only [adjGraph_adj_iff (bmEdgeCount_symm ε _ _)]
    constructor
    · rintro ⟨hj, k, hk, he⟩
      exact ⟨hj, k, hk, fun h => hk (h ▸ hj), he⟩
    · rintro ⟨hj, k, hk, _, he⟩
      exact ⟨hj, k, hk, he⟩

end MatedCRT
