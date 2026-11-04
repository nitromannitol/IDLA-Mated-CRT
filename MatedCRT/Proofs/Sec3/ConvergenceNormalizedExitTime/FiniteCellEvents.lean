import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CompactProjection

/-! Measurable events involving finitely many curve cells. -/

namespace MatedCRT

open Set MeasureTheory Topology Metric
open scoped BigOperators

private theorem finset_prod_pos_iff_of_nonneg {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (0 < ∏ i ∈ s, f i) ↔ ∀ i ∈ s, 0 < f i := by
  constructor
  · intro h i hi
    have hn := (Finset.prod_ne_zero_iff.mp (ne_of_gt h)) i hi
    exact lt_of_le_of_ne (hf i hi) (Ne.symm hn)
  · exact Finset.prod_pos

/-- The set of curves for which a compact set contains two nearby points in
specified cells, avoiding finitely many other cells, is measurable. -/
theorem measurableSet_exists_pair_mem_cells_avoiding
    (ε δ : ℝ) (a b : ℤ) (L R : Finset ℤ) (K : Set ℂ) (hK : IsCompact K)
    (hI : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty) :
    MeasurableSet {η : C(ℝ, ℂ) | ∃ x ∈ K, ∃ y ∈ K,
      x ∈ cell ε η a ∧ y ∈ cell ε η b ∧ dist x y < δ ∧
      (∀ j ∈ L, x ∉ cell ε η j) ∧ (∀ j ∈ R, y ∉ cell ε η j)} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let pointL : (C(ℝ, ℂ) × (K × K)) → C(ℝ, ℂ) × ℂ :=
    fun p => (p.1, p.2.1)
  let pointR : (C(ℝ, ℂ) × (K × K)) → C(ℝ, ℂ) × ℂ :=
    fun p => (p.1, p.2.2)
  have hpL : Continuous pointL := continuous_fst.prodMk
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hpR : Continuous pointR := continuous_fst.prodMk
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  let F : Set (C(ℝ, ℂ) × (K × K)) :=
    pointL ⁻¹' {p | p.2 ∈ cell ε p.1 a} ∩
      pointR ⁻¹' {p | p.2 ∈ cell ε p.1 b}
  have hF : IsClosed F := ((isClosed_curve_cell_graph ε a).preimage hpL).inter
    ((isClosed_curve_cell_graph ε b).preimage hpR)
  let dL := fun p => ∏ j ∈ L, curveCellDistance ε j (pointL p)
  let dR := fun p => ∏ j ∈ R, curveCellDistance ε j (pointR p)
  have hdL : Continuous dL := by
    exact continuous_finsetProd _ fun j _ => (continuous_curveCellDistance ε j).comp hpL
  have hdR : Continuous dR := by
    exact continuous_finsetProd _ fun j _ => (continuous_curveCellDistance ε j).comp hpR
  let g := fun p : C(ℝ, ℂ) × (K × K) =>
    min (δ - dist (pointL p).2 (pointR p).2) (min (dL p) (dR p))
  have hg : Continuous g := (continuous_const.sub ((continuous_snd.comp hpL).dist
    (continuous_snd.comp hpR))).min (hdL.min hdR)
  have hm := measurableSet_exists_mem_closed_pos F hF g hg
  convert hm using 1
  ext η
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, y, hy, hxa, hyb, hxy, hL, hR⟩
    refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ⟨hxa, hyb⟩, ?_⟩
    apply lt_min (sub_pos.mpr hxy)
    apply lt_min
    · exact Finset.prod_pos fun j hj => (curveCellDistance_pos_iff ε j (hI j) _).mpr (hL j hj)
    · exact Finset.prod_pos fun j hj => (curveCellDistance_pos_iff ε j (hI j) _).mpr (hR j hj)
  · rintro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, ⟨hxa, hyb⟩, hpos⟩
    have hxy := (lt_min_iff.mp hpos).1
    have hLR := lt_min_iff.mp (lt_min_iff.mp hpos).2
    refine ⟨x, hx, y, hy, hxa, hyb, sub_pos.mp hxy, ?_, ?_⟩
    · have hn : ∀ j ∈ L, 0 ≤ curveCellDistance ε j (η, x) := by
        intro j hj
        rw [curveCellDistance_eq_infDist ε j (hI j)]
        exact infDist_nonneg
      intro j hj
      exact (curveCellDistance_pos_iff ε j (hI j) _).mp
        ((finset_prod_pos_iff_of_nonneg L _ hn).mp hLR.1 j hj)
    · have hn : ∀ j ∈ R, 0 ≤ curveCellDistance ε j (η, y) := by
        intro j hj
        rw [curveCellDistance_eq_infDist ε j (hI j)]
        exact infDist_nonneg
      intro j hj
      exact (curveCellDistance_pos_iff ε j (hI j) _).mp
        ((finset_prod_pos_iff_of_nonneg R _ hn).mp hLR.2 j hj)

end MatedCRT
