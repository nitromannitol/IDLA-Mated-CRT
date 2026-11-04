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

/-- For fixed mesh and index, the curves whose cell meets a compact set form
a closed set. -/
theorem isClosed_curve_cell_meets_compact (ε : ℝ) (j : ℤ) (K : Set ℂ)
    (hK : IsCompact K) :
    IsClosed {η : C(ℝ, ℂ) | ∃ x ∈ K, x ∈ cell ε η j} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : Set (C(ℝ, ℂ) × K) :=
    (fun p : C(ℝ, ℂ) × K => (p.1, (p.2 : ℂ))) ⁻¹'
      {p | p.2 ∈ cell ε p.1 j}
  have hF : IsClosed F := (isClosed_curve_cell_graph ε j).preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have h := isClosedMap_fst_of_compactSpace _ hF
  convert h using 1
  ext η
  simp only [mem_ofPred_eq, mem_image, Prod.exists]
  constructor
  · rintro ⟨x, hx, hmem⟩
    exact ⟨η, ⟨x, hx⟩, hmem, rfl⟩
  · rintro ⟨η', ⟨x, hx⟩, hmem, rfl⟩
    exact ⟨x, hx, hmem⟩

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

/-- A measurable curve and measurable vertex values give a measurable
oscillation event when all cells meeting the compact set have a common lower
index bound. -/
theorem measurableSet_bounded_index_oscillation
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (u : Ω → ℤ → ℝ) (hu : ∀ a, Measurable fun ω => u ω a)
    (ε δ t : ℝ) (K : Set ℂ) (hK : IsCompact K)
    (hI : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty) :
    MeasurableSet {ω | ∃ N a b : ℤ,
      (∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) ∧
      t < |u ω a - u ω b| ∧
      ∃ x ∈ K, ∃ y ∈ K,
        x ∈ cell ε (η ω) a ∧ y ∈ cell ε (η ω) b ∧ dist x y < δ ∧
        (∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∧
        (∀ j ∈ Finset.Ico N b, y ∉ cell ε (η ω) j)} := by
  have hbound : ∀ N : ℤ, MeasurableSet {ω | ∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j} := by
    intro N
    have h : ∀ j : ℤ, MeasurableSet {ω | ∀ x ∈ K, x ∉ cell ε (η ω) j} := by
      intro j
      convert ((isClosed_curve_cell_meets_compact ε j K hK).measurableSet.preimage hη).compl using 1
      ext ω
      simp
    convert MeasurableSet.iInter (fun j : ℤ => MeasurableSet.iInter fun (_ : j < N) => h j) using 1
    ext ω
    simp
  have hpair : ∀ N a b : ℤ, MeasurableSet {ω | ∃ x ∈ K, ∃ y ∈ K,
      x ∈ cell ε (η ω) a ∧ y ∈ cell ε (η ω) b ∧ dist x y < δ ∧
      (∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∧
      (∀ j ∈ Finset.Ico N b, y ∉ cell ε (η ω) j)} := by
    intro N a b
    exact (measurableSet_exists_pair_mem_cells_avoiding ε δ a b
      (Finset.Ico N a) (Finset.Ico N b) K hK hI).preimage hη
  convert MeasurableSet.iUnion (fun N : ℤ => MeasurableSet.iUnion fun a : ℤ =>
    MeasurableSet.iUnion fun b : ℤ => (hbound N).inter
      ((measurableSet_lt (measurable_const : Measurable (fun _ : Ω => t))
        ((hu a).sub (hu b)).abs).inter (hpair N a b))) using 1
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, Pi.sub_apply]

/-- On a compact region with a lower bound for cell indices, the finite-cell
oscillation event is equivalent to oscillation of the least-index cell map. -/
theorem bounded_index_oscillation_iff
    (η : ℝ → ℂ) (u : ℤ → ℝ) (ε δ t : ℝ) (K : Set ℂ)
    (hbound : ∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε η j)
    (hsel : ∀ x ∈ K, x ∈ cell ε η (vertexOf ε η x)) :
    (∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧
      t < |u (vertexOf ε η x) - u (vertexOf ε η y)|) ↔
    ∃ N a b : ℤ, (∀ j < N, ∀ x ∈ K, x ∉ cell ε η j) ∧
      t < |u a - u b| ∧
      ∃ x ∈ K, ∃ y ∈ K, x ∈ cell ε η a ∧ y ∈ cell ε η b ∧ dist x y < δ ∧
        (∀ j ∈ Finset.Ico N a, x ∉ cell ε η j) ∧
        (∀ j ∈ Finset.Ico N b, y ∉ cell ε η j) := by
  classical
  have hbdd : ∀ N : ℤ, (∀ j < N, ∀ x ∈ K, x ∉ cell ε η j) →
      ∀ x ∈ K, BddBelow {j : ℤ | x ∈ cell ε η j} := by
    intro N hN x hx
    refine ⟨N, ?_⟩
    intro j hj
    exact le_of_not_gt (fun hjN => hN j hjN x hx hj)
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hu⟩
    obtain ⟨N, hN⟩ := hbound
    refine ⟨N, vertexOf ε η x, vertexOf ε η y, hN, hu,
      x, hx, y, hy, hsel x hx, hsel y hy, hxy, ?_, ?_⟩
    · intro j hj hjx
      exact (not_lt_of_ge (csInf_le (hbdd N hN x hx) hjx)) (Finset.mem_Ico.mp hj).2
    · intro j hj hjy
      exact (not_lt_of_ge (csInf_le (hbdd N hN y hy) hjy)) (Finset.mem_Ico.mp hj).2
  · rintro ⟨N, a, b, hN, hu, x, hx, y, hy, hxa, hyb, hxy, hL, hR⟩
    have heq : ∀ x ∈ K, ∀ a : ℤ, x ∈ cell ε η a →
        (∀ j ∈ Finset.Ico N a, x ∉ cell ε η j) → vertexOf ε η x = a := by
      intro z hz k hzk hexcl
      apply le_antisymm
      · exact csInf_le (hbdd N hN z hz) hzk
      · by_contra h
        have hlt : vertexOf ε η z < k := lt_of_not_ge h
        by_cases hn : vertexOf ε η z < N
        · exact hN _ hn z hz (hsel z hz)
        · exact hexcl _ (Finset.mem_Ico.mpr ⟨le_of_not_gt hn, hlt⟩) (hsel z hz)
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    rw [heq x hx a hxa hL, heq y hy b hyb hR]
    exact hu

end MatedCRT
