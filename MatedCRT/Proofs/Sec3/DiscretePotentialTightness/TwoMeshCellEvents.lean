import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.FiniteCellEvents

/-! # Measurable overlap events for cells from two meshes -/

namespace MatedCRT

open Set MeasureTheory Topology Metric
open scoped BigOperators

/-- A compact set meets two specified cells, avoiding finitely many cells of
    each mesh, in a measurable set of curves. -/
theorem measurableSet_exists_mem_two_mesh_cells_avoiding
    (ε δ : ℝ) (a b : ℤ) (L R : Finset ℤ) (K : Set ℂ) (hK : IsCompact K)
    (hε : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty)
    (hδ : ∀ k : ℤ, (Icc (δ * (k - 1)) (δ * k)).Nonempty) :
    MeasurableSet {η : C(ℝ, ℂ) | ∃ x ∈ K,
      x ∈ cell ε η a ∧ x ∈ cell δ η b ∧
      (∀ j ∈ L, x ∉ cell ε η j) ∧ (∀ j ∈ R, x ∉ cell δ η j)} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let point : (C(ℝ, ℂ) × K) → C(ℝ, ℂ) × ℂ := fun p => (p.1, p.2)
  have hp : Continuous point := continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)
  let F : Set (C(ℝ, ℂ) × K) :=
    point ⁻¹' {p | p.2 ∈ cell ε p.1 a} ∩ point ⁻¹' {p | p.2 ∈ cell δ p.1 b}
  have hF : IsClosed F := ((isClosed_curve_cell_graph ε a).preimage hp).inter
    ((isClosed_curve_cell_graph δ b).preimage hp)
  let dL := fun p => ∏ j ∈ L, curveCellDistance ε j (point p)
  let dR := fun p => ∏ j ∈ R, curveCellDistance δ j (point p)
  have hdL : Continuous dL := continuous_finsetProd _ fun j _ =>
    (continuous_curveCellDistance ε j).comp hp
  have hdR : Continuous dR := continuous_finsetProd _ fun j _ =>
    (continuous_curveCellDistance δ j).comp hp
  have hm := measurableSet_exists_mem_closed_pos F hF (fun p => min (dL p) (dR p))
    (hdL.min hdR)
  convert hm using 1
  ext η
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hxa, hxb, hL, hR⟩
    refine ⟨⟨x, hx⟩, ⟨hxa, hxb⟩, lt_min ?_ ?_⟩
    · exact Finset.prod_pos fun j hj => (curveCellDistance_pos_iff ε j (hε j) _).mpr (hL j hj)
    · exact Finset.prod_pos fun j hj => (curveCellDistance_pos_iff δ j (hδ j) _).mpr (hR j hj)
  · rintro ⟨⟨x, hx⟩, ⟨hxa, hxb⟩, hpos⟩
    have hLR := lt_min_iff.mp hpos
    refine ⟨x, hx, hxa, hxb, ?_, ?_⟩
    · intro j hj
      apply (curveCellDistance_pos_iff ε j (hε j) (η, x)).mp
      have hn : ∀ j ∈ L, 0 ≤ curveCellDistance ε j (η, x) := by
        intro j hj
        rw [curveCellDistance_eq_infDist ε j (hε j)]
        exact infDist_nonneg
      have hne := (Finset.prod_ne_zero_iff.mp (ne_of_gt hLR.1)) j hj
      exact lt_of_le_of_ne (hn j hj) (Ne.symm hne)
    · intro j hj
      apply (curveCellDistance_pos_iff δ j (hδ j) (η, x)).mp
      have hn : ∀ j ∈ R, 0 ≤ curveCellDistance δ j (η, x) := by
        intro j hj
        rw [curveCellDistance_eq_infDist δ j (hδ j)]
        exact infDist_nonneg
      have hne := (Finset.prod_ne_zero_iff.mp (ne_of_gt hLR.2)) j hj
      exact lt_of_le_of_ne (hn j hj) (Ne.symm hne)

/-- A measurable threshold for values assigned to pairs of cells, with a
    lower bound on the cell indices meeting the compact set. -/
theorem measurableSet_bounded_two_mesh_cell_values
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (v : Ω → ℤ → ℤ → ℝ) (hv : ∀ a b, Measurable fun ω => v ω a b)
    (ε δ t : ℝ) (K : Set ℂ) (hK : IsCompact K)
    (hε : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty)
    (hδ : ∀ k : ℤ, (Icc (δ * (k - 1)) (δ * k)).Nonempty) :
    MeasurableSet {ω | ∃ N M a b : ℤ,
      (∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) ∧
      (∀ j < M, ∀ x ∈ K, x ∉ cell δ (η ω) j) ∧ t < v ω a b ∧
      ∃ x ∈ K, x ∈ cell ε (η ω) a ∧ x ∈ cell δ (η ω) b ∧
        (∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∧
        (∀ j ∈ Finset.Ico M b, x ∉ cell δ (η ω) j)} := by
  have hbound' : ∀ e : ℝ, ∀ N : ℤ,
      MeasurableSet {ω | ∀ j < N, ∀ x ∈ K, x ∉ cell e (η ω) j} := by
    intro e N
    have h : ∀ j : ℤ, MeasurableSet {ω | ∀ x ∈ K, x ∉ cell e (η ω) j} := by
      intro j
      convert ((isClosed_curve_cell_meets_compact e j K hK).measurableSet.preimage hη).compl using 1
      ext ω
      simp
    convert MeasurableSet.iInter (fun j : ℤ => MeasurableSet.iInter fun (_ : j < N) => h j) using 1
    ext ω
    simp
  have hpair : ∀ N M a b : ℤ, MeasurableSet {ω | ∃ x ∈ K,
      x ∈ cell ε (η ω) a ∧ x ∈ cell δ (η ω) b ∧
      (∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∧
      (∀ j ∈ Finset.Ico M b, x ∉ cell δ (η ω) j)} := by
    intro N M a b
    exact (measurableSet_exists_mem_two_mesh_cells_avoiding ε δ a b
      (Finset.Ico N a) (Finset.Ico M b) K hK hε hδ).preimage hη
  convert MeasurableSet.iUnion (fun N : ℤ => MeasurableSet.iUnion fun M : ℤ =>
    MeasurableSet.iUnion fun a : ℤ => MeasurableSet.iUnion fun b : ℤ =>
      (hbound' ε N).inter ((hbound' δ M).inter
        ((measurableSet_lt (measurable_const : Measurable (fun _ : Ω => t)) (hv a b)).inter (hpair N M a b)))) using 1
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]

/-- Finite exclusions characterize the least cell of a point whenever a
    lower index bound and a selected cell are available. -/
theorem vertexOf_eq_of_cell_avoiding
    (η : ℝ → ℂ) (ε : ℝ) (K : Set ℂ) (N : ℤ)
    (hN : ∀ j < N, ∀ x ∈ K, x ∉ cell ε η j)
    (hsel : ∀ x ∈ K, x ∈ cell ε η (vertexOf ε η x))
    {x : ℂ} (hx : x ∈ K) {a : ℤ} (ha : x ∈ cell ε η a)
    (hexcl : ∀ j ∈ Finset.Ico N a, x ∉ cell ε η j) : vertexOf ε η x = a := by
  have hbdd : BddBelow {j : ℤ | x ∈ cell ε η j} := by
    refine ⟨N, ?_⟩
    intro j hj
    exact le_of_not_gt (fun hjN => hN j hjN x hx hj)
  apply le_antisymm
  · exact csInf_le hbdd ha
  · by_contra h
    have hlt : vertexOf ε η x < a := lt_of_not_ge h
    by_cases hn : vertexOf ε η x < N
    · exact hN _ hn x hx (hsel x hx)
    · exact hexcl _ (Finset.mem_Ico.mpr ⟨le_of_not_gt hn, hlt⟩) (hsel x hx)

/-- The measurable finite-cell test agrees with the pointwise two-mesh test
    when both least-index cells exist and cell indices are bounded below. -/
theorem bounded_two_mesh_cell_values_iff
    (η : ℝ → ℂ) (v : ℤ → ℤ → ℝ) (ε δ t : ℝ) (K : Set ℂ)
    (hboundε : ∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε η j)
    (hboundδ : ∃ M : ℤ, ∀ j < M, ∀ x ∈ K, x ∉ cell δ η j)
    (hselε : ∀ x ∈ K, x ∈ cell ε η (vertexOf ε η x))
    (hselδ : ∀ x ∈ K, x ∈ cell δ η (vertexOf δ η x)) :
    (∃ x ∈ K, t < v (vertexOf ε η x) (vertexOf δ η x)) ↔
    ∃ N M a b : ℤ, (∀ j < N, ∀ x ∈ K, x ∉ cell ε η j) ∧
      (∀ j < M, ∀ x ∈ K, x ∉ cell δ η j) ∧ t < v a b ∧
      ∃ x ∈ K, x ∈ cell ε η a ∧ x ∈ cell δ η b ∧
        (∀ j ∈ Finset.Ico N a, x ∉ cell ε η j) ∧
        (∀ j ∈ Finset.Ico M b, x ∉ cell δ η j) := by
  classical
  constructor
  · rintro ⟨x, hx, hv⟩
    obtain ⟨N, hN⟩ := hboundε
    obtain ⟨M, hM⟩ := hboundδ
    have hbddε : BddBelow {j : ℤ | x ∈ cell ε η j} := by
      refine ⟨N, ?_⟩
      intro j hj
      exact le_of_not_gt (fun h => hN j h x hx hj)
    have hbddδ : BddBelow {j : ℤ | x ∈ cell δ η j} := by
      refine ⟨M, ?_⟩
      intro j hj
      exact le_of_not_gt (fun h => hM j h x hx hj)
    refine ⟨N, M, vertexOf ε η x, vertexOf δ η x, hN, hM, hv,
      x, hx, hselε x hx, hselδ x hx, ?_, ?_⟩
    · intro j hj hjx
      exact (not_lt_of_ge (csInf_le hbddε hjx)) (Finset.mem_Ico.mp hj).2
    · intro j hj hjx
      exact (not_lt_of_ge (csInf_le hbddδ hjx)) (Finset.mem_Ico.mp hj).2
  · rintro ⟨N, M, a, b, hN, hM, hv, x, hx, ha, hb, hL, hR⟩
    exact ⟨x, hx, by rw [vertexOf_eq_of_cell_avoiding η ε K N hN hselε hx ha hL,
      vertexOf_eq_of_cell_avoiding η δ K M hM hselδ hx hb hR]; exact hv⟩

/-- A measurable version of a strict threshold for a two-mesh field; the
    agreement holds whenever the two selection and lower-bound conditions hold. -/
theorem exists_measurable_two_mesh_cell_values_event
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (v : Ω → ℤ → ℤ → ℝ) (hv : ∀ a b, Measurable fun ω => v ω a b)
    (ε δ t : ℝ) (K : Set ℂ) (hK : IsCompact K)
    (hε : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty)
    (hδ : ∀ k : ℤ, (Icc (δ * (k - 1)) (δ * k)).Nonempty) :
    ∃ A : Set Ω, MeasurableSet A ∧ ∀ ω,
      (∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) →
      (∃ M : ℤ, ∀ j < M, ∀ x ∈ K, x ∉ cell δ (η ω) j) →
      (∀ x ∈ K, x ∈ cell ε (η ω) (vertexOf ε (η ω) x)) →
      (∀ x ∈ K, x ∈ cell δ (η ω) (vertexOf δ (η ω) x)) →
      (ω ∈ A ↔ ∃ x ∈ K, t < v ω (vertexOf ε (η ω) x) (vertexOf δ (η ω) x)) := by
  let A : Set Ω := {ω | ∃ N M a b : ℤ,
      (∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) ∧
      (∀ j < M, ∀ x ∈ K, x ∉ cell δ (η ω) j) ∧ t < v ω a b ∧
      ∃ x ∈ K, x ∈ cell ε (η ω) a ∧ x ∈ cell δ (η ω) b ∧
        (∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∧
        (∀ j ∈ Finset.Ico M b, x ∉ cell δ (η ω) j)}
  refine ⟨A, measurableSet_bounded_two_mesh_cell_values η hη v hv ε δ t K hK hε hδ, ?_⟩
  intro ω hbε hbδ hsε hsδ
  exact (bounded_two_mesh_cell_values_iff (η ω) (v ω) ε δ t K hbε hbδ hsε hsδ).symm

end MatedCRT
