import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells

/-! # Measurability of cells in the space-filling curve -/

namespace MatedCRT

open Set Filter Topology MeasureTheory

/-- The graph of a cell, viewed as a set of continuous curves and spatial
points, is closed. Compactness of the time interval allows projection. -/
theorem isClosed_curve_cell_graph (ε : ℝ) (k : ℤ) :
    IsClosed {p : C(ℝ, ℂ) × ℂ | p.2 ∈ cell ε p.1 k} := by
  let I : Set ℝ := Icc (ε * (k - 1)) (ε * k)
  let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let B : Set ((C(ℝ, ℂ) × ℂ) × I) := {p | p.1.1 p.2 = p.1.2}
  have heval : Continuous (fun p : (C(ℝ, ℂ) × ℂ) × I => p.1.1 p.2) := by
    exact ContinuousEval.continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have hB : IsClosed B := isClosed_eq heval (continuous_snd.comp continuous_fst)
  have hclosed := isClosedMap_fst_of_compactSpace _ hB
  have heq : Prod.fst '' B = {p : C(ℝ, ℂ) × ℂ | p.2 ∈ cell ε p.1 k} := by
    ext p
    constructor
    · rintro ⟨⟨q, u⟩, hu, rfl⟩
      exact ⟨u, u.property, hu⟩
    · rintro ⟨u, hu, he⟩
      exact ⟨(p, ⟨u, hu⟩), he, rfl⟩
  rwa [heq] at hclosed

/-- The cell-membership relation of a valid environment has a jointly
measurable version, simultaneously in every spatial point. -/
theorem MatedCRTEnv.IsValid.exists_measurable_cell_graph
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ) (k : ℤ) :
    ∃ A : Set (Ω × ℂ), MeasurableSet A ∧
      ∀ᵐ ω ∂S.P, ∀ x, (ω, x) ∈ A ↔ x ∈ cell ε (S.η ω) k := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hc, hbridge⟩ := hS.matingOfTrees
  let A : Set (Ω × ℂ) := (fun p : Ω × ℂ => (η' p.1, p.2)) ⁻¹'
    {p : C(ℝ, ℂ) × ℂ | p.2 ∈ cell ε p.1 k}
  refine ⟨A, ?_, ?_⟩
  · exact (isClosed_curve_cell_graph ε k).measurableSet.preimage
      ((hc.measurable_curves.2.1.comp measurable_fst).prodMk measurable_snd)
  · filter_upwards [hbridge] with ω hη
    intro x
    change x ∈ cell ε (η' ω) k ↔ x ∈ cell ε (S.η ω) k
    rw [hη.1]

/-- The least-index cell containing a point has a jointly measurable version,
simultaneously for all points, under the valid environment assumptions. -/
theorem MatedCRTEnv.IsValid.exists_measurable_vertexOf
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Ω × ℂ → ℤ, Measurable V ∧
      ∀ᵐ ω ∂S.P, ∀ x, V (ω, x) = vertexOf ε (S.η ω) x := by
  classical
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hc, hbridge⟩ := hS.matingOfTrees
  let A : ℤ → Set (Ω × ℂ) := fun k =>
    (fun p : Ω × ℂ => (η' p.1, p.2)) ⁻¹' {p : C(ℝ, ℂ) × ℂ | p.2 ∈ cell ε p.1 k}
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    (isClosed_curve_cell_graph ε k).measurableSet.preimage
      ((hc.measurable_curves.2.1.comp measurable_fst).prodMk measurable_snd)
  let P : (Ω × ℂ) → ℤ → Prop := fun p k => p ∈ A k ∧ ∀ j < k, p ∉ A j
  have hP : ∀ k, MeasurableSet {p | P p k} := by
    intro k
    convert (hA k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun (_ : j < k) => (hA j).compl) using 1
    ext p
    simp [P]
  let Q : (Ω × ℂ) → ℕ → Prop := fun p n => P p (Tightness.intEnum n)
  have hchoice : ∀ p, ∃ n, Q p n ∨ ¬∃ n, Q p n := by
    intro p
    by_cases h : ∃ n, Q p n
    · obtain ⟨n, hn⟩ := h
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr h⟩
  have hexists : MeasurableSet {p | ∃ n, Q p n} := by
    convert MeasurableSet.iUnion (fun n => hP (Tightness.intEnum n)) using 1
    ext p
    simp [Q]
  have hfind : Measurable (fun p => Nat.find (hchoice p)) :=
    measurable_find hchoice (fun n => (hP _).union hexists.compl)
  let V : Ω × ℂ → ℤ := fun p => Tightness.intEnum (Nat.find (hchoice p))
  refine ⟨V, (measurable_of_countable Tightness.intEnum).comp hfind, ?_⟩
  filter_upwards [hbridge, hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hη hp harea
  intro x
  let a : ℤ := vertexOf ε (S.η ω) x
  have hcell : x ∈ cell ε (S.η ω) a :=
    Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x
  have hfinite : {j : ℤ | x ∈ cell ε (S.η ω) j}.Finite :=
    (Tightness.cellVertices_finite harea.1 hp hε (Bornology.isBounded_singleton (x := x))).subset
      (fun j hj => ⟨x, hj, rfl⟩)
  have hleast : ∀ j, x ∈ cell ε (S.η ω) j → a ≤ j := fun j hj => csInf_le hfinite.bddBelow hj
  have hPa : P (ω, x) a := by
    constructor
    · change x ∈ cell ε (η' ω) a
      rw [hη.1]
      exact hcell
    · intro j hj hmem
      have hjcell : x ∈ cell ε (S.η ω) j := by
        change x ∈ cell ε (η' ω) j at hmem
        rwa [hη.1] at hmem
      exact (not_le_of_gt hj) (hleast j hjcell)
  obtain ⟨n, hn⟩ := Tightness.intEnum_surjective a
  have hQ : ∃ n, Q (ω, x) n := ⟨n, by simpa [Q, hn] using hPa⟩
  have hspec := Nat.find_spec (hchoice (ω, x))
  have hPv : P (ω, x) (V (ω, x)) := hspec.resolve_right (fun h => h hQ)
  have hvcell : x ∈ cell ε (S.η ω) (V (ω, x)) := by
    have hmem := hPv.1
    change x ∈ cell ε (η' ω) (V (ω, x)) at hmem
    rwa [hη.1] at hmem
  apply le_antisymm ?_ (hleast _ hvcell)
  by_contra h
  exact hPv.2 a (lt_of_not_ge h) hPa.1

end MatedCRT
