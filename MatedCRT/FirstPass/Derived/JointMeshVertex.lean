import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentVertex

/-! # Joint measurability of the cell containing a point -/

set_option autoImplicit false

namespace MatedCRT

open Set Filter Topology MeasureTheory

/-- The cell-membership graph is closed jointly in positive mesh, curve and point. -/
theorem isClosed_jointMesh_cell_graph (k : ℤ) :
    IsClosed {p : {ε : ℝ // 0 < ε} × C(ℝ, ℂ) × ℂ |
      p.2.2 ∈ cell p.1.1 p.2.1 k} := by
  let I : Set ℝ := Icc 0 1
  let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let E := {ε : ℝ // 0 < ε} × C(ℝ, ℂ) × ℂ
  let B : Set (E × I) := {p | p.1.2.1 (p.1.1.1 * ((k : ℝ) - 1 + p.2)) = p.1.2.2}
  have ht : Continuous (fun p : E × I => p.1.1.1 * ((k : ℝ) - 1 + p.2)) := by
    dsimp only [E]
    fun_prop
  have heval : Continuous (fun p : E × I =>
      p.1.2.1 (p.1.1.1 * ((k : ℝ) - 1 + p.2))) :=
    ContinuousEval.continuous_eval.comp ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk ht)
  have hB : IsClosed B := isClosed_eq heval (continuous_snd.comp (continuous_snd.comp continuous_fst))
  have hc := isClosedMap_fst_of_compactSpace _ hB
  have heq : Prod.fst '' B = {p : E | p.2.2 ∈ cell p.1.1 p.2.1 k} := by
    ext p
    constructor
    · rintro ⟨⟨q, u⟩, hu, rfl⟩
      refine ⟨q.1.1 * ((k : ℝ) - 1 + u), ?_, hu⟩
      have hε := q.1.2
      have hu0 := u.property.1
      have hu1 := u.property.2
      constructor <;> nlinarith
    · rintro ⟨t, ht, he⟩
      let u : ℝ := t / p.1.1 - ((k : ℝ) - 1)
      have hε := p.1.2
      have hu0 : 0 ≤ u := by
        have h : (k : ℝ) - 1 ≤ t / p.1.1 := (le_div_iff₀ hε).2 (by simpa [mul_comm] using ht.1)
        dsimp [u]; linarith
      have hu1 : u ≤ 1 := by
        have h : t / p.1.1 ≤ (k : ℝ) := (div_le_iff₀ hε).2 (by simpa [mul_comm] using ht.2)
        dsimp [u]; linarith
      have hut : p.1.1 * ((k : ℝ) - 1 + u) = t := by
        dsimp [u]
        field_simp [ne_of_gt hε]; ring
      refine ⟨(p, ⟨u, hu0, hu1⟩), ?_, rfl⟩
      change p.2.1 (p.1.1 * ((k : ℝ) - 1 + u)) = p.2.2
      rwa [hut]
  rwa [heq] at hc

/-- A Borel selector agrees with the least cell index for every positive mesh and
proper surjective continuous curve. -/
theorem exists_measurable_jointMesh_vertexOf :
    ∃ V : {ε : ℝ // 0 < ε} × C(ℝ, ℂ) × ℂ → ℤ, Measurable V ∧
      ∀ (ε : {ε : ℝ // 0 < ε}) (η : C(ℝ, ℂ)) (x : ℂ),
        Tendsto η (cocompact ℝ) (cocompact ℂ) → Function.Surjective η →
          V (ε, η, x) = vertexOf ε.1 η x := by
  classical
  let E := {ε : ℝ // 0 < ε} × C(ℝ, ℂ) × ℂ
  let A : ℤ → Set E := fun k => {p | p.2.2 ∈ cell p.1.1 p.2.1 k}
  have hA : ∀ k, MeasurableSet (A k) := fun k => (isClosed_jointMesh_cell_graph k).measurableSet
  let P : E → ℤ → Prop := fun p k => p ∈ A k ∧ ∀ j < k, p ∉ A j
  have hP : ∀ k, MeasurableSet {p | P p k} := by
    intro k
    convert (hA k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun (_ : j < k) => (hA j).compl) using 1
    ext p
    simp [P]
  let Q : E → ℕ → Prop := fun p n => P p (Tightness.intEnum n)
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
  let V : E → ℤ := fun p => Tightness.intEnum (Nat.find (hchoice p))
  refine ⟨V, (measurable_of_countable Tightness.intEnum).comp hfind, ?_⟩
  intro ε η x hp hsurj
  let a : ℤ := vertexOf ε.1 η x
  have hcell : x ∈ cell ε.1 η a :=
    Tightness.mem_cell_vertexOf η.continuous hp hsurj ε.2 x
  have hfinite : {j : ℤ | x ∈ cell ε.1 η j}.Finite :=
    (Tightness.cellVertices_finite η.continuous hp ε.2 (Bornology.isBounded_singleton (x := x))).subset
      (fun j hj => ⟨x, hj, rfl⟩)
  have hleast : ∀ j, x ∈ cell ε.1 η j → a ≤ j := fun j hj => csInf_le hfinite.bddBelow hj
  have hPa : P (ε, η, x) a := by
    constructor
    · exact hcell
    · intro j hj hmem
      exact (not_le_of_gt hj) (hleast j hmem)
  obtain ⟨n, hn⟩ := Tightness.intEnum_surjective a
  have hQ : ∃ n, Q (ε, η, x) n := ⟨n, by simpa [Q, hn] using hPa⟩
  have hspec := Nat.find_spec (hchoice (ε, η, x))
  have hPv : P (ε, η, x) (V (ε, η, x)) := hspec.resolve_right (fun h => h hQ)
  have hvcell : x ∈ cell ε.1 η (V (ε, η, x)) := hPv.1
  apply le_antisymm ?_ (hleast _ hvcell)
  by_contra h
  exact hPv.2 a (lt_of_not_ge h) hPa.1

end MatedCRT
