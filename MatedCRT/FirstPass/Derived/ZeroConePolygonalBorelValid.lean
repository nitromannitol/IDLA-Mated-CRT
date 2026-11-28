import MatedCRT.FirstPass.Derived.ZeroConePolygonalData

/-!
# The validity set of the unit-mesh data is Borel

The polygonal cell configuration of a unit-mesh weighted datum `w = (η, m)` (a curve
`η : C(ℝ, ℂ)` and edge counts `m : ℤ → ℤ → ℕ`) is defined on the validity set `UnitMeshValid`
and by a fixed default configuration off it. For the configuration to be a measurable function of
the datum, as the random cell configurations of Gwynne–Miller–Sheffield (arXiv:1807.07515v3,
Section 1.3) and the comparison of the mesh-`1/n` cells of the `0`-quantum cone with unit-mesh cells
(arXiv:1705.11161v5, Lemma 3.5) require, the validity set must be Borel. This file proves it, for
the compact-open Borel `σ`-algebra on `C(ℝ, ℂ)` and the product of the discrete `σ`-algebras on
`ℤ → ℤ → ℕ`.

Every clause of `UnitMeshValid` is replaced by an equivalent countable test, with the old cells
`K_j = η([j - 1, j])` read through the closed sets of curves defined by a closed condition at some
time of `[j - 1, j]` (the projection along a compact interval is a closed map):

* local finiteness: for every integer `R` only finitely many labels have `K_j` meeting the closed
  ball of radius `R`;
* coverage: under local finiteness the union of the cells is closed, so it suffices that every
  point of a dense sequence lies in some cell;
* positive areas and null overlaps: the membership set `{(w, z) | z ∈ K_j}` is closed, and the area
  of a section of a measurable set is measurable;
* the conditions on `m` are coordinate tests, the condition `m_ij > 0 → K_i ∩ K_j ≠ ∅` is closed in
  the curve;
* the point connectivity of the labels: under local finiteness the label set `{a | z ∈ K_a}` of a
  point is a finite set `F`, the condition depends on `z` only through `F`, and the points with label
  set `F` are those at positive distance from the cells with labels outside `F`; for each margin
  `1/(n + 1)` this is a closed condition, and the chains of positive counts inside `F` form a
  countable union of coordinate tests.

## Main declarations

* `isClosed_setOf_exists_mem_Icc`: a closed condition at some time of a compact interval is closed.
* `UnitMeshValidTest`: the countable form of `UnitMeshValid`.
* `unitMeshValid_iff_test`: the two forms agree.
* `measurable_volume_unitCell`: the area of an old cell is a measurable function of the datum.
* `measurable_reflTransGen`: the reflexive transitive closure of measurable relations on a countable
  type is measurable.
* `measurableSet_unitMeshValid`: **the validity set is Borel**.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology Relation

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS

/-! ### Closed conditions along a compact time interval -/

/-- **A closed condition at some time of a compact interval is closed**: if `{(x, t) | p x t}` is
closed, then so is `{x | ∃ t ∈ [a, b], p x t}`, the projection along the compact factor `[a, b]`
being a closed map. -/
theorem isClosed_setOf_exists_mem_Icc {X : Type*} [TopologicalSpace X] (a b : ℝ) {p : X → ℝ → Prop}
    (hp : IsClosed {q : X × ℝ | p q.1 q.2}) : IsClosed {x | ∃ t ∈ Icc a b, p x t} := by
  have e : {x | ∃ t ∈ Icc a b, p x t} = Prod.fst '' {q : X × Icc a b | p q.1 q.2} := by
    ext x
    constructor
    · rintro ⟨t, ht, hpt⟩
      exact ⟨(x, ⟨t, ht⟩), hpt, rfl⟩
    · rintro ⟨⟨_, t⟩, hpt, rfl⟩
      exact ⟨t, t.2, hpt⟩
  rw [e]
  exact isClosedMap_fst_of_compactSpace _
    (hp.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

/-- A condition `∀ i, c i → p i x` with closed sets `{x | p i x}` is closed. -/
theorem isClosed_setOf_forall_imp {X ι : Type*} [TopologicalSpace X] {c : ι → Prop}
    {p : ι → X → Prop} (h : ∀ i, c i → IsClosed {x | p i x}) :
    IsClosed {x | ∀ i, c i → p i x} := by
  have e : {x | ∀ i, c i → p i x} = ⋂ i, ⋂ (_ : c i), {x | p i x} := by
    ext
    simp only [mem_ofPred_eq, mem_iInter]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun hi => h i hi

/-- The conjunction of two closed conditions is closed. -/
theorem isClosed_setOf_and_of_isClosed {X : Type*} [TopologicalSpace X] {p q : X → Prop}
    (hp : IsClosed {x | p x}) (hq : IsClosed {x | q x}) : IsClosed {x | p x ∧ q x} :=
  hp.inter hq

/-! ### The old cells as images of time intervals -/

/-- A point lies in the old cell `K_j` iff it is `η(t)` for some `t ∈ [j - 1, j]`. -/
theorem mem_unitCell_iff {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} {j : ℤ} {z : Plane} :
    z ∈ unitCell w j ↔
      ∃ t ∈ Icc ((j : ℝ) - 1) j, Complex.orthonormalBasisOneI.repr (w.1 t) = z := by
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t, ?_, rfl⟩
    simpa only [one_mul] using ht
  · rintro ⟨t, ht, rfl⟩
    refine ⟨_, ⟨t, ?_, rfl⟩, rfl⟩
    simpa only [one_mul] using ht

theorem unitCell_inter_closedBall_nonempty_iff {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} {j : ℤ} {R : ℝ} :
    (unitCell w j ∩ closedBall 0 R).Nonempty ↔
      ∃ t ∈ Icc ((j : ℝ) - 1) j, Complex.orthonormalBasisOneI.repr (w.1 t) ∈ closedBall (0 : Plane) R := by
  constructor
  · rintro ⟨_, hz, hR⟩
    obtain ⟨t, ht, rfl⟩ := mem_unitCell_iff.1 hz
    exact ⟨t, ht, hR⟩
  · rintro ⟨t, ht, hR⟩
    exact ⟨_, mem_unitCell_iff.2 ⟨t, ht, rfl⟩, hR⟩

theorem unitCell_inter_nonempty_iff {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} {i j : ℤ} :
    (unitCell w i ∩ unitCell w j).Nonempty ↔
      ∃ s ∈ Icc ((i : ℝ) - 1) i, ∃ t ∈ Icc ((j : ℝ) - 1) j,
        Complex.orthonormalBasisOneI.repr (w.1 s) = Complex.orthonormalBasisOneI.repr (w.1 t) := by
  constructor
  · rintro ⟨_, hi, hj⟩
    obtain ⟨s, hs, rfl⟩ := mem_unitCell_iff.1 hi
    obtain ⟨t, ht, hts⟩ := mem_unitCell_iff.1 hj
    exact ⟨s, hs, t, ht, hts.symm⟩
  · rintro ⟨s, hs, t, ht, e⟩
    exact ⟨_, mem_unitCell_iff.2 ⟨s, hs, rfl⟩, mem_unitCell_iff.2 ⟨t, ht, e.symm⟩⟩

/-- Under local finiteness the old cells form a locally finite family. -/
theorem locallyFinite_unitCell {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}
    (hlf : ∀ A : Set Plane, IsCompact A → {j | (unitCell w j ∩ A).Nonempty}.Finite) :
    LocallyFinite (unitCell w) := fun x =>
  ⟨closedBall x 1, Metric.closedBall_mem_nhds x one_pos, hlf _ (isCompact_closedBall x 1)⟩

/-! ### The countable form of the validity hypotheses -/

/-- **The label test** at the finite label set `F`, the label `i` and the margin `1/(n + 1)`: some
point `z = η(s)` of the old cell `K_i` lies in every old cell `K_a`, `a ∈ F`, and at distance at
least `1/(n + 1)` from every old cell `K_b`, `b ∉ F`. Then the label set of `z` is exactly `F`. -/
def LabelPointTest (F : Finset ℤ) (i : ℤ) (n : ℕ) (f : C(ℝ, ℂ)) : Prop :=
  ∃ s ∈ Icc ((i : ℝ) - 1) i,
    (∀ a ∈ F, ∃ t ∈ Icc ((a : ℝ) - 1) a,
      Complex.orthonormalBasisOneI.repr (f t) = Complex.orthonormalBasisOneI.repr (f s)) ∧
    ∀ b ∉ F, ∀ t ∈ Icc ((b : ℝ) - 1) b,
      1 / ((n : ℝ) + 1) ≤
        dist (Complex.orthonormalBasisOneI.repr (f s)) (Complex.orthonormalBasisOneI.repr (f t))

/-- **The countable form of `UnitMeshValid`**: local finiteness tested on the balls of integer
radius, coverage tested on a dense sequence, positive areas and null overlaps, the coordinate
conditions on `m`, the condition `m_ij > 0 → K_i ∩ K_j ≠ ∅` in terms of times, and the point
connectivity of the labels tested on the finite label sets `F` with the label test. -/
def UnitMeshValidTest (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : Prop :=
  (∀ R : ℕ, ∃ N : ℕ, ∀ j : ℤ,
      (∃ t ∈ Icc ((j : ℝ) - 1) j, Complex.orthonormalBasisOneI.repr (w.1 t) ∈ closedBall (0 : Plane) R) →
        -(N : ℤ) ≤ j ∧ j ≤ N) ∧
    (∀ k : ℕ, ∃ j : ℤ, ∃ t ∈ Icc ((j : ℝ) - 1) j,
      Complex.orthonormalBasisOneI.repr (w.1 t) = TopologicalSpace.denseSeq Plane k) ∧
    (∀ j, 0 < volume (unitCell w j)) ∧
    (∀ i j, i ≠ j → volume (unitCell w i ∩ unitCell w j) = 0) ∧
    (∀ i j, w.2 i j = w.2 j i) ∧
    (∀ j, w.2 j j = 0) ∧
    (∀ i j, 0 < w.2 i j → ∃ s ∈ Icc ((i : ℝ) - 1) i, ∃ t ∈ Icc ((j : ℝ) - 1) j,
      Complex.orthonormalBasisOneI.repr (w.1 s) = Complex.orthonormalBasisOneI.repr (w.1 t)) ∧
    ∀ (F : Finset ℤ) (i j : ℤ) (n : ℕ), i ∈ F → j ∈ F → LabelPointTest F i n w.1 →
      ReflTransGen (fun a b => 0 < w.2 a b ∧ a ∈ F ∧ b ∈ F) i j

/-- Local finiteness of the old cells is local finiteness on the balls of integer radius. -/
theorem lf_iff_forall_nat {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} :
    (∀ A : Set Plane, IsCompact A → {j | (unitCell w j ∩ A).Nonempty}.Finite) ↔
      ∀ R : ℕ, ∃ N : ℕ, ∀ j : ℤ,
        (∃ t ∈ Icc ((j : ℝ) - 1) j,
          Complex.orthonormalBasisOneI.repr (w.1 t) ∈ closedBall (0 : Plane) R) →
          -(N : ℤ) ≤ j ∧ j ≤ N := by
  constructor
  · intro h R
    obtain ⟨N, hN⟩ := ((h _ (isCompact_closedBall (0 : Plane) R)).image Int.natAbs).bddAbove
    refine ⟨N, fun j hj => ?_⟩
    have hjN : j.natAbs ≤ N :=
      hN (mem_image_of_mem _ (unitCell_inter_closedBall_nonempty_iff.2 hj))
    omega
  · intro h A hA
    obtain ⟨r, hr⟩ := hA.isBounded.subset_closedBall (0 : Plane)
    obtain ⟨R, hR⟩ := exists_nat_ge r
    obtain ⟨N, hN⟩ := h R
    refine (Set.finite_Icc (-(N : ℤ)) N).subset fun j hj => ?_
    obtain ⟨z, hzj, hzA⟩ := hj
    exact hN j (unitCell_inter_closedBall_nonempty_iff.1
      ⟨z, hzj, closedBall_subset_closedBall hR (hr hzA)⟩)

/-- Under local finiteness the old cells cover the plane iff they contain a dense sequence. -/
theorem cover_iff_forall_denseSeq {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}
    (hlf : ∀ A : Set Plane, IsCompact A → {j | (unitCell w j ∩ A).Nonempty}.Finite) :
    (∀ z, ∃ j, z ∈ unitCell w j) ↔
      ∀ k : ℕ, ∃ j : ℤ, ∃ t ∈ Icc ((j : ℝ) - 1) j,
        Complex.orthonormalBasisOneI.repr (w.1 t) = TopologicalSpace.denseSeq Plane k := by
  constructor
  · intro h k
    obtain ⟨j, hj⟩ := h (TopologicalSpace.denseSeq Plane k)
    exact ⟨j, mem_unitCell_iff.1 hj⟩
  · intro h z
    have hU : IsClosed (⋃ j, unitCell w j) :=
      (locallyFinite_unitCell hlf).isClosed_iUnion fun j => (isCompact_unitCell w j).isClosed
    have hsub : range (TopologicalSpace.denseSeq Plane) ⊆ ⋃ j, unitCell w j := by
      rintro _ ⟨k, rfl⟩
      obtain ⟨j, hj⟩ := h k
      exact mem_iUnion.2 ⟨j, mem_unitCell_iff.2 hj⟩
    exact mem_iUnion.1 (closure_minimal hsub hU (TopologicalSpace.denseRange_denseSeq Plane z))

/-- **The point connectivity of the labels through the finite label sets**: under local finiteness,
the old cells through each point are joined by chains of positive counts between cells through that
point iff, for every finite label set `F`, every label `i ∈ F` and every margin `1/(n + 1)` passing
the label test, the labels of `F` are joined by chains of positive counts inside `F`. -/
theorem pt_iff_labelPointTest {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}
    (hlf : ∀ A : Set Plane, IsCompact A → {j | (unitCell w j ∩ A).Nonempty}.Finite) :
    (∀ z i j, z ∈ unitCell w i → z ∈ unitCell w j →
      ReflTransGen (fun a b => 0 < w.2 a b ∧ z ∈ unitCell w a ∧ z ∈ unitCell w b) i j) ↔
    ∀ (F : Finset ℤ) (i j : ℤ) (n : ℕ), i ∈ F → j ∈ F → LabelPointTest F i n w.1 →
      ReflTransGen (fun a b => 0 < w.2 a b ∧ a ∈ F ∧ b ∈ F) i j := by
  have hmono : ∀ {r p : ℤ → ℤ → Prop} {a b : ℤ}, ReflTransGen r a b →
      (∀ a b, r a b → p a b) → ReflTransGen p a b := by
    intro _ _ _ _ hab h
    induction hab with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail (h _ _ hbc)
  constructor
  · rintro hpt F i j n hi hj ⟨s, -, hF, hout⟩
    have hmem : ∀ a, Complex.orthonormalBasisOneI.repr (w.1 s) ∈ unitCell w a ↔ a ∈ F := by
      intro a
      refine ⟨fun ha => ?_, fun ha => ?_⟩
      · by_contra haF
        obtain ⟨t, ht, e⟩ := mem_unitCell_iff.1 ha
        have h1 := hout a haF t ht
        rw [e, dist_self] at h1
        have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · obtain ⟨t, ht, e⟩ := hF a ha
        exact mem_unitCell_iff.2 ⟨t, ht, e⟩
    exact hmono (hpt _ i j ((hmem i).2 hi) ((hmem j).2 hj))
      fun a b hab => ⟨hab.1, (hmem a).1 hab.2.1, (hmem b).1 hab.2.2⟩
  · intro hP z i j hi hj
    obtain ⟨F, hF⟩ : ∃ F : Finset ℤ, ∀ a, a ∈ F ↔ z ∈ unitCell w a :=
      ⟨(hlf {z} isCompact_singleton).toFinset, fun a => by
        rw [Set.Finite.mem_toFinset, mem_ofPred_eq, Set.inter_singleton_nonempty]⟩
    obtain ⟨s, hs, hsz⟩ := mem_unitCell_iff.1 hi
    have hD : IsClosed (⋃ b : {b : ℤ // b ∉ F}, unitCell w b) :=
      ((locallyFinite_unitCell hlf).comp_injective Subtype.val_injective).isClosed_iUnion
        fun b => (isCompact_unitCell w b).isClosed
    have hzD : z ∉ ⋃ b : {b : ℤ // b ∉ F}, unitCell w b := by
      rw [mem_iUnion, not_exists]
      exact fun b hb => b.2 ((hF b).2 hb)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD.isOpen_compl z hzD
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine hmono (hP F i j n ((hF i).2 hi) ((hF j).2 hj) ⟨s, hs, fun a ha => ?_, fun b hb t ht => ?_⟩)
      fun a b hab => ⟨hab.1, (hF a).1 hab.2.1, (hF b).1 hab.2.2⟩
    · obtain ⟨t, ht, e⟩ := mem_unitCell_iff.1 ((hF a).1 ha)
      exact ⟨t, ht, e.trans hsz.symm⟩
    · have hmem : Complex.orthonormalBasisOneI.repr (w.1 t) ∈ ⋃ b : {b : ℤ // b ∉ F}, unitCell w b :=
        mem_iUnion.2 ⟨⟨b, hb⟩, mem_unitCell_iff.2 ⟨t, ht, rfl⟩⟩
      have hnot : Complex.orthonormalBasisOneI.repr (w.1 t) ∉ ball z ε := fun h' => hball h' hmem
      rw [mem_ball, not_lt] at hnot
      rw [hsz, dist_comm]
      linarith

/-- **The validity hypotheses and their countable form agree.** -/
theorem unitMeshValid_iff_test {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} :
    UnitMeshValid w ↔ UnitMeshValidTest w := by
  constructor
  · intro h
    exact ⟨lf_iff_forall_nat.1 h.lf, (cover_iff_forall_denseSeq h.lf).1 h.cover, h.volume_pos,
      h.volume_inter, h.m_symm, h.m_diag, fun i j hij => unitCell_inter_nonempty_iff.1 (h.m_inter i j hij),
      (pt_iff_labelPointTest h.lf).1 h.pt⟩
  · rintro ⟨hlf, hcov, hvol, hint, hsymm, hdiag, hm, hpt⟩
    have hlf' := lf_iff_forall_nat.2 hlf
    exact ⟨hvol, hlf', (cover_iff_forall_denseSeq hlf').2 hcov, hint, hsymm, hdiag,
      fun i j hij => unitCell_inter_nonempty_iff.2 (hm i j hij), (pt_iff_labelPointTest hlf').2 hpt⟩

/-! ### Measurability -/

/-- A condition on the curve of a datum which is closed in the compact-open topology is measurable. -/
theorem measurable_of_isClosed_setOf_fst {p : C(ℝ, ℂ) → Prop} (hp : IsClosed {f | p f}) :
    Measurable fun w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => p w.1 := by
  have h : MeasurableSet {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) | p w.1} := measurable_fst hp.measurableSet
  exact measurableSet_setOfPred.1 h

/-- The membership set `{(w, z) | z ∈ K_j}` is measurable (it is closed in the curve and the point). -/
theorem measurableSet_mem_unitCell (j : ℤ) :
    MeasurableSet {q : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × Plane | q.2 ∈ unitCell q.1 j} := by
  have hE : IsClosed {q : C(ℝ, ℂ) × Plane |
      ∃ t ∈ Icc ((j : ℝ) - 1) j, Complex.orthonormalBasisOneI.repr (q.1 t) = q.2} :=
    isClosed_setOf_exists_mem_Icc _ _
      (isClosed_eq (Complex.orthonormalBasisOneI.repr.continuous.comp (by fun_prop)) (by fun_prop))
  have hm : Measurable fun q : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × Plane => (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  convert hE.measurableSet.preimage hm using 1
  ext
  simp only [mem_ofPred_eq, mem_preimage]
  exact mem_unitCell_iff

/-- **The area of an old cell is a measurable function of the datum.** -/
theorem measurable_volume_unitCell (j : ℤ) :
    Measurable fun w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => volume (unitCell w j) :=
  measurable_measure_prodMk_left (ν := (volume : Measure Plane)) (measurableSet_mem_unitCell j)

/-- The area of the overlap of two old cells is a measurable function of the datum. -/
theorem measurable_volume_unitCell_inter (i j : ℤ) :
    Measurable fun w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => volume (unitCell w i ∩ unitCell w j) :=
  measurable_measure_prodMk_left (ν := (volume : Measure Plane))
    ((measurableSet_mem_unitCell i).inter (measurableSet_mem_unitCell j))

/-- **The reflexive transitive closure of measurable relations on a countable type is measurable**:
it is the countable union over the lists `l` of the chains `i :: l` ending at `j`. -/
theorem measurable_reflTransGen {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {r : α → ι → ι → Prop} (hr : ∀ a b, Measurable fun x => r x a b) (i j : ι) :
    Measurable fun x => ReflTransGen (r x) i j := by
  have hchain : ∀ (l : List ι) (a : ι), Measurable fun x => List.IsChain (r x) (a :: l) := by
    intro l
    induction l with
    | nil =>
      intro a
      have e : (fun x => List.IsChain (r x) [a]) = fun _ => True :=
        funext fun _ => propext (iff_true_intro (List.isChain_singleton a))
      rw [e]
      exact measurable_const
    | cons b l ih =>
      intro a
      simp only [List.isChain_cons_cons]
      exact (hr a b).and (ih b)
  have e : (fun x => ReflTransGen (r x) i j) = fun x =>
      ∃ l : List ι, List.IsChain (r x) (i :: l) ∧ (i :: l).getLast (List.cons_ne_nil _ _) = j :=
    funext fun _ => propext ⟨List.exists_isChain_cons_of_relationReflTransGen,
      fun ⟨l, h1, h2⟩ => List.relationReflTransGen_of_exists_isChain_cons l h1 h2⟩
  rw [e]
  exact Measurable.exists fun l => (hchain l i).and measurable_const

/-- The label test is a closed condition on the curve. -/
theorem isClosed_labelPointTest (F : Finset ℤ) (i : ℤ) (n : ℕ) :
    IsClosed {f : C(ℝ, ℂ) | LabelPointTest F i n f} := by
  unfold LabelPointTest
  refine isClosed_setOf_exists_mem_Icc _ _ ?_
  refine isClosed_setOf_and_of_isClosed ?_ ?_
  · refine isClosed_setOf_forall_imp fun _ _ => ?_
    exact isClosed_setOf_exists_mem_Icc _ _
      (isClosed_eq (Complex.orthonormalBasisOneI.repr.continuous.comp (by fun_prop))
        (Complex.orthonormalBasisOneI.repr.continuous.comp (by fun_prop)))
  · refine isClosed_setOf_forall_imp fun _ _ => ?_
    refine isClosed_setOf_forall_imp fun _ _ => ?_
    exact isClosed_le continuous_const
      ((Complex.orthonormalBasisOneI.repr.continuous.comp (by fun_prop)).dist
        (Complex.orthonormalBasisOneI.repr.continuous.comp (by fun_prop)))

/-- The countable form of the validity hypotheses is a measurable condition on the datum. -/
theorem measurable_unitMeshValidTest :
    Measurable fun w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => UnitMeshValidTest w := by
  have hc : ∀ i j : ℤ, Measurable fun w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => w.2 i j := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)
  have hpos : ∀ i j : ℤ, Measurable fun w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => 0 < w.2 i j := fun i j =>
    (measurable_from_nat (f := fun k : ℕ => 0 < k)).comp (hc i j)
  have hball : ∀ (j : ℤ) (R : ℕ), IsClosed {f : C(ℝ, ℂ) |
      ∃ t ∈ Icc ((j : ℝ) - 1) j, Complex.orthonormalBasisOneI.repr (f t) ∈ closedBall (0 : Plane) R} :=
    fun _ _ => isClosed_setOf_exists_mem_Icc _ _
      (isClosed_closedBall.preimage (Complex.orthonormalBasisOneI.repr.continuous.comp (by fun_prop)))
  have hpt : ∀ (j : ℤ) (z : Plane), IsClosed {f : C(ℝ, ℂ) |
      ∃ t ∈ Icc ((j : ℝ) - 1) j, Complex.orthonormalBasisOneI.repr (f t) = z} :=
    fun _ _ => isClosed_setOf_exists_mem_Icc _ _
      (isClosed_eq (Complex.orthonormalBasisOneI.repr.continuous.comp (by fun_prop)) continuous_const)
  have hint : ∀ i j : ℤ, IsClosed {f : C(ℝ, ℂ) | ∃ s ∈ Icc ((i : ℝ) - 1) i, ∃ t ∈ Icc ((j : ℝ) - 1) j,
      Complex.orthonormalBasisOneI.repr (f s) = Complex.orthonormalBasisOneI.repr (f t)} :=
    fun _ _ => isClosed_setOf_exists_mem_Icc _ _ (isClosed_setOf_exists_mem_Icc _ _
      (isClosed_eq (Complex.orthonormalBasisOneI.repr.continuous.comp (by fun_prop))
        (Complex.orthonormalBasisOneI.repr.continuous.comp (by fun_prop))))
  unfold UnitMeshValidTest
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_
    (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_))))))
  · refine Measurable.forall fun R => Measurable.exists fun _ => Measurable.forall fun j => ?_
    exact Measurable.imp (measurable_of_isClosed_setOf_fst (hball j R)) measurable_const
  · exact Measurable.forall fun k => Measurable.exists fun j =>
      measurable_of_isClosed_setOf_fst (hpt j (TopologicalSpace.denseSeq Plane k))
  · refine Measurable.forall fun j => ?_
    have h := measurableSet_lt
      (measurable_const : Measurable fun _ : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => (0 : ENNReal))
      (measurable_volume_unitCell j)
    exact measurableSet_setOfPred.1 h
  · exact Measurable.forall fun i => Measurable.forall fun j =>
      Measurable.imp measurable_const ((measurable_volume_unitCell_inter i j).eq_const 0)
  · refine Measurable.forall fun i => Measurable.forall fun j => ?_
    have e : (fun w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => w.2 i j = w.2 j i) =
        fun w => ∃ k : ℕ, w.2 i j = k ∧ w.2 j i = k :=
      funext fun w => propext ⟨fun h => ⟨_, rfl, h.symm⟩, fun ⟨_, h1, h2⟩ => h1.trans h2.symm⟩
    rw [e]
    exact Measurable.exists fun k => ((hc i j).eq_const k).and ((hc j i).eq_const k)
  · exact Measurable.forall fun j => (hc j j).eq_const 0
  · exact Measurable.forall fun i => Measurable.forall fun j =>
      Measurable.imp (hpos i j) (measurable_of_isClosed_setOf_fst (hint i j))
  · refine Measurable.forall fun F => Measurable.forall fun i => Measurable.forall fun j =>
      Measurable.forall fun n => ?_
    refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp
      (measurable_of_isClosed_setOf_fst (isClosed_labelPointTest F i n)) ?_))
    refine measurable_reflTransGen ?_ i j
    intro a b
    exact (hpos a b).and measurable_const

/-- **The validity set of the unit-mesh data is Borel**: `{w | UnitMeshValid w}` is a measurable
subset of `C(ℝ, ℂ) × (ℤ → ℤ → ℕ)`, for the compact-open Borel `σ`-algebra on the curves and the
product of the discrete `σ`-algebras on the edge counts. -/
theorem measurableSet_unitMeshValid :
    MeasurableSet {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) | UnitMeshValid w} := by
  have e : {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) | UnitMeshValid w} = {w | UnitMeshValidTest w} :=
    Set.ext fun w => unitMeshValid_iff_test (w := w)
  rw [e]
  exact measurableSet_setOfPred.2 measurable_unitMeshValidTest

end MatedCRT.ZeroConePolygonal
