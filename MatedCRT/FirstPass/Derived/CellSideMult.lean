import MatedCRT.Defs.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.MetricSpace.Thickening
import LatticeProb.Topology.CompactSplit

/-!
# The frontier-side multiplicity of two cells, read off the curve

For a cell size `ε > 0` and labels `j, k`, `cellSideMult ε η j k` counts the edges joining the cells
`η([ε(j-1), εj])` and `η([ε(k-1), εk])` of the mated-CRT map by the frontier sides the two cells share
(Gwynne–Miller–Sheffield, arXiv:1705.11161, §2.5 and Proposition 2.2): `0` if `ε ≤ 0` or `j = k`, `1` for consecutive
labels, and for separated cells, with the cell intervals `I = [a, b]`, `J = [c, d]` in increasing order (`b < c`), the
number (capped at two) of times `u ∈ (b, c)` at which a frontier side shared by the two cells branches, tested by
the curve alone: `u ∈ B_η` if there are `s ∈ (a, b)` and `t ∈ (c, d)` such that each pair among `s, u, t` is a
contact (`cellSideContact`): the images of any two disjoint closed rational intervals about the two times, inside
`(a, d)`, share a continuum of positive diameter.

The main result is `measurable_cellSideMult`: `η ↦ cellSideMult ε η j k` is Borel on `C(ℝ, ℂ)`. The proof needs no
projection theorem:
* for closed intervals `P, Q`, the curves `η` such that every connected subset of `η(P) ∩ η(Q)` has diameter less than
  `δ` form an open set (`isOpen_setOf_connectedDiamLT`): such a compact set splits into finitely many disjoint compact
  pieces of diameter less than `δ` (`LatticeProb.Topology.exists_compact_split`), whose thin thickenings are disjoint
  open sets of diameter less than `δ`, and `η(P) ∩ η(Q)` stays inside their union for nearby curves;
* the failure of a contact is witnessed by an open rectangle of times, so the existence of a branch time is decided
  on compact boxes of times by finite subcovers (`measurableSet_exists_mem_compact_forall_open`).
-/

set_option autoImplicit false

open Set Metric Filter Topology MeasureTheory

namespace MatedCRT

/-! ### The definition -/

/-- **The contact relation `D_η(v, w)` on the times `(a, d)`**: for every pair
of disjoint rational open intervals about `v` and about `w` whose closures `P`, `Q` lie in `(a, d)`, the set
`η(P) ∩ η(Q)` contains a continuum (a nonempty compact connected set) of positive diameter. It is used for distinct
times `v, w ∈ (a, d)`. -/
def cellSideContact (a d : ℝ) (η : ℝ → ℂ) (v w : ℝ) : Prop :=
  ∀ p₁ p₂ q₁ q₂ : ℚ, v ∈ Ioo (p₁ : ℝ) p₂ → w ∈ Ioo (q₁ : ℝ) q₂ →
    Disjoint (Ioo (p₁ : ℝ) p₂) (Ioo (q₁ : ℝ) q₂) → Icc (p₁ : ℝ) p₂ ⊆ Ioo a d → Icc (q₁ : ℝ) q₂ ⊆ Ioo a d →
    ∃ K ⊆ η '' Icc (p₁ : ℝ) p₂ ∩ η '' Icc (q₁ : ℝ) q₂, IsCompact K ∧ IsConnected K ∧ 0 < diam K

/-- **The branch times `B_η` of the shared frontier sides of the cell intervals `[a, b]` and `[c, d]`**: the times `u ∈ (b, c)` for which there are `s ∈ (a, b)` and `t ∈ (c, d)` with
`D_η(s, u)`, `D_η(u, t)` and `D_η(s, t)`. -/
def cellSideBranchTimes (a b c d : ℝ) (η : ℝ → ℂ) : Set ℝ :=
  {u | u ∈ Ioo b c ∧ ∃ s ∈ Ioo a b, ∃ t ∈ Ioo c d,
    cellSideContact a d η s u ∧ cellSideContact a d η u t ∧ cellSideContact a d η s t}

open Classical in
/-- The number of shared frontier sides of two separated cells with time intervals `[a, b]` and `[c, d]`, `b < c`:
`1_{∃ u ∈ B_η} + 1_{∃ u, v ∈ B_η, u ≠ v}`. -/
noncomputable def cellSideCount (a b c d : ℝ) (η : ℝ → ℂ) : ℕ :=
  (if (cellSideBranchTimes a b c d η).Nonempty then 1 else 0) +
    (if ∃ u ∈ cellSideBranchTimes a b c d η, ∃ v ∈ cellSideBranchTimes a b c d η, u ≠ v then 1 else 0)

open Classical in
/-- **The frontier-side multiplicity of the cells `εj` and `εk`, read off the curve `η`** (the written argument; Gwynne–Miller–Sheffield, arXiv:1705.11161, §2.5 and Proposition 2.2: an edge for each frontier side
shared by the two cells). It is `0` if `ε ≤ 0` or `j = k`, `1` for consecutive labels (`|j - k| = 1`), and otherwise,
with the cell intervals `[ε(lo - 1), ε lo]` and `[ε(hi - 1), ε hi]` of `lo = min j k < hi = max j k` (the conventions
of `cell` and `cellMult`, `MatedCRT/Defs/Map.lean`), the count `cellSideCount` of the branch times of the shared
sides, capped at two. -/
noncomputable def cellSideMult (ε : ℝ) (η : ℝ → ℂ) (j k : ℤ) : ℕ :=
  if ε ≤ 0 ∨ j = k then 0
  else if |j - k| = 1 then 1
  else cellSideCount (ε * ((min j k : ℤ) - 1 : ℝ)) (ε * (min j k : ℤ)) (ε * ((max j k : ℤ) - 1 : ℝ))
    (ε * (max j k : ℤ)) η

/-! ### Continua in compact sets -/

/-- Every connected subset of `C` has diameter less than `δ`. -/
def ConnectedDiamLT (δ : ℝ) (C : Set ℂ) : Prop :=
  ∀ K ⊆ C, IsConnected K → diam K < δ

/-- `C` contains a continuum of positive diameter. -/
def ContainsNondegenerateContinuum (C : Set ℂ) : Prop :=
  ∃ K ⊆ C, IsCompact K ∧ IsConnected K ∧ 0 < diam K

theorem diam_thickening_le_of_isBounded {C : Set ℂ} (hC : Bornology.IsBounded C) {r : ℝ} (hr : 0 ≤ r) :
    diam (thickening r C) ≤ diam C + 2 * r := by
  refine diam_le_of_forall_dist_le (add_nonneg diam_nonneg (by linarith)) fun y hy z hz => ?_
  obtain ⟨y', hy'C, hyy'⟩ := mem_thickening_iff.1 hy
  obtain ⟨z', hz'C, hzz'⟩ := mem_thickening_iff.1 hz
  have h1 := dist_le_diam_of_mem hC hy'C hz'C
  have h2 := dist_triangle4 y y' z' z
  have h3 : dist z' z < r := by
    rw [dist_comm]
    exact hzz'
  linarith

/-- Two disjoint compact sets, the first of diameter less than `δ` and the second inside an open set all of whose
connected subsets have diameter less than `δ`, lie in an open set with the same property. -/
theorem exists_isOpen_connectedDiamLT_union {δ : ℝ} {C₁ C₂ V₂ : Set ℂ} (hC₁ : IsCompact C₁) (hC₂ : IsCompact C₂)
    (hd : Disjoint C₁ C₂) (h₁ : diam C₁ < δ) (hV₂ : IsOpen V₂) (hCV₂ : C₂ ⊆ V₂) (hgood₂ : ConnectedDiamLT δ V₂) :
    ∃ V, IsOpen V ∧ C₁ ∪ C₂ ⊆ V ∧ ConnectedDiamLT δ V := by
  obtain ⟨r₀, hr₀, hdisj⟩ := hd.exists_thickenings hC₁ hC₂.isClosed
  set r := min r₀ ((δ - diam C₁) / 4)
  have hrpos : 0 < r := lt_min hr₀ (by linarith)
  have hdisj' : Disjoint (thickening r C₁) (thickening r C₂) :=
    hdisj.mono (thickening_mono (min_le_left _ _) _) (thickening_mono (min_le_left _ _) _)
  have hdiam : diam (thickening r C₁) < δ := by
    have h1 := diam_thickening_le_of_isBounded hC₁.isBounded hrpos.le
    have h2 : r ≤ (δ - diam C₁) / 4 := min_le_right _ _
    linarith
  refine ⟨thickening r C₁ ∪ (V₂ ∩ thickening r C₂), isOpen_thickening.union (hV₂.inter isOpen_thickening),
    union_subset_union (self_subset_thickening hrpos _) (subset_inter hCV₂ (self_subset_thickening hrpos _)), ?_⟩
  intro K hK hKc
  by_cases hmeet : (K ∩ thickening r C₁).Nonempty
  · have hsub := hKc.isPreconnected.subset_left_of_subset_union isOpen_thickening
      (hV₂.inter isOpen_thickening) (hdisj'.mono_right inter_subset_right) hK hmeet
    exact (diam_mono hsub hC₁.isBounded.thickening).trans_lt hdiam
  · have hsub : K ⊆ V₂ := fun y hy => by
      rcases hK hy with h | h
      · exact absurd ⟨y, hy, h⟩ hmeet
      · exact h.1
    exact hgood₂ K hsub hKc

/-- A compact set covered by finitely many sets `A i` cutting it into compact pieces `C ∩ A i`, `C \ A i`, with
`diam (C ∩ A i) < δ`, lies in an open set all of whose connected subsets have diameter less than `δ`. -/
theorem exists_isOpen_connectedDiamLT_of_finite_cover {δ : ℝ} {ι : Type*} (A : ι → Set ℂ)
    (t : Finset ι) : ∀ C : Set ℂ, IsCompact C → C ⊆ ⋃ i ∈ t, A i →
      (∀ i ∈ t, IsCompact (C ∩ A i) ∧ IsCompact (C \ A i) ∧ diam (C ∩ A i) < δ) →
      ∃ V, IsOpen V ∧ C ⊆ V ∧ ConnectedDiamLT δ V := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro C _ hC _
    refine ⟨∅, isOpen_empty, fun y hy => ?_, fun K hK hKc => absurd (hKc.nonempty.mono hK) not_nonempty_empty⟩
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (hC hy)
    exact absurd hi (Finset.notMem_empty i)
  | insert i t _hi ih =>
    intro C _ hC hA
    obtain ⟨h1, h2, h3⟩ := hA i (Finset.mem_insert_self i t)
    have hcov : C \ A i ⊆ ⋃ j ∈ t, A j := by
      intro y hy
      obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 (hC hy.1)
      rcases Finset.mem_insert.1 hj with rfl | hj'
      · exact absurd hyj hy.2
      · exact mem_iUnion₂.2 ⟨j, hj', hyj⟩
    have hpieces : ∀ j ∈ t, IsCompact ((C \ A i) ∩ A j) ∧ IsCompact ((C \ A i) \ A j) ∧
        diam ((C \ A i) ∩ A j) < δ := by
      intro j hj
      obtain ⟨g1, g2, g3⟩ := hA j (Finset.mem_insert_of_mem hj)
      have e1 : (C \ A i) ∩ A j = (C ∩ A j) ∩ (C \ A i) := by
        ext y
        exact ⟨fun hy => ⟨⟨hy.1.1, hy.2⟩, hy.1⟩, fun hy => ⟨hy.2, hy.1.2⟩⟩
      have e2 : (C \ A i) \ A j = (C \ A i) ∩ (C \ A j) := by
        ext y
        exact ⟨fun hy => ⟨hy.1, hy.1.1, hy.2⟩, fun hy => ⟨hy.1, hy.2.2⟩⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [e1]
        exact g1.inter h2
      · rw [e2]
        exact h2.inter g2
      · exact (diam_mono (show (C \ A i) ∩ A j ⊆ C ∩ A j from fun y hy => ⟨hy.1.1, hy.2⟩)
          g1.isBounded).trans_lt g3
    obtain ⟨V₂, hV₂o, hV₂, hV₂g⟩ := ih (C \ A i) h2 hcov hpieces
    obtain ⟨V, hVo, hV, hVg⟩ := exists_isOpen_connectedDiamLT_union h1 h2
      (disjoint_left.2 fun y hy hy' => hy'.2 hy.2) h3 hV₂o hV₂ hV₂g
    refine ⟨V, hVo, fun y hy => hV ?_, hVg⟩
    by_cases hyA : y ∈ A i
    · exact Or.inl ⟨hy, hyA⟩
    · exact Or.inr ⟨hy, hyA⟩

/-- **A compact set all of whose connected subsets have diameter less than `δ` lies in an open set with the same
property.** For `x ∈ C` the component of `x` in `C` has diameter `< δ`; split `C` into disjoint compact pieces, one
containing `x` and inside a thin thickening of that component (`LatticeProb.Topology.exists_compact_split`), and use
finitely many of them. -/
theorem exists_isOpen_connectedDiamLT {δ : ℝ} {C : Set ℂ} (hC : IsCompact C)
    (hsmall : ConnectedDiamLT δ C) : ∃ V, IsOpen V ∧ C ⊆ V ∧ ConnectedDiamLT δ V := by
  classical
  have hsplit : ∀ x : C, ∃ A : Set ℂ, IsCompact A ∧ IsCompact (C \ A) ∧ A ⊆ C ∧ diam A < δ ∧ (x : ℂ) ∈ A := by
    intro x
    set K := connectedComponentIn C (x : ℂ)
    have hKC : K ⊆ C := connectedComponentIn_subset _ _
    have hKb : Bornology.IsBounded K := hC.isBounded.subset hKC
    have hKd : diam K < δ :=
      hsmall K hKC ⟨⟨x, mem_connectedComponentIn x.2⟩, isPreconnected_connectedComponentIn⟩
    set r := (δ - diam K) / 3 with hrdef
    have hr : 0 < r := by
      rw [hrdef]
      linarith
    have hT : ∀ T ⊆ C, IsPreconnected T →
        ¬ ((T ∩ {(x : ℂ)}).Nonempty ∧ (T ∩ (thickening r K)ᶜ).Nonempty) := by
      rintro T hTC hTp ⟨⟨y, hyT, hy⟩, ⟨z, hzT, hz⟩⟩
      rw [mem_singleton_iff] at hy
      subst hy
      exact hz (self_subset_thickening hr K (hTp.subset_connectedComponentIn hyT hTC hzT))
    obtain ⟨SE, SG, hSE, hSG, hdisj, hunion, hSEG, hSGE⟩ :=
      LatticeProb.Topology.exists_compact_split hC isClosed_singleton isOpen_thickening.isClosed_compl hT
    have hCSE : C \ SE = SG := by
      ext y
      constructor
      · rintro ⟨hyC, hyE⟩
        rw [← hunion] at hyC
        exact hyC.resolve_left hyE
      · intro hy
        refine ⟨?_, fun hyE => disjoint_left.1 hdisj hyE hy⟩
        rw [← hunion]
        exact Or.inr hy
    refine ⟨SE, hSE, by rw [hCSE]; exact hSG, ?_, ?_, ?_⟩
    · rw [← hunion]
      exact subset_union_left
    · have hsub : SE ⊆ thickening r K := disjoint_compl_right_iff_subset.1 hSEG
      have h1 := diam_thickening_le_of_isBounded hKb hr.le
      have h2 := diam_mono hsub hKb.thickening
      linarith
    · have hxC : (x : ℂ) ∈ SE ∪ SG := by
        rw [hunion]
        exact x.2
      rcases hxC with h | h
      · exact h
      · exact absurd (mem_singleton (x : ℂ)) (disjoint_left.1 hSGE h)
  choose A hAc hAd hAC hAdiam hxA using hsplit
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C => (C \ A x)ᶜ) (fun x => (hAd x).isClosed.isOpen_compl)
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, fun h => h.2 (hxA _)⟩)
  refine exists_isOpen_connectedDiamLT_of_finite_cover A t C hC ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht hy)
    exact mem_iUnion₂.2 ⟨x, hx, Classical.byContradiction fun h => hyx ⟨hy, h⟩⟩
  · intro x _
    rw [inter_eq_right.2 (hAC x)]
    exact ⟨hAc x, hAd x, hAdiam x⟩

/-- For a compact set, containing a continuum of positive diameter means having a connected subset of diameter at
least `1/(m+1)` for some `m`. -/
theorem containsNondegenerateContinuum_iff {C : Set ℂ} (hC : IsCompact C) :
    ContainsNondegenerateContinuum C ↔ ∃ m : ℕ, ¬ ConnectedDiamLT (1 / ((m : ℝ) + 1)) C := by
  constructor
  · rintro ⟨K, hKC, -, hK, hd⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hd
    exact ⟨m, fun h => lt_asymm (h K hKC hK) hm⟩
  · rintro ⟨m, hm⟩
    simp only [ConnectedDiamLT, not_forall, not_lt] at hm
    obtain ⟨K, hKC, hK, hd⟩ := hm
    have hcl : closure K ⊆ C := hC.isClosed.closure_subset_iff.2 hKC
    refine ⟨closure K, hcl, hC.of_isClosed_subset isClosed_closure hcl, hK.closure, ?_⟩
    rw [diam_closure]
    exact lt_of_lt_of_le (by positivity) hd

/-! ### Openness and measurability of the continuum test -/

/-- For an open `V`, the curves `η` with `η(P) ∩ η(Q) ⊆ V` form an open set of `C(ℝ, ℂ)`. -/
theorem isOpen_setOf_image_inter_image_subset (p₁ p₂ q₁ q₂ : ℝ) {V : Set ℂ} (hV : IsOpen V) :
    IsOpen {η : C(ℝ, ℂ) | η '' Icc p₁ p₂ ∩ η '' Icc q₁ q₂ ⊆ V} := by
  let I : Set (ℝ × ℝ) := Icc p₁ p₂ ×ˢ Icc q₁ q₂
  have : CompactSpace I := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  have h1 : Continuous fun z : C(ℝ, ℂ) × I => z.1 (z.2 : ℝ × ℝ).1 :=
    ContinuousEval.continuous_eval.comp
      (continuous_fst.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))
  have h2 : Continuous fun z : C(ℝ, ℂ) × I => z.1 (z.2 : ℝ × ℝ).2 :=
    ContinuousEval.continuous_eval.comp
      (continuous_fst.prodMk (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))
  have hB : IsClosed {z : C(ℝ, ℂ) × I | z.1 (z.2 : ℝ × ℝ).1 = z.1 (z.2 : ℝ × ℝ).2 ∧
      z.1 (z.2 : ℝ × ℝ).1 ∈ Vᶜ} :=
    (isClosed_eq h1 h2).inter (hV.isClosed_compl.preimage h1)
  have heq : {η : C(ℝ, ℂ) | η '' Icc p₁ p₂ ∩ η '' Icc q₁ q₂ ⊆ V}ᶜ =
      Prod.fst '' {z : C(ℝ, ℂ) × I | z.1 (z.2 : ℝ × ℝ).1 = z.1 (z.2 : ℝ × ℝ).2 ∧
        z.1 (z.2 : ℝ × ℝ).1 ∈ Vᶜ} := by
    ext η
    constructor
    · intro hη
      obtain ⟨y, ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩, hy⟩ := not_subset.1 hη
      exact ⟨(η, ⟨(s, t), mk_mem_prod hs ht⟩), ⟨hts.symm, hy⟩, rfl⟩
    · rintro ⟨⟨η', ⟨⟨s, t⟩, hs, ht⟩⟩, ⟨hst, hy⟩, rfl⟩ hsub
      exact hy (hsub ⟨⟨s, hs, rfl⟩, ⟨t, ht, hst.symm⟩⟩)
  rw [← isClosed_compl_iff, heq]
  exact isClosedMap_fst_of_compactSpace _ hB

/-- **The curves `η` such that every connected subset of `η(P) ∩ η(Q)` has diameter less than `δ` form an open set
of `C(ℝ, ℂ)`.** -/
theorem isOpen_setOf_connectedDiamLT (p₁ p₂ q₁ q₂ δ : ℝ) :
    IsOpen {η : C(ℝ, ℂ) | ConnectedDiamLT δ (η '' Icc p₁ p₂ ∩ η '' Icc q₁ q₂)} := by
  refine isOpen_iff_forall_mem_open.2 fun η₀ h₀ => ?_
  have hC : IsCompact (η₀ '' Icc p₁ p₂ ∩ η₀ '' Icc q₁ q₂) :=
    (isCompact_Icc.image η₀.continuous).inter (isCompact_Icc.image η₀.continuous)
  obtain ⟨V, hVo, hCV, hV⟩ := exists_isOpen_connectedDiamLT hC h₀
  exact ⟨_, fun η hη K hK hKc => hV K (hK.trans hη) hKc,
    isOpen_setOf_image_inter_image_subset p₁ p₂ q₁ q₂ hVo, hCV⟩

/-- **The continuum test is Borel in the curve.** -/
theorem measurableSet_setOf_containsNondegenerateContinuum (p₁ p₂ q₁ q₂ : ℝ) :
    MeasurableSet {η : C(ℝ, ℂ) | ContainsNondegenerateContinuum (η '' Icc p₁ p₂ ∩ η '' Icc q₁ q₂)} := by
  have heq : {η : C(ℝ, ℂ) | ContainsNondegenerateContinuum (η '' Icc p₁ p₂ ∩ η '' Icc q₁ q₂)} =
      ⋃ m : ℕ, {η : C(ℝ, ℂ) | ConnectedDiamLT (1 / ((m : ℝ) + 1)) (η '' Icc p₁ p₂ ∩ η '' Icc q₁ q₂)}ᶜ := by
    ext η
    rw [mem_iUnion]
    exact containsNondegenerateContinuum_iff
      ((isCompact_Icc.image η.continuous).inter (isCompact_Icc.image η.continuous))
  rw [heq]
  exact MeasurableSet.iUnion fun m =>
    (isOpen_setOf_connectedDiamLT p₁ p₂ q₁ q₂ _).measurableSet.compl

/-! ### Existence of good times in compact boxes -/

/-- Let `K m` be compact, `O j` open (`j` in a countable type) and `T j` measurable. The `ω` for which some `x` in
some `K m` satisfies `ω ∈ T j` whenever `x ∈ O j` form a measurable set: by compactness, `x` fails to exist in `K m`
iff finitely many `O j` with `ω ∉ T j` cover `K m`. -/
theorem measurableSet_exists_mem_compact_forall_open {X Ω J : Type*} [TopologicalSpace X] [MeasurableSpace Ω]
    [Countable J] {K : ℕ → Set X} (hK : ∀ m, IsCompact (K m)) {O : J → Set X} (hO : ∀ j, IsOpen (O j))
    {T : J → Set Ω} (hT : ∀ j, MeasurableSet (T j)) :
    MeasurableSet {ω | ∃ m, ∃ x ∈ K m, ∀ j, x ∈ O j → ω ∈ T j} := by
  have key : ∀ m, {ω | ∃ x ∈ K m, ∀ j, x ∈ O j → ω ∈ T j}ᶜ =
      ⋃ t ∈ {t : Set J | t.Finite ∧ t ⊆ univ}, ({_ω : Ω | K m ⊆ ⋃ j ∈ t, O j} ∩ ⋂ j ∈ t, (T j)ᶜ) := by
    intro m
    ext ω
    rw [mem_compl_iff, mem_iUnion₂]
    constructor
    · intro hω
      have hcov : K m ⊆ ⋃ j ∈ {j | ω ∉ T j}, O j := by
        intro x hx
        by_contra hx'
        refine hω ⟨x, hx, fun j hxj => ?_⟩
        by_contra hj
        exact hx' (mem_iUnion₂.2 ⟨j, hj, hxj⟩)
      obtain ⟨t, htsub, htfin, htcov⟩ := (hK m).elim_finite_subcover_image (fun j _ => hO j) hcov
      exact ⟨t, ⟨htfin, subset_univ t⟩, htcov, mem_iInter₂.2 fun j hj => htsub hj⟩
    · rintro ⟨t, -, htcov, hT'⟩ ⟨x, hx, hgood⟩
      have htcov' : K m ⊆ ⋃ j ∈ t, O j := htcov
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 (htcov' hx)
      exact (mem_iInter₂.1 hT' j hj) (hgood j hxj)
  have hS : {t : Set J | t.Finite ∧ t ⊆ univ}.Countable := Set.countable_ofPred_finite_subset countable_univ
  have hmeas : ∀ m, MeasurableSet {ω | ∃ x ∈ K m, ∀ j, x ∈ O j → ω ∈ T j} := fun m => by
    rw [← compl_compl {ω | ∃ x ∈ K m, ∀ j, x ∈ O j → ω ∈ T j}, key m]
    exact (MeasurableSet.biUnion hS fun t ht => (MeasurableSet.const _).inter
      (MeasurableSet.biInter ht.1.countable fun j _ => (hT j).compl)).compl
  have heq : {ω | ∃ m, ∃ x ∈ K m, ∀ j, x ∈ O j → ω ∈ T j} =
      ⋃ m, {ω | ∃ x ∈ K m, ∀ j, x ∈ O j → ω ∈ T j} := by
    ext ω
    rw [mem_iUnion]
    rfl
  rw [heq]
  exact MeasurableSet.iUnion hmeas

/-- The compact boxes `[a + 1/(m+1), b - 1/(m+1)] × [b + 1/(m+1), c - 1/(m+1)] × [c + 1/(m+1), d - 1/(m+1)]`
exhausting `(a, b) × (b, c) × (c, d)`. -/
def sideBox (a b c d : ℝ) (m : ℕ) : Set (ℝ × ℝ × ℝ) :=
  Icc (a + 1 / ((m : ℝ) + 1)) (b - 1 / ((m : ℝ) + 1)) ×ˢ Icc (b + 1 / ((m : ℝ) + 1)) (c - 1 / ((m : ℝ) + 1)) ×ˢ
    Icc (c + 1 / ((m : ℝ) + 1)) (d - 1 / ((m : ℝ) + 1))

theorem isCompact_sideBox (a b c d : ℝ) (m : ℕ) : IsCompact (sideBox a b c d m) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

theorem sideBox_subset (a b c d : ℝ) (m : ℕ) : sideBox a b c d m ⊆ Ioo a b ×ˢ Ioo b c ×ˢ Ioo c d := by
  have he : 0 < 1 / ((m : ℝ) + 1) := by positivity
  intro x hx
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ := hx
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem eventually_mem_sideBox {a b c d : ℝ} {x : ℝ × ℝ × ℝ} (hx : x ∈ Ioo a b ×ˢ Ioo b c ×ˢ Ioo c d) :
    ∀ᶠ m : ℕ in atTop, x ∈ sideBox a b c d m := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ := hx
  have he : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h := fun (g : ℝ) (hg : 0 < g) => (tendsto_order.1 he).2 g hg
  filter_upwards [h _ (sub_pos.2 h1), h _ (sub_pos.2 h2), h _ (sub_pos.2 h3), h _ (sub_pos.2 h4),
    h _ (sub_pos.2 h5), h _ (sub_pos.2 h6)] with m g1 g2 g3 g4 g5 g6
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-! ### Measurability of the branch-time indicators -/

/-- The pairs of times `(v, w)` in the rational intervals `(p₁, p₂)` and `(q₁, q₂)` of `i = (p₁, p₂, q₁, q₂)`, when these
are disjoint with closures in `(a, d)` (empty otherwise). -/
def contactRect (a d : ℝ) (i : ℚ × ℚ × ℚ × ℚ) : Set (ℝ × ℝ) :=
  {_vw | Disjoint (Ioo (i.1 : ℝ) i.2.1) (Ioo (i.2.2.1 : ℝ) i.2.2.2) ∧ Icc (i.1 : ℝ) i.2.1 ⊆ Ioo a d ∧
    Icc (i.2.2.1 : ℝ) i.2.2.2 ⊆ Ioo a d} ∩ Ioo (i.1 : ℝ) i.2.1 ×ˢ Ioo (i.2.2.1 : ℝ) i.2.2.2

/-- The curves whose images of the closed rational intervals of `i` share a continuum of positive diameter. -/
def contactTest (i : ℚ × ℚ × ℚ × ℚ) : Set C(ℝ, ℂ) :=
  {η | ContainsNondegenerateContinuum (η '' Icc (i.1 : ℝ) i.2.1 ∩ η '' Icc (i.2.2.1 : ℝ) i.2.2.2)}

theorem isOpen_contactRect (a d : ℝ) (i : ℚ × ℚ × ℚ × ℚ) : IsOpen (contactRect a d i) :=
  isOpen_const.inter (isOpen_Ioo.prod isOpen_Ioo)

theorem measurableSet_contactTest (i : ℚ × ℚ × ℚ × ℚ) : MeasurableSet (contactTest i) :=
  measurableSet_setOf_containsNondegenerateContinuum _ _ _ _

theorem cellSideContact_iff {a d : ℝ} {η : C(ℝ, ℂ)} {v w : ℝ} :
    cellSideContact a d ⇑η v w ↔ ∀ i, (v, w) ∈ contactRect a d i → η ∈ contactTest i := by
  constructor
  · rintro h ⟨p₁, p₂, q₁, q₂⟩ ⟨⟨hd, hP, hQ⟩, hv, hw⟩
    exact h p₁ p₂ q₁ q₂ hv hw hd hP hQ
  · intro h p₁ p₂ q₁ q₂ hv hw hd hP hQ
    exact h (p₁, p₂, q₁, q₂) ⟨⟨hd, hP, hQ⟩, hv, hw⟩

/-- The open sets of triples of times `(s, u, t)` at which one of the three contacts fails for the test `i`. -/
def sideContactPairs (a d : ℝ) :
    (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ) → Set (ℝ × ℝ × ℝ) :=
  Sum.elim (fun i => (fun x : ℝ × ℝ × ℝ => (x.1, x.2.1)) ⁻¹' contactRect a d i)
    (Sum.elim (fun i => (fun x : ℝ × ℝ × ℝ => (x.2.1, x.2.2)) ⁻¹' contactRect a d i)
      (fun i => (fun x : ℝ × ℝ × ℝ => (x.1, x.2.2)) ⁻¹' contactRect a d i))

/-- The continuum tests of the three contacts. -/
def sideContactTests : (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ) → Set C(ℝ, ℂ) :=
  Sum.elim contactTest (Sum.elim contactTest contactTest)

theorem isOpen_sideContactPairs (a d : ℝ) (j : (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ)) :
    IsOpen (sideContactPairs a d j) := by
  rcases j with i | i | i
  · exact (isOpen_contactRect a d i).preimage (by fun_prop)
  · exact (isOpen_contactRect a d i).preimage (by fun_prop)
  · exact (isOpen_contactRect a d i).preimage (by fun_prop)

theorem measurableSet_sideContactTests (j : (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ)) :
    MeasurableSet (sideContactTests j) := by
  rcases j with i | i | i <;> exact measurableSet_contactTest i

theorem forall_sideContact_iff {a d : ℝ} {η : C(ℝ, ℂ)} {x : ℝ × ℝ × ℝ} :
    (∀ j, x ∈ sideContactPairs a d j → η ∈ sideContactTests j) ↔
      cellSideContact a d ⇑η x.1 x.2.1 ∧ cellSideContact a d ⇑η x.2.1 x.2.2 ∧
        cellSideContact a d ⇑η x.1 x.2.2 := by
  exact Sum.forall.trans (and_congr cellSideContact_iff.symm
    (Sum.forall.trans (and_congr cellSideContact_iff.symm cellSideContact_iff.symm)))

theorem measurableSet_setOf_cellSideBranchTimes_nonempty (a b c d : ℝ) :
    MeasurableSet {η : C(ℝ, ℂ) | (cellSideBranchTimes a b c d ⇑η).Nonempty} := by
  have heq : {η : C(ℝ, ℂ) | (cellSideBranchTimes a b c d ⇑η).Nonempty} =
      {η | ∃ m, ∃ x ∈ sideBox a b c d m, ∀ j, x ∈ sideContactPairs a d j → η ∈ sideContactTests j} := by
    ext η
    constructor
    · rintro ⟨u, hu, s, hs, t, ht, h1, h2, h3⟩
      obtain ⟨m, hm⟩ := (eventually_mem_sideBox (x := (s, u, t)) ⟨hs, hu, ht⟩).exists
      exact ⟨m, (s, u, t), hm, forall_sideContact_iff.2 ⟨h1, h2, h3⟩⟩
    · rintro ⟨m, x, hx, hgood⟩
      obtain ⟨hs, hu, ht⟩ := sideBox_subset a b c d m hx
      obtain ⟨h1, h2, h3⟩ := forall_sideContact_iff.1 hgood
      exact ⟨x.2.1, hu, x.1, hs, x.2.2, ht, h1, h2, h3⟩
  rw [heq]
  exact measurableSet_exists_mem_compact_forall_open (isCompact_sideBox a b c d) (isOpen_sideContactPairs a d)
    measurableSet_sideContactTests

/-- The compact sets of pairs of triples of times in `sideBox a b c d m` whose middle times are `1/(m+1)` apart. -/
def sideBox₂ (a b c d : ℝ) (m : ℕ) : Set ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) :=
  (sideBox a b c d m ×ˢ sideBox a b c d m) ∩ {xy | 1 / ((m : ℝ) + 1) ≤ |xy.1.2.1 - xy.2.2.1|}

theorem isCompact_sideBox₂ (a b c d : ℝ) (m : ℕ) : IsCompact (sideBox₂ a b c d m) :=
  ((isCompact_sideBox a b c d m).prod (isCompact_sideBox a b c d m)).inter_right
    (isClosed_le continuous_const (continuous_fst.snd.fst.sub continuous_snd.snd.fst).abs)

theorem measurableSet_setOf_cellSideBranchTimes_two (a b c d : ℝ) :
    MeasurableSet {η : C(ℝ, ℂ) |
      ∃ u ∈ cellSideBranchTimes a b c d ⇑η, ∃ v ∈ cellSideBranchTimes a b c d ⇑η, u ≠ v} := by
  let O₂ : ((ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ)) ⊕
      ((ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ)) → Set ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) :=
    Sum.elim (fun j => Prod.fst ⁻¹' sideContactPairs a d j) (fun j => Prod.snd ⁻¹' sideContactPairs a d j)
  let T₂ : ((ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ)) ⊕
      ((ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ) ⊕ (ℚ × ℚ × ℚ × ℚ)) → Set C(ℝ, ℂ) :=
    Sum.elim sideContactTests sideContactTests
  have hO₂ : ∀ j, IsOpen (O₂ j) := by
    rintro (j | j)
    · exact (isOpen_sideContactPairs a d j).preimage continuous_fst
    · exact (isOpen_sideContactPairs a d j).preimage continuous_snd
  have hT₂ : ∀ j, MeasurableSet (T₂ j) := by
    rintro (j | j) <;> exact measurableSet_sideContactTests j
  have hiff : ∀ (η : C(ℝ, ℂ)) (xy : (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)), (∀ j, xy ∈ O₂ j → η ∈ T₂ j) ↔
      (∀ j, xy.1 ∈ sideContactPairs a d j → η ∈ sideContactTests j) ∧
        ∀ j, xy.2 ∈ sideContactPairs a d j → η ∈ sideContactTests j := fun _ _ => Sum.forall
  have heq : {η : C(ℝ, ℂ) |
      ∃ u ∈ cellSideBranchTimes a b c d ⇑η, ∃ v ∈ cellSideBranchTimes a b c d ⇑η, u ≠ v} =
      {η | ∃ m, ∃ xy ∈ sideBox₂ a b c d m, ∀ j, xy ∈ O₂ j → η ∈ T₂ j} := by
    ext η
    constructor
    · rintro ⟨u, ⟨hu, s, hs, t, ht, h1, h2, h3⟩, v, ⟨hv, s', hs', t', ht', h1', h2', h3'⟩, huv⟩
      have hpos : 0 < |u - v| := abs_pos.2 (sub_ne_zero.2 huv)
      have he : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      obtain ⟨m, hm1, hm2, hm3⟩ := ((eventually_mem_sideBox (x := (s, u, t)) ⟨hs, hu, ht⟩).and
        ((eventually_mem_sideBox (x := (s', v, t')) ⟨hs', hv, ht'⟩).and
          ((tendsto_order.1 he).2 _ hpos))).exists
      exact ⟨m, ((s, u, t), (s', v, t')), ⟨⟨hm1, hm2⟩, hm3.le⟩,
        (hiff η _).2 ⟨forall_sideContact_iff.2 ⟨h1, h2, h3⟩, forall_sideContact_iff.2 ⟨h1', h2', h3'⟩⟩⟩
    · rintro ⟨m, xy, ⟨⟨hx, hy⟩, hxy⟩, hgood⟩
      obtain ⟨g1, g2⟩ := (hiff η xy).1 hgood
      obtain ⟨hs, hu, ht⟩ := sideBox_subset a b c d m hx
      obtain ⟨hs', hv, ht'⟩ := sideBox_subset a b c d m hy
      obtain ⟨h1, h2, h3⟩ := forall_sideContact_iff.1 g1
      obtain ⟨h1', h2', h3'⟩ := forall_sideContact_iff.1 g2
      have hpos : 0 < |xy.1.2.1 - xy.2.2.1| := lt_of_lt_of_le (by positivity) hxy
      refine ⟨xy.1.2.1, ⟨hu, xy.1.1, hs, xy.1.2.2, ht, h1, h2, h3⟩, xy.2.2.1,
        ⟨hv, xy.2.1, hs', xy.2.2.2, ht', h1', h2', h3'⟩, fun h => ?_⟩
      rw [h, sub_self, abs_zero] at hpos
      exact lt_irrefl 0 hpos
  rw [heq]
  exact measurableSet_exists_mem_compact_forall_open (isCompact_sideBox₂ a b c d) hO₂ hT₂

/-! ### Measurability of the multiplicity -/

theorem measurable_cellSideCount (a b c d : ℝ) : Measurable fun η : C(ℝ, ℂ) => cellSideCount a b c d ⇑η := by
  classical
  have heq : (fun η : C(ℝ, ℂ) => cellSideCount a b c d ⇑η) = fun η : C(ℝ, ℂ) =>
      if (cellSideBranchTimes a b c d ⇑η).Nonempty then
        (if ∃ u ∈ cellSideBranchTimes a b c d ⇑η, ∃ v ∈ cellSideBranchTimes a b c d ⇑η, u ≠ v then 2 else 1)
      else
        (if ∃ u ∈ cellSideBranchTimes a b c d ⇑η, ∃ v ∈ cellSideBranchTimes a b c d ⇑η, u ≠ v then 1 else 0) := by
    funext η
    unfold cellSideCount
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite (measurableSet_setOf_cellSideBranchTimes_nonempty a b c d)
    (Measurable.ite (measurableSet_setOf_cellSideBranchTimes_two a b c d) measurable_const measurable_const)
    (Measurable.ite (measurableSet_setOf_cellSideBranchTimes_two a b c d) measurable_const measurable_const)

/-- **The frontier-side multiplicity is a Borel function of the curve**. -/
theorem measurable_cellSideMult (ε : ℝ) (j k : ℤ) : Measurable fun η : C(ℝ, ℂ) => cellSideMult ε ⇑η j k := by
  by_cases h1 : ε ≤ 0 ∨ j = k
  · have heq : (fun η : C(ℝ, ℂ) => cellSideMult ε ⇑η j k) = fun _ => 0 := by
      funext η
      rw [cellSideMult, ite_eq_left h1]
    rw [heq]
    exact measurable_const
  · by_cases h2 : |j - k| = 1
    · have heq : (fun η : C(ℝ, ℂ) => cellSideMult ε ⇑η j k) = fun _ => 1 := by
        funext η
        rw [cellSideMult, ite_eq_right h1, ite_eq_left h2]
      rw [heq]
      exact measurable_const
    · have heq : (fun η : C(ℝ, ℂ) => cellSideMult ε ⇑η j k) = fun η : C(ℝ, ℂ) =>
          cellSideCount (ε * ((min j k : ℤ) - 1 : ℝ)) (ε * (min j k : ℤ)) (ε * ((max j k : ℤ) - 1 : ℝ))
            (ε * (max j k : ℤ)) ⇑η := by
        funext η
        rw [cellSideMult, ite_eq_right h1, ite_eq_right h2]
      rw [heq]
      exact measurable_cellSideCount _ _ _ _

end MatedCRT
