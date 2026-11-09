/- Credit: the contact times of the almost-sure statement are `MatedCRT.AdjacentContactWitnesses.ae_contact_times`
(commit d117aff), which rests on Leonardo Bonanno's frozen `MatedCRTHarmonic.MatedCRT.DirectRel`
(LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel, commit 31e7483), `MatedCRTHarmonic.MatedCRT.lrCoord`
and the mating-of-trees structure `IsMatingOfTreesCoupling` (see that file's header). The topology used here is
Mathlib's (`IsPreconnected.union'`, `IsPreconnected.image`, `IsCompact.image`, `IsCompact.union`). -/
import MatedCRT.Proofs.MatingOfTrees.AdjacentContactWitnesses

/-!
# Connected and compact traces of cell paths

Source: `notes/wpn-steps2/steps2-r3.tex` (sha256 88dfb1f9...), lines 637-652: the labels of the cells meeting a
connected path form a connected graph; the union of the cells along a chain of pairwise meeting cells is connected.
A *vertex path* is `IsVPathIn m A p a b` (Defs/Map.lean): a list `p` from `a` to `b` in `A` whose successive vertices
are joined by edges `m c d ≠ 0`. Its trace is `pathCells ε η p = ⋃_{c ∈ p} H^ε_c`, the union of the cells
`H^ε_c = η([ε(c-1), εc])` (`cell`).

* `isVPathIn_pathCells` (deterministic): for continuous `η`, if each successive edge `(c, d)` of `p` with `m c d ≠ 0`
  joins intersecting cells, then the trace is preconnected and compact, contains the cells of the exact endpoints `a`
  and `b`, and lies in `fillCells ε η A`.
* `ae_isVPathIn_pathCells` (environment): for a valid mated-CRT environment `S` and a fixed mesh `ε > 0`, almost surely,
  for every finite vertex path of `S.mult ε ω`, the same conclusions hold for `S.η ω`. The quantifiers are fixed-mesh:
  the event depends on `ε`, and no event is claimed common to all meshes.

The deterministic part uses only continuity of `η`; the mesh positivity enters only through the contact times.
-/

namespace MatedCRT.ConnectedCellTraces

open MeasureTheory Set

/-- The trace `⋃_{c ∈ p} H^ε_c` of a list of vertices: the union of the cells of the vertices of `p`. -/
def pathCells (ε : ℝ) (η : ℝ → ℂ) (p : List ℤ) : Set ℂ :=
  ⋃ c ∈ p, cell ε η c

theorem pathCells_nil (ε : ℝ) (η : ℝ → ℂ) : pathCells ε η [] = ∅ := by
  ext z
  simp [pathCells]

theorem pathCells_cons (ε : ℝ) (η : ℝ → ℂ) (c : ℤ) (p : List ℤ) :
    pathCells ε η (c :: p) = cell ε η c ∪ pathCells ε η p := by
  ext z
  simp [pathCells]

theorem cell_subset_pathCells {ε : ℝ} {η : ℝ → ℂ} {c : ℤ} {p : List ℤ} (h : c ∈ p) :
    cell ε η c ⊆ pathCells ε η p :=
  fun _ hz => Set.mem_iUnion₂.2 ⟨c, h, hz⟩

/-- A point of the closed time cell `[ε(k-1), εk]` lies in the cell `H^ε_k = η([ε(k-1), εk])`. -/
theorem mem_cell_of_mem_Icc {ε : ℝ} {η : ℝ → ℂ} {k : ℤ} {t : ℝ}
    (ht : t ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k)) : η t ∈ cell ε η k :=
  Set.mem_image_of_mem η ht

/-- A cell is the continuous image of a compact interval, hence connected. -/
theorem cell_isPreconnected {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    IsPreconnected (cell ε η k) := by
  unfold cell
  exact isPreconnected_Icc.image η hη.continuousOn

/-- A cell is the continuous image of a compact interval, hence compact. -/
theorem cell_isCompact {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    IsCompact (cell ε η k) := by
  unfold cell
  exact isCompact_Icc.image hη

/-- A chain of connected cells, consecutive ones meeting, has connected trace (Mathlib `IsPreconnected.union'`). -/
theorem pathCells_isPreconnected {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) :
    ∀ p : List ℤ, p.IsChain (fun c d => (cell ε η c ∩ cell ε η d).Nonempty) →
      IsPreconnected (pathCells ε η p)
  | [], _ => by
    rw [pathCells_nil]
    exact isPreconnected_empty
  | [c], _ => by
    rw [pathCells_cons, pathCells_nil, Set.union_empty]
    exact cell_isPreconnected hη c
  | c :: d :: p, h => by
    rw [List.isChain_cons_cons] at h
    rw [pathCells_cons]
    obtain ⟨z, hzc, hzd⟩ := h.1
    exact IsPreconnected.union' ⟨z, hzc, cell_subset_pathCells (c := d) (p := d :: p) (by simp) hzd⟩
      (cell_isPreconnected hη c) (pathCells_isPreconnected hη (d :: p) h.2)

/-- The trace of a finite list of vertices is compact: a finite union of compact cells. -/
theorem pathCells_isCompact {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) :
    ∀ p : List ℤ, IsCompact (pathCells ε η p)
  | [] => by
    rw [pathCells_nil]
    exact isCompact_empty
  | c :: p => by
    rw [pathCells_cons]
    exact (cell_isCompact hη c).union (pathCells_isCompact hη p)

/-- Two chains on one list give a chain of conjunctions. -/
theorem isChain_and_of_isChain {α : Type*} {R S : α → α → Prop} :
    ∀ l : List α, l.IsChain R → l.IsChain S → l.IsChain fun a b => R a b ∧ S a b
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: l, hR, hS => by
    rw [List.isChain_cons_cons] at hR hS ⊢
    exact ⟨⟨hR.1, hS.1⟩, isChain_and_of_isChain (b :: l) hR.2 hS.2⟩

/-- **Connected trace of a vertex path.** Let `η` be continuous and let `p` be a vertex path from `a` to `b` in `A`
for the edge multiplicity `m` (`IsVPathIn m A p a b`). If each successive edge `(c, d)` of `p` with `m c d ≠ 0` joins
intersecting cells `H^ε_c` and `H^ε_d`, then the union of the cells of `p` is preconnected and compact, contains the
cells of the exact endpoints `a` and `b`, and is contained in `fillCells ε η A`. -/
theorem isVPathIn_pathCells {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {m : ℤ → ℤ → ℕ} {A : Set ℤ} {p : List ℤ}
    {a b : ℤ} (hp : IsVPathIn m A p a b)
    (hedge : p.IsChain fun c d => m c d ≠ 0 → (cell ε η c ∩ cell ε η d).Nonempty) :
    IsPreconnected (pathCells ε η p) ∧ IsCompact (pathCells ε η p) ∧
      pathCells ε η p ⊆ fillCells ε η A ∧
      cell ε η a ⊆ pathCells ε η p ∧ cell ε η b ⊆ pathCells ε η p := by
  obtain ⟨hhead, hlast, hA, hedges⟩ := hp
  have hchain : p.IsChain fun c d => (cell ε η c ∩ cell ε η d).Nonempty :=
    (isChain_and_of_isChain p hedges hedge).imp fun c d h => h.2 h.1
  have ha : a ∈ p := List.mem_of_mem_head? (Option.mem_def.2 hhead)
  have hb : b ∈ p := List.mem_of_mem_getLast? (Option.mem_def.2 hlast)
  refine ⟨pathCells_isPreconnected hη p hchain, pathCells_isCompact hη p, ?_,
    cell_subset_pathCells ha, cell_subset_pathCells hb⟩
  intro z hz
  obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.1 hz
  exact Set.mem_iUnion₂.2 ⟨c, hA c hc, hzc⟩

/-- **Almost sure connected traces at a fixed mesh.** Let `S` be a valid mated-CRT environment and `ε > 0` a fixed
mesh. Almost surely, simultaneously for every finite vertex path of `S.mult ε ω` (every `A`, `p`, `a`, `b` with
`IsVPathIn (S.mult ε ω) A p a b`), the trace of `p` in `S.η ω` is connected and compact, contains the cells of its exact
endpoints, and lies in `fillCells ε (S.η ω) A`. The event is one event for all paths at this mesh; it is not claimed
for all meshes. -/
theorem ae_isVPathIn_pathCells (𝒮 : SpaceFillingSLEModel) (γ : ℝ) (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ (A : Set ℤ) (p : List ℤ) (a b : ℤ), IsVPathIn (S.mult ε ω) A p a b →
      IsPreconnected (pathCells ε (S.η ω) p) ∧ IsCompact (pathCells ε (S.η ω) p) ∧
        pathCells ε (S.η ω) p ⊆ fillCells ε (S.η ω) A ∧
        cell ε (S.η ω) a ⊆ pathCells ε (S.η ω) p ∧ cell ε (S.η ω) b ⊆ pathCells ε (S.η ω) p := by
  filter_upwards [AdjacentContactWitnesses.ae_contact_times 𝒮 γ Ω S hS ε hε, hS.isAreaParametrized]
    with ω hω hAP
  have hmeet : ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty := by
    intro j k hjk
    obtain ⟨u, hu, v, hv, huv⟩ := hω j k hjk
    exact ⟨S.η ω u, mem_cell_of_mem_Icc hu, by rw [huv]; exact mem_cell_of_mem_Icc hv⟩
  intro A p a b hp
  exact isVPathIn_pathCells hAP.1 hp (hp.2.2.2.imp fun c d h _ => hmeet c d h)

end MatedCRT.ConnectedCellTraces
