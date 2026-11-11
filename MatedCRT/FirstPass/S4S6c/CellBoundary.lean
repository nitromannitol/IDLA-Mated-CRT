import Mathlib

/-!
# Boundary crossing of the cell walk (lines 59-89)

For a family of connected cells `H v ⊆ ℂ` (`v : ℤ`) with adjacent cells intersecting, and an open set `D`, the printed argument writes
`V(D) = {v : H v ∩ D ≠ ∅}` and `I(D) = V(D) \ V(∂D)`, where `V(∂D) = {v : H v ∩ ∂D ≠ ∅}`. The deterministic facts are:
* a cell of `I(D)` lies entirely in `D` (connectedness of the cell, and the cell does not meet `∂D`);
* a walk that leaves `I(D)` first visits a cell meeting `∂D` (its previous vertex is in `I(D)`, and adjacent cells meet).
These are used in the exit-time bookkeeping of Lemma 3 and of the successive tests (eqs (23)-(27)).
-/

open Set Topology

namespace MatedCRT

/-- `V(D) = {v : H v ∩ D ≠ ∅}`. -/
def vertsMeet (H : ℤ → Set ℂ) (D : Set ℂ) : Set ℤ := {v | (H v ∩ D).Nonempty}

/-- `V(∂D) = {v : H v ∩ ∂D ≠ ∅}` (`∂D` the topological frontier). -/
def vertsFrontier (H : ℤ → Set ℂ) (D : Set ℂ) : Set ℤ := {v | (H v ∩ frontier D).Nonempty}

/-- `I(D) = V(D) \ V(∂D)`. -/
def innerVertices (H : ℤ → Set ℂ) (D : Set ℂ) : Set ℤ := vertsMeet H D \ vertsFrontier H D

/-- **A cell of `I(D)` lies in `D`.** It meets `D` and not `∂D`, and it is connected. -/
theorem cell_subset_of_mem_innerVertices {H : ℤ → Set ℂ} (hconn : ∀ v, IsPreconnected (H v))
    {D : Set ℂ} (hD : IsOpen D) {v : ℤ} (hv : v ∈ innerVertices H D) : H v ⊆ D := by
  obtain ⟨hmeet, hfront⟩ := hv
  have hmeet' : (H v ∩ D).Nonempty := hmeet
  have hfront' : ¬ (H v ∩ frontier D).Nonempty := hfront
  have hsub : H v ⊆ D ∪ (closure D)ᶜ := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · right
      intro hxc
      have hf : x ∈ frontier D := by
        rw [frontier, hD.interior_eq]
        exact ⟨hxc, hxD⟩
      exact hfront' ⟨x, hx, hf⟩
  have hdisj : Disjoint D (closure D)ᶜ :=
    Set.disjoint_left.2 fun x hx hx' => hx' (subset_closure hx)
  exact (hconn v).subset_left_of_subset_union hD isClosed_closure.isOpen_compl hdisj hsub hmeet'

/-- **A walk that leaves `I(D)` enters a cell meeting `∂D`.** If `v ∈ I(D)` and `w` is adjacent to `v` with `w ∉ I(D)`,
then `w ∈ V(∂D)`. -/
theorem neighbour_mem_vertsFrontier {H : ℤ → Set ℂ} (Adj : ℤ → ℤ → Prop)
    (hconn : ∀ v, IsPreconnected (H v)) (hadj : ∀ v w, Adj v w → (H v ∩ H w).Nonempty)
    {D : Set ℂ} (hD : IsOpen D) {v w : ℤ} (hv : v ∈ innerVertices H D) (hvw : Adj v w)
    (hw : w ∉ innerVertices H D) : w ∈ vertsFrontier H D := by
  obtain ⟨x, hxv, hxw⟩ := hadj v w hvw
  have hsub := cell_subset_of_mem_innerVertices hconn hD hv
  have hwD : (H w ∩ D).Nonempty := ⟨x, hxw, hsub hxv⟩
  by_contra hcon
  exact hw ⟨⟨x, hxw, hsub hxv⟩, hcon⟩

/-- **The first exit of a walk from `I(D)` is through a cell meeting `∂D`.** If the walk `x` starts in `I(D)` and at some
time leaves `I(D)`, then at the first such time `k` it is in `V(∂D)`, and it stayed in `I(D)` before. -/
theorem path_exits_through_frontier {H : ℤ → Set ℂ} (Adj : ℤ → ℤ → Prop)
    (hconn : ∀ v, IsPreconnected (H v)) (hadj : ∀ v w, Adj v w → (H v ∩ H w).Nonempty)
    {D : Set ℂ} (hD : IsOpen D) (x : ℕ → ℤ) (hpath : ∀ n, Adj (x n) (x (n + 1)))
    (h0 : x 0 ∈ innerVertices H D) (hex : ∃ n, x n ∉ innerVertices H D) :
    ∃ k, x k ∈ vertsFrontier H D ∧ x k ∉ innerVertices H D ∧ ∀ n < k, x n ∈ innerVertices H D := by
  classical
  obtain ⟨k, hk, hmin⟩ : ∃ k, x k ∉ innerVertices H D ∧ ∀ n < k, x n ∈ innerVertices H D :=
    ⟨Nat.find hex, Nat.find_spec hex, fun n hn => not_not.1 (Nat.find_min hex hn)⟩
  rcases k with _ | j
  · exact absurd h0 hk
  · refine ⟨j + 1, ?_, hk, fun n hn => hmin n hn⟩
    exact neighbour_mem_vertsFrontier Adj hconn hadj hD (hmin j (Nat.lt_succ_self j)) (hpath j) hk

end MatedCRT
