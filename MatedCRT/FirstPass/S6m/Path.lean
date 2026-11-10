import Mathlib
import MatedCRT.FirstPass.S6m.Geom
import MatedCRT.FirstPass.S6h.Successive
import MatedCRT.FirstPass.S6e.Relation

/-!
# The pathwise containment `T_N < τ_U` (Lemma 6.8, write-up C3, C10-C12; fp-S6m, owner z10)

For a fixed legal path `x` of the cell walk, started at `a`, with the successive exit times `T_j = exitSchedule W j`
of the windows `W y = I(B_{2R(z y)}(z y))` (write-up C1-C3), the induction below proves, for `j ≤ N`:
* `P(j)`: `T_j = t` for some `t ∈ ℕ` and `|η(x_t) - η(a)| ≤ 3 j s` (write-up (C6); `s = √δ`, `δ = Δ(p,r)`);
* `Q(j)`: `x n ∈ killed ε η Θ F0 r` for every `n ≤ t` (the killed set of write-up (10)).
At `j = N` this gives `T_N < vExitTime (killed ...)` (write-up (C12)).
-/

namespace MatedCRT

namespace Lemma68C12

open MeasureTheory Set Metric Filter
open scoped ENNReal
open Lemma68Geometry Lemma68GeometryId Lemma68Admissible Lemma68Relation Lemma68Successive

/-- A finite exit time `vExitTime A x = k` means `x k ∉ A` and `x i ∈ A` for `i < k` (the definition of `τ_A`). -/
lemma vExitTime_eq_coe_spec {A : Set ℤ} {x : ℕ → ℤ} {k : ℕ} (h : vExitTime A x = (k : ℕ∞)) :
    x k ∉ A ∧ ∀ i < k, x i ∈ A := by
  classical
  unfold vExitTime at h
  split_ifs at h with hex
  · have hk : Nat.find hex = k := by exact_mod_cast h
    refine ⟨?_, fun i hi => ?_⟩
    · rw [← hk]
      exact Nat.find_spec hex
    · by_contra hc
      have hlt : i < Nat.find hex := by rw [hk]; exact hi
      exact Nat.find_min hex hlt hc
  · simp at h

/-- A vertex whose point lies at distance in `(0, r)` from `K` and off `Θ` is in the killed set (write-up (10)). -/
lemma mem_killed_of_infDist {ε r : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε) {Θ F0 : Finset ℤ}
    (hF : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ (↑F0 : Set ℤ)) {v : ℤ}
    (h0 : 0 < Metric.infDist (vertexPoint ε η v) (fillCells ε η (↑Θ : Set ℤ)))
    (hr : Metric.infDist (vertexPoint ε η v) (fillCells ε η (↑Θ : Set ℤ)) < r) :
    v ∈ killed ε η Θ F0 r := by
  have hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, Metric.infDist_empty] at h0
    exact lt_irrefl _ h0
  have hmem : v ∈ cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) := by
    refine ⟨vertexPoint ε η v, vertexPoint_mem_cell hε η v, ?_⟩
    rw [Metric.mem_thickening_iff]
    exact (Metric.infDist_lt_iff hK).1 hr
  have hv : v ∉ (↑Θ : Set ℤ) := by
    intro hvΘ
    have hpt : vertexPoint ε η v ∈ fillCells ε η (↑Θ : Set ℤ) :=
      Set.mem_iUnion₂.2 ⟨v, hvΘ, vertexPoint_mem_cell hε η v⟩
    have := Metric.infDist_zero_of_mem hpt
    linarith
  exact (S6k.sdiff_W_subset_killed hη hε hF) ⟨hmem, hv⟩

/-- A cell of a vertex in the window `I(B)` lies in the ball `B` (write-up C3, connectedness). -/
lemma cell_subset_of_mem_interior {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (z : ℂ) (R : ℝ) {k : ℤ}
    (hk : k ∈ interiorCellVertices ε η (ball z R)) : cell ε η k ⊆ ball z R := by
  obtain ⟨h1, h2⟩ := hk
  have hnf : cell ε η k ∩ frontier (ball z R) = ∅ := by
    by_contra hne
    exact h2 (Set.nonempty_iff_ne_empty.2 hne)
  exact cell_subset_ball_of_meet hη k z R h1 hnf

end Lemma68C12

end MatedCRT
