import Mathlib
import MatedCRT.FirstPass.S6k
import MatedCRT.FirstPass.S6e.Relation

/-!
# Geometry of the Lemma 6.8 test windows

Deterministic cell and distance facts used by the containment argument C12 (write-up C5, C7-C11
section C3). A cell is `cell ε η k = η '' Icc (ε (k-1)) (ε k)`, `K = fillCells ε η Θ` is the filled set of `Θ`, and the
distance of a point to `K` is `Metric.infDist` (potential-theoretic distance, Armitage-Gardiner terminology).
-/

namespace MatedCRT

namespace Lemma68C12

open MeasureTheory Set Metric Filter
open scoped ENNReal
open Lemma68Geometry Lemma68GeometryId Lemma68Admissible Lemma68Relation

/-- The vertex point `η(εk)` lies in the cell of `k`. -/
lemma vertexPoint_mem_cell {ε : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩

/-- A cell is connected (`IsPreconnected`): if it meets an open ball and misses the frontier of the ball, it lies in the
ball. This is the connectedness step of the window `I(B_{2R}(z))` (write-up C3). -/
lemma cell_subset_ball_of_meet {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) (z : ℂ) (R : ℝ)
    (hmeet : (cell ε η k ∩ ball z R).Nonempty) (hnf : cell ε η k ∩ frontier (ball z R) = ∅) :
    cell ε η k ⊆ ball z R := by
  have hconn := S6k.cell_isPreconnected ε hη k
  have hsuv : cell ε η k ⊆ ball z R ∪ (closure (ball z R))ᶜ := by
    intro y hy
    by_cases h : y ∈ closure (ball z R)
    · left
      by_contra hb
      have hyf : y ∈ frontier (ball z R) := by
        rw [frontier, isOpen_ball.interior_eq]
        exact ⟨h, hb⟩
      exact (Set.eq_empty_iff_forall_notMem.1 hnf) y ⟨hy, hyf⟩
    · exact Or.inr h
  refine hconn.subset_left_of_subset_union isOpen_ball isClosed_closure.isOpen_compl ?_ hsuv hmeet
  exact Set.disjoint_left.2 fun y hy hy' => hy' (subset_closure hy)

/-- `x ↦ dist(x, K)` is `1`-Lipschitz. -/
lemma abs_infDist_sub_le {K : Set ℂ} (x y : ℂ) :
    |Metric.infDist x K - Metric.infDist y K| ≤ dist x y := by
  have h1 : Metric.infDist x K ≤ Metric.infDist y K + dist x y := Metric.infDist_le_infDist_add_dist
  have h2 : Metric.infDist y K ≤ Metric.infDist x K + dist y x := Metric.infDist_le_infDist_add_dist
  rw [dist_comm y x] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- If `dist(y, K) < c` and `K ⊆ B(0, R)`, then `‖y‖ < R + c`. -/
lemma norm_lt_of_infDist_lt {K : Set ℂ} (hK : K.Nonempty) {R c : ℝ} (hKb : K ⊆ ball (0 : ℂ) R) {y : ℂ}
    (h : Metric.infDist y K < c) : ‖y‖ < R + c := by
  obtain ⟨k, hk, hd⟩ := (Metric.infDist_lt_iff hK).1 h
  have hk' : ‖k‖ < R := mem_ball_zero_iff.1 (hKb hk)
  have h3 := dist_triangle y k 0
  simp only [dist_zero_right] at h3
  linarith

/-- The filled set `K` is nonempty as soon as `ε` is positive and `Θ` is nonempty; the distance of `η(q)` to `K` is
recovered from the `ENNReal` distance. -/
lemma ofReal_infDist_eq {K : Set ℂ} (hK : K.Nonempty) (u : ℂ) :
    ENNReal.ofReal (Metric.infDist u K) = Metric.infEDist u K := by
  unfold Metric.infDist
  exact ENNReal.ofReal_toReal (Metric.infEDist_ne_top hK)

/-- **Start on the middle sphere (write-up C5, intermediate value).** Let `dd a ≤ r/2 ≤ ddMax a`. Then some point of the
cell `H_a` lies at distance exactly `r/2` from `K`. The cell is connected and compact; the minimum and maximum of
`dist(·, K)` on it are attained, and they are the `ENNReal` infimum and supremum `cellDist`, `cellDistMax`. -/
lemma exists_cell_point_infDist {ε r : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε) {Θ : Finset ℤ}
    (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty) (hr : 0 < r) {a : ℤ}
    (h1 : dd ε η Θ a ≤ r / 2) (h2 : r / 2 ≤ ddMax ε η Θ a) :
    ∃ y ∈ cell ε η a, Metric.infDist y (fillCells ε η (↑Θ : Set ℤ)) = r / 2 := by
  set K := fillCells ε η (↑Θ : Set ℤ) with hKdef
  have hne := S6k.cell_nonempty hε η a
  have hcpt := S6k.cell_isCompact ε hη a
  have hconn := S6k.cell_isPreconnected ε hη a
  have hcont : ContinuousOn (fun y => Metric.infDist y K) (cell ε η a) :=
    (Metric.continuous_infDist_pt K).continuousOn
  obtain ⟨u₀, hu₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
  obtain ⟨u₁, hu₁, hmax⟩ := hcpt.exists_isMaxOn hne hcont
  have hfin0 := cellDist_ne_top hη hε hK a
  have hfin1 := cellDistMax_ne_top hη hε hK a
  have hdd : cellDist ε η Θ a ≤ ENNReal.ofReal (r / 2) := by
    rw [← ENNReal.ofReal_toReal hfin0]
    exact ENNReal.ofReal_le_ofReal h1
  have hddM : ENNReal.ofReal (r / 2) ≤ cellDistMax ε η Θ a := by
    rw [← ENNReal.ofReal_toReal hfin1]
    exact ENNReal.ofReal_le_ofReal h2
  have hE0 : Metric.infEDist u₀ K = cellDist ε η Θ a := by
    rw [cellDist_eq_iInf_cell hη hε Θ a]
    refine le_antisymm (le_iInf₂ fun u hu => ?_) (iInf₂_le u₀ hu₀)
    rw [← ofReal_infDist_eq hK u₀, ← ofReal_infDist_eq hK u]
    exact ENNReal.ofReal_le_ofReal (isMinOn_iff.1 hmin u hu)
  have hE1 : Metric.infEDist u₁ K = cellDistMax ε η Θ a := by
    rw [cellDistMax_eq_iSup_cell hη hε Θ a]
    refine le_antisymm (le_iSup₂ (f := fun u _ => Metric.infEDist u K) u₁ hu₁) (iSup₂_le fun u hu => ?_)
    rw [← ofReal_infDist_eq hK u₁, ← ofReal_infDist_eq hK u]
    exact ENNReal.ofReal_le_ofReal (isMaxOn_iff.1 hmax u hu)
  have hlo : Metric.infDist u₀ K ≤ r / 2 := by
    have h := hE0.trans_le hdd
    rw [← ofReal_infDist_eq hK u₀] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h
  have hhi : r / 2 ≤ Metric.infDist u₁ K := by
    have h := hddM.trans_eq hE1.symm
    rw [← ofReal_infDist_eq hK u₁] at h
    exact (ENNReal.ofReal_le_ofReal_iff Metric.infDist_nonneg).1 h
  obtain ⟨y, hy, hfy⟩ := hconn.intermediate_value hu₀ hu₁ hcont ⟨hlo, hhi⟩
  exact ⟨y, hy, hfy⟩

/-- **Start distance (write-up C5).** If `dd a ≤ r/2 ≤ ddMax a`, the start point `η(εa)` satisfies
`|dist(η(εa), K) - r/2| ≤ d`, provided every cell meeting `B_ρ` has diameter at most `d` and `K ⊆ B(0, ρ/2)`, `r ≤ ρ/100`. -/
lemma start_infDist_close {ε r ρ d : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε) {Θ : Finset ℤ}
    (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty) (hKb : fillCells ε η (↑Θ : Set ℤ) ⊆ ball (0 : ℂ) (ρ / 2))
    (hr : 0 < r) (hrρ : r ≤ ρ / 100) {a : ℤ}
    (h1 : dd ε η Θ a ≤ r / 2) (h2 : r / 2 ≤ ddMax ε η Θ a)
    (hsize : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty → Metric.diam (cell ε η k) ≤ d) :
    |Metric.infDist (vertexPoint ε η a) (fillCells ε η (↑Θ : Set ℤ)) - r / 2| ≤ d := by
  obtain ⟨y, hy, hfy⟩ := exists_cell_point_infDist hη hε hK hr h1 h2
  have hyb : y ∈ ball (0 : ℂ) ρ := by
    have h := norm_lt_of_infDist_lt hK hKb (c := r / 2 + r) (y := y) (by rw [hfy]; linarith)
    rw [mem_ball_zero_iff]
    linarith
  have hdiam := hsize a ⟨y, hy, hyb⟩
  have hcpt := S6k.cell_isCompact ε hη a
  have hdist : dist (vertexPoint ε η a) y ≤ d :=
    (Metric.dist_le_diam_of_mem hcpt.isBounded (vertexPoint_mem_cell hε η a) hy).trans hdiam
  have habs := abs_infDist_sub_le (K := fillCells ε η (↑Θ : Set ℤ)) (vertexPoint ε η a) y
  rw [hfy] at habs
  exact habs.trans hdist

end Lemma68C12

end MatedCRT
