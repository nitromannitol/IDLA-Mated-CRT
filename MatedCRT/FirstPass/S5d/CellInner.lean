import MatedCRT.Defs.Map
import MatedCRT.Defs.Notation

/-!
# Cells meeting an inner neighbourhood lie in a smaller one

Deterministic geometry behind the compact-containment step: if a cell `H^ε_a` meets the `δ`-inner neighbourhood `B⁻_δ(X) = innerNbhd δ X` and has diameter at most `δ/2`,
then the whole cell lies in `B⁻_{δ/2}(X)`. No probability and no paper input. The diameter bound is the output of the
cell-size estimate (Lemma 2.8, `CellSizeEstimateStmt`); boundedness of the cell is part of the hypothesis.
-/

namespace MatedCRT

open Metric Set

/-- **Cells of small diameter.** If the cell `H^ε_a` is bounded, meets `B⁻_δ(X)` and has diameter at most `δ/2`, then
`H^ε_a ⊆ B⁻_{δ/2}(X)`. -/
theorem cell_subset_innerNbhd_half {ε : ℝ} {η : ℝ → ℂ} {X : Set ℂ} {δ : ℝ} {a : ℤ} (hδ : 0 < δ)
    (hbd : Bornology.IsBounded (cell ε η a)) (hdiam : diam (cell ε η a) ≤ δ / 2)
    (hmeet : (cell ε η a ∩ innerNbhd δ X).Nonempty) :
    cell ε η a ⊆ innerNbhd (δ / 2) X := by
  obtain ⟨y, hyc, hyX, hyd⟩ := hmeet
  intro x hx
  have hdist : dist x y ≤ δ / 2 := (dist_le_diam_of_mem hbd hx hyc).trans hdiam
  have hedist : edist y x ≤ ENNReal.ofReal (δ / 2) := by
    rw [edist_dist, dist_comm]
    exact ENNReal.ofReal_le_ofReal hdist
  have hxX : x ∈ X := by
    by_contra hx'
    have h0 : Metric.infEDist y Xᶜ ≤ edist y x := Metric.infEDist_le_edist_of_mem hx'
    have h1 : ENNReal.ofReal δ ≤ ENNReal.ofReal (δ / 2) := hyd.trans (h0.trans hedist)
    rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
    linarith
  show x ∈ X ∧ ENNReal.ofReal (δ / 2) ≤ Metric.infEDist x Xᶜ
  refine ⟨hxX, ?_⟩
  by_contra hlt
  replace hlt := not_le.mp hlt
  have h1 : Metric.infEDist y Xᶜ ≤ edist y x + Metric.infEDist x Xᶜ :=
    Metric.infEDist_le_edist_add_infEDist
  have hfin : edist y x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hedist
  have h2 : edist y x + Metric.infEDist x Xᶜ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
    ENNReal.add_lt_add_of_le_of_lt hfin hedist hlt
  rw [← ENNReal.ofReal_add (by linarith) (by linarith), show δ / 2 + δ / 2 = δ by ring] at h2
  exact absurd h2 (not_lt.2 (hyd.trans h1))

end MatedCRT
