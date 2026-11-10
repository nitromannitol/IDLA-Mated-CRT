import MatedCRT.FirstPass.S4S6c.TraceInputs68

/-!
# Cell-size input of the uniform Lemma 6.8 (q2, task fp-S4S6c-envscaling-6-7-6-8; LEMMA68 B1, Draft 2.8)

The diameter bound of the cell-size estimate (`CellSizeEstimateStmt`, Draft/Section2.lean:131), read on one
configuration `η`: if every cell meeting `ball 0 ρ` has diameter at most `d`, then the diameter hypothesis `hsm0` of
`TraceBand68.trace_band` holds with the same `d`, for the closures of the cells. Boundedness of the cells is
deterministic once `η` is continuous (`TraceInputs68.cell_isBounded`; `ae_continuous_eta` gives continuity almost
surely).

Terminology: diameter and closure of the cell `cell ε η k = η '' Icc (ε (k-1)) (ε k)` (Duplantier-Sheffield mating
of trees, cells of the space-filling SLE curve; Armstrong-Kuusi-Mourrat for the vertex/cell terminology).
-/

open MeasureTheory Set Metric

namespace MatedCRT
namespace CellSize68

/-- **Pairwise diameter bound from the cell diameters.** For continuous `η`, a bound `diam (cell ε η k) ≤ d` on every
cell meeting `ball 0 ρ` gives the closure form of `hsm0`: any two points of the closure of a cell meeting `ball 0 ρ`
are at distance at most `d`. -/
theorem hsm0_of_diam_le {ε ρ d : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty → diam (cell ε η k) ≤ d) :
    ∀ v : ℤ, (cell ε η v ∩ ball (0 : ℂ) ρ).Nonempty →
      ∀ u ∈ closure (cell ε η v), ∀ u' ∈ closure (cell ε η v), dist u u' ≤ d := by
  intro v hv u hu u' hu'
  have hb : Bornology.IsBounded (closure (cell ε η v)) :=
    (TraceInputs68.cell_isBounded hη v).closure
  calc dist u u' ≤ diam (closure (cell ε η v)) := dist_le_diam_of_mem hb hu hu'
    _ = diam (cell ε η v) := diam_closure _
    _ ≤ d := hdiam v hv

/-- **Cell-size estimate, read as `hsm0`.** On the event of `CellSizeEstimateStmt` (the upper half of its
two-sided bound, `diam (cell ε (η) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)` for every cell meeting `ball 0 ρ`), for continuous
`η` the diameter hypothesis `hsm0` holds with `d = ε ^ (2 / (2 + γ) ^ 2 - ζ)`. -/
theorem hsm0_of_cellSize {ε ρ γ ζ : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hev : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty →
      ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε η k) ∧ diam (cell ε η k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)) :
    ∀ v : ℤ, (cell ε η v ∩ ball (0 : ℂ) ρ).Nonempty →
      ∀ u ∈ closure (cell ε η v), ∀ u' ∈ closure (cell ε η v),
        dist u u' ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ) :=
  hsm0_of_diam_le hη (fun k hk => (hev k hk).2)

end CellSize68
end MatedCRT

#print axioms MatedCRT.CellSize68.hsm0_of_diam_le
#print axioms MatedCRT.CellSize68.hsm0_of_cellSize
