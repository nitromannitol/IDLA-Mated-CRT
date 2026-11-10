import Mathlib
import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.FirstPass.S3t.CellGeometry

/-!
# Consecutive walk cells meet (input `hadj` of Step 10; fp-S3t-walk-adjacency, owner z1)

The hypothesis `hadj` of `MatedCRT.TruncatedLaws.quenched_sub_stopped_le` (`FirstPass/S3t/RiemannSum.lean`) asks that,
for consecutive vertices `q j`, `q (j + 1)` of the walk, the cells `cell ε η _` intersect. Here the walk is a sample
path of `srwLaw (S.mult ε ω) a`, and `η = S.η ω`. The proof uses three inputs, all proved:

* `MatedCRT.srwAeAdjacentStep` (`Proofs/Sec6/ConstantOrderLowerBound/Walk.lean`): almost surely every step of simple
  random walk is stationary or along an edge of positive multiplicity;
* `MatedCRT.adjacentCellsMeetAeStep` (`Proofs/MatingOfTrees/AdjacentCells.lean`): almost surely, for every `ε > 0`,
  vertices joined by an edge of `S.mult ε ω` have intersecting cells, simultaneously for all `ε`;
* `MatedCRT.TruncatedLaws.vertexPoint_mem_cell_of_nonneg` (`FirstPass/S3t/CellGeometry.lean`): a vertex lies in its own
  cell, so a stationary step keeps a nonempty cell.

No hypothesis is added and no new Prop is frozen.
-/

open MeasureTheory Set Filter

namespace MatedCRT.TruncatedLaws

/-- Deterministic step: if every edge of the multigraph `m` joins meeting cells, then a walk `q` whose steps are
stationary or along edges of `m` has meeting cells at each pair of consecutive vertices. -/
lemma walk_step_cells_meet {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} (hε : 0 ≤ ε)
    (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) (q : ℕ → ℤ)
    (hq : ∀ n : ℕ, q (n + 1) = q n ∨ m (q n) (q (n + 1)) ≠ 0) (n : ℕ) :
    (cell ε η (q n) ∩ cell ε η (q (n + 1))).Nonempty := by
  rcases hq n with h | h
  · rw [h, Set.inter_self]
    exact ⟨vertexPoint ε η (q n), vertexPoint_mem_cell_of_nonneg hε (q n)⟩
  · exact hedge _ _ h

/-- Almost every walk of `srwLaw m a` has meeting cells at all consecutive vertices, when the edges of `m` join meeting
cells. -/
lemma srwLaw_cells_meet_ae {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} (hε : 0 ≤ ε)
    (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) (a : ℤ) :
    ∀ᵐ q ∂srwLaw m a, ∀ n : ℕ, (cell ε η (q n) ∩ cell ε η (q (n + 1))).Nonempty := by
  filter_upwards [MatedCRT.srwAeAdjacentStep m a] with q hq
  intro n
  exact walk_step_cells_meet hε hedge q hq n

/-- **Consecutive walk cells meet, almost surely.** For almost every `ω`, simultaneously for every cell size `ε > 0`
and every starting vertex `a : ℤ`, almost every walk `q` of `srwLaw (S.mult ε ω) a` has meeting cells
`cell ε (S.η ω) (q n)` and `cell ε (S.η ω) (q (n + 1))` for all `n`. -/
theorem walk_cells_meet_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ a : ℤ, ∀ᵐ q ∂srwLaw (S.mult ε ω) a,
      ∀ n : ℕ, (cell ε (S.η ω) (q n) ∩ cell ε (S.η ω) (q (n + 1))).Nonempty := by
  filter_upwards [MatedCRT.adjacentCellsMeetAeStep 𝒮 γ hγ0 hγ2 Ω S hS] with ω hω ε hε a
  exact srwLaw_cells_meet_ae hε.le (fun j k hjk => hω ε hε j k hjk) a

/-- **Input `hadj` of `quenched_sub_stopped_le`, almost surely.** For a cell size `ε > 0` and reals `mε`, `T`: for
almost every `ω`, for every starting vertex `a`, almost every walk `q` of `srwLaw (S.mult ε ω) a` satisfies
`∀ j < ⌊T * mε⌋₊, (cell ε (S.η ω) (q j) ∩ cell ε (S.η ω) (q (j + 1))).Nonempty`. -/
theorem walk_hadj_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {ε : ℝ} (hε : 0 < ε) (mε T : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ a : ℤ, ∀ᵐ q ∂srwLaw (S.mult ε ω) a,
      ∀ j < ⌊T * mε⌋₊, (cell ε (S.η ω) (q j) ∩ cell ε (S.η ω) (q (j + 1))).Nonempty := by
  filter_upwards [walk_cells_meet_ae hγ0 hγ2 S hS] with ω hω a
  filter_upwards [hω ε hε a] with q hq
  intro j _
  exact hq j

end MatedCRT.TruncatedLaws
