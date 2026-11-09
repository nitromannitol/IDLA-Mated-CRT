/- Credit: the almost-sure input is `MatedCRT.ConnectedCellTraces.ae_isVPathIn_pathCells` (commit 320ebaf). It rests on
`MatedCRT.AdjacentContactWitnesses.ae_contact_times` (commit d117aff) and through it on Leonardo Bonanno's frozen
`MatedCRTHarmonic.MatedCRT.DirectRel` (LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel, commit 31e7483),
`MatedCRTHarmonic.MatedCRT.lrCoord` and the mating-of-trees structure `IsMatingOfTreesCoupling` (see that file's header).
The countable aggregation is Mathlib's `MeasureTheory.ae_all_iff`. -/
import MatedCRT.Proofs.MatingOfTrees.ConnectedCellTraces

/-!
# Countable-mesh and dyadic-mesh events for connected cell traces

Source: `notes/wpn-steps2/steps2-r3.tex` lines 637-652 (the labels of the cells meeting a connected path form a connected
graph) and the fixed-mesh restriction at lines 602-630 (common contact times for countably many label pairs at one
mesh). The barrier consumer at lines 652-690 is written for a fixed mesh `ε`; the dyadic family below is the countable
mesh set for its specialization.

* `ae_forall_isVPathIn_pathCells`: for a supplied countable family `ε : ι → ℝ` of strictly positive meshes, almost
  surely, simultaneously for every index `i` and every finite vertex path of `S.mult (ε i) ω`, the trace at mesh `ε i`
  is connected and compact, contains the cells of its exact endpoints, and lies in `fillCells (ε i) (S.η ω) A`.
  The proof is `ae_all_iff` applied to the fixed-mesh event `ConnectedCellTraces.ae_isVPathIn_pathCells`.
* `ae_dyadic_isVPathIn_pathCells`: the same statement for the dyadic meshes `dyadicMesh n = 2^{-n}`, `n ∈ ℕ`.

This is countable aggregation only. No event is claimed for all real meshes `ε > 0`, and no probability exponent is
derived from it.
-/

namespace MatedCRT.CountableMeshContactTraces

open MeasureTheory MatedCRT.ConnectedCellTraces

/-- **Countable-mesh event for connected cell traces.** Let `S` be a valid mated-CRT environment and let
`ε : ι → ℝ` be a supplied family of strictly positive meshes indexed by a countable type `ι`. Almost surely, for every
index `i` and every finite vertex path `p` of `S.mult (ε i) ω` from `a` to `b` in `A`, the trace of `p` at mesh `ε i`
in `S.η ω` is connected and compact, lies in `fillCells (ε i) (S.η ω) A`, and contains the cells of the exact endpoints
`a` and `b`. The mesh family is not reindexed, and the path quantifiers are those of the fixed-mesh event. -/
theorem ae_forall_isVPathIn_pathCells {ι : Type*} [Countable ι]
    (𝒮 : SpaceFillingSLEModel) (γ : ℝ) (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∀ᵐ ω ∂S.P, ∀ (i : ι) (A : Set ℤ) (p : List ℤ) (a b : ℤ), IsVPathIn (S.mult (ε i) ω) A p a b →
      IsPreconnected (pathCells (ε i) (S.η ω) p) ∧ IsCompact (pathCells (ε i) (S.η ω) p) ∧
        pathCells (ε i) (S.η ω) p ⊆ fillCells (ε i) (S.η ω) A ∧
        cell (ε i) (S.η ω) a ⊆ pathCells (ε i) (S.η ω) p ∧
        cell (ε i) (S.η ω) b ⊆ pathCells (ε i) (S.η ω) p :=
  ae_all_iff.2 fun i => ae_isVPathIn_pathCells 𝒮 γ Ω S hS (ε i) (hε i)

/-- The dyadic mesh `2^{-n}` at level `n ∈ ℕ`. -/
noncomputable def dyadicMesh (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n

theorem dyadicMesh_pos (n : ℕ) : 0 < dyadicMesh n := by
  unfold dyadicMesh
  positivity

/-- **Dyadic-mesh event for connected cell traces.** Almost surely, for every dyadic level `n ∈ ℕ` (mesh `2^{-n}`) and
every finite vertex path `p` of `S.mult (dyadicMesh n) ω` from `a` to `b` in `A`, the trace of `p` at mesh `2^{-n}` in
`S.η ω` is connected and compact, lies in `fillCells (dyadicMesh n) (S.η ω) A`, and contains the cells of `a` and `b`.
This is the specialization of `ae_forall_isVPathIn_pathCells` to the countable family `dyadicMesh`. -/
theorem ae_dyadic_isVPathIn_pathCells (𝒮 : SpaceFillingSLEModel) (γ : ℝ) (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (n : ℕ) (A : Set ℤ) (p : List ℤ) (a b : ℤ), IsVPathIn (S.mult (dyadicMesh n) ω) A p a b →
      IsPreconnected (pathCells (dyadicMesh n) (S.η ω) p) ∧ IsCompact (pathCells (dyadicMesh n) (S.η ω) p) ∧
        pathCells (dyadicMesh n) (S.η ω) p ⊆ fillCells (dyadicMesh n) (S.η ω) A ∧
        cell (dyadicMesh n) (S.η ω) a ⊆ pathCells (dyadicMesh n) (S.η ω) p ∧
        cell (dyadicMesh n) (S.η ω) b ⊆ pathCells (dyadicMesh n) (S.η ω) p :=
  ae_forall_isVPathIn_pathCells 𝒮 γ Ω S hS dyadicMesh dyadicMesh_pos

end MatedCRT.CountableMeshContactTraces
