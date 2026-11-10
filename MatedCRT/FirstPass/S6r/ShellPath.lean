import Mathlib
import MatedCRT.FirstPass.S6r.ShellWiring
import MatedCRT.FirstPass.S6r.ShellOmega
import MatedCRT.FirstPass.S6e.GeometryId
import MatedCRT.FirstPass.S6e.Admissible

/-!
# Lemma 6.8 shells on path space: the pathwise shell chain in the `ShellOmega` form (`ShellPath`)

`shell_chain_pathwise` (ShellWiring) is stated for `ℕ`-valued hitting, centre and exit times. Here the
`ℕ∞`-valued shell times `shellHit`, `shellCentre`, `shellExit`, `testEnd` of `ShellOmega` are matched to it:

* the cell-level exit set of the killed walk is the thickening of the filled set `K = fillCells Θ`
  (`cellVertices_thickening_eq`, GeometryId), so the killed set `U` contains `V^ε(K + B_r) \ Θ` once the
  named hypothesis `F0 ⊇ {dd < r}` holds (`cellVertices_thickening_sdiff_subset_killed`, the one inclusion needed);
* the nearest-neighbour steps give the cell adjacency `cell (x m) ∩ cell (x (m+1)) ≠ ∅` (`hadj_of_nn`);
* the mesh condition `CellDiamLe ε η h Set.univ` (every cell has diameter at most `h`) is an environment
  hypothesis; it gives the diameter and centre-mesh conditions of the chain.

Terminology: shells `Σ_k`, hitting times `C_k`, exit times `T_k`, test ends `L_k` as in notes (7.20)-(7.35) and
the PRO redesign, step 12.
-/

open MeasureTheory Metric Set
open scoped ENNReal
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible

namespace MatedCRT
namespace Lemma68ShellPath

section Helpers

variable {ε : ℝ} {η : ℝ → ℂ}

lemma cell_nonempty (hε : 0 < ε) (k : ℤ) : (cell ε η k).Nonempty := by
  unfold cell
  exact Set.Nonempty.image η (Set.nonempty_Icc.2 (mul_le_mul_of_nonneg_left (by linarith) hε.le))

lemma cell_inter_succ_nonempty (hε : 0 < ε) (k : ℤ) :
    (cell ε η k ∩ cell ε η (k + 1)).Nonempty := by
  unfold cell
  refine ⟨η (ε * (k : ℝ)), ⟨⟨ε * (k : ℝ), ⟨?_, le_rfl⟩, rfl⟩, ⟨ε * (k : ℝ), ⟨?_, ?_⟩, rfl⟩⟩⟩
  · exact mul_le_mul_of_nonneg_left (by linarith) hε.le
  · push_cast
    exact le_of_eq (by ring)
  · push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) hε.le

/-- Adjacent integers have intersecting cells: `cell k` and `cell (k+1)` share the point `η (ε k)`. -/
lemma cell_adj_nonempty (hε : 0 < ε) (k k' : ℤ) (h : k' = k + 1 ∨ k' = k - 1) :
    (cell ε η k ∩ cell ε η k').Nonempty := by
  rcases h with rfl | rfl
  · exact cell_inter_succ_nonempty hε k
  · have h' := cell_inter_succ_nonempty (η := η) hε (k - 1)
    rw [sub_add_cancel, Set.inter_comm] at h'
    exact h'

/-- Nearest-neighbour steps give the adjacency hypothesis of the shell chain. -/
lemma hadj_of_nn (hε : 0 < ε) (x : ℕ → ℤ) (hnn : ∀ m, x (m + 1) = x m + 1 ∨ x (m + 1) = x m - 1)
    (m : ℕ) : (cell ε η (x m) ∩ cell ε η (x (m + 1))).Nonempty :=
  cell_adj_nonempty hε (x m) (x (m + 1)) (hnn m)

/-- A global mesh bound `CellDiamLe ε η h univ` gives the bound on every subset `E`. -/
lemma cellDiamLe_of_univ {h : ℝ} (hmesh : CellDiamLe ε η h Set.univ) (E : Set ℂ) :
    CellDiamLe ε η h E :=
  fun k hk => hmesh k (by obtain ⟨p, hp⟩ := hk; exact ⟨p, hp.1, trivial⟩)

lemma cell_diam_of_univ {h : ℝ} (hε : 0 < ε) (hmesh : CellDiamLe ε η h Set.univ) (k : ℤ) :
    ∀ p ∈ cell ε η k, ∀ q ∈ cell ε η k, dist p q ≤ h := by
  refine hmesh k ?_
  obtain ⟨p, hp⟩ := cell_nonempty (η := η) hε k
  exact ⟨p, hp, trivial⟩

open Classical in
/-- The killed-walk exit time is a point outside the killed set when finite. -/
lemma vExitTime_toNat_not_mem {A : Set ℤ} {x : ℕ → ℤ} (h : vExitTime A x ≠ ⊤) :
    x (vExitTime A x).toNat ∉ A := by
  unfold vExitTime at h ⊢
  split_ifs at h ⊢ with hex
  · rw [ENat.toNat_natCast]
    exact Nat.find_spec hex
  · exact absurd rfl h

/-- The first-time functional: if `m < firstTime P` then `P m` fails. -/
lemma not_of_lt_firstTime {P : ℕ → Prop} {m : ℕ} (hm : (m : ℕ∞) < firstTime P) : ¬ P m := by
  intro hP
  exact absurd ((firstTime_le_iff P m).2 ⟨m, le_rfl, hP⟩) (not_le.2 hm)

open Classical in
/-- The first-time functional is attained when finite. -/
lemma firstTime_toNat_spec {P : ℕ → Prop} (h : firstTime P ≠ ⊤) : P (firstTime P).toNat := by
  unfold firstTime at h ⊢
  split_ifs at h ⊢ with hex
  · rw [ENat.toNat_natCast]
    exact Nat.find_spec hex
  · exact absurd rfl h

/-- `firstTime` of the cell-hit predicate is the `firstShellHit` of `Crossing`, when the hit exists. -/
lemma firstTime_eq_firstShellHit {X : ℕ → ℤ} {S : Set ℂ}
    (h : ∃ m, (cell ε η (X m) ∩ S).Nonempty) :
    firstTime (fun m => (cell ε η (X m) ∩ S).Nonempty) =
      ((firstShellHit ε η X S : ℕ) : ℕ∞) := by
  unfold firstTime firstShellHit
  split_ifs with hex
  · congr 1
    exact (Nat.sInf_def (s := {n : ℕ | (cell ε η (X n) ∩ S).Nonempty}) hex).symm
  · exact absurd h hex

/-- The filled set `K = fillCells Θ` of the shells contains each cell `cell k`, `k ∈ Θ`. -/
lemma cell_subset_fillCells {Θ : Finset ℤ} {k : ℤ} (hk : k ∈ Θ) :
    cell ε η k ⊆ fillCells ε η ↑Θ :=
  Set.subset_biUnion_of_mem (u := cell ε η) (Finset.mem_coe.2 hk)

/-- B2 (one inclusion): the cells of the thickening `K + B_r` outside `Θ` lie in the killed set `U`, when
`F0 ⊇ {dd < r}` (named hypothesis of the assembly). Uses `cellVertices_thickening_eq`. -/
lemma cellVertices_thickening_sdiff_subset_killed {Θ F0 : Finset ℤ} {r : ℝ} (hη : Continuous η)
    (hε : 0 < ε) (hF0 : ∀ v : ℤ, dd ε η Θ v < r → v ∈ F0) :
    cellVertices ε η (thickening r (fillCells ε η ↑Θ)) \ ↑Θ ⊆ killed ε η Θ F0 r := by
  rintro v ⟨hv, hΘ⟩
  rw [cellVertices_thickening_eq hη hε Θ r] at hv
  have hd : dd ε η Θ v < r := ENNReal.toReal_lt_of_lt_ofReal hv
  exact ⟨hF0 v hd, hd, fun h => hΘ (Finset.mem_coe.2 h)⟩

end Helpers

end Lemma68ShellPath
end MatedCRT
