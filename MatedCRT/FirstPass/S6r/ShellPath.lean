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

section Pathwise

variable {ε : ℝ} {η : ℝ → ℂ}

/-- The four shell-order inequalities of `exitQ_le_pow` (S4S6c/WalkBridge68) for the `ShellOmega` times
`T k = shellExit k`, `L k = testEnd k` on one nearest-neighbour path `x` with finite exits (`hfin`), the
hitting shells found by `bad_path_crosses_all_shells`, and the shell chain `shell_chain_pathwise`.
Named inputs: `hF0` (`F0 ⊇ {dd < r}`, B2), `hmesh` (mesh on all cells), `hstart`, `hfin`, `hzE` (eligibility). -/
theorem shell_ineqs_path {Θ F0 : Finset ℤ} {r s d h : ℝ} {R : ℂ → ℝ} {Elig : ℂ → Prop} {n : ℕ} {x : ℕ → ℤ}
    (hη : Continuous η) (hε : 0 < ε) (hr : 0 < r) (hs : 0 < s) (hs4 : s ≤ r / 4000) (hd : 0 < d)
    (hh : h ≤ d / 100) (hds : d / 100 ≤ s / 100) (hΘne : Θ.Nonempty)
    (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s) (hF0 : ∀ v : ℤ, dd ε η Θ v < r → v ∈ F0)
    (hmesh : CellDiamLe ε η h Set.univ) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20)
    (hnn : ∀ m, x (m + 1) = x m + 1 ∨ x (m + 1) = x m - 1)
    (hstart : (cell ε η (x 0) ∩ frontier (thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hτ : vExitTime (killed ε η Θ F0 r) x ≠ ⊤)
    (hfin : ∀ k ≤ n, shellExit ε η (fillCells ε η ↑Θ) r s d R k x ≠ ⊤ ∧
      testEnd ε η (fillCells ε η ↑Θ) r s d R k x ≠ ⊤)
    (hzE : ∀ k ≤ n, Elig (shellCentre ε η (fillCells ε η ↑Θ) r s d k x)) :
    (∀ j < n, shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x < vExitTime (killed ε η Θ F0 r) x →
        shellExit ε η (fillCells ε η ↑Θ) r s d R j x ≤ shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x) ∧
    (∀ j < n, shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x < vExitTime (killed ε η Θ F0 r) x →
        testEnd ε η (fillCells ε η ↑Θ) r s d R j x ≤ shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x) ∧
    shellExit ε η (fillCells ε η ↑Θ) r s d R n x < vExitTime (killed ε η Θ F0 r) x ∧
    testEnd ε η (fillCells ε η ↑Θ) r s d R n x ≤ vExitTime (killed ε η Θ F0 r) x := by
  have hKne : (fillCells ε η ↑Θ).Nonempty := by
    obtain ⟨w, hw⟩ := hΘne
    exact Set.Nonempty.mono (cell_subset_fillCells (ε := ε) (η := η) hw) (cell_nonempty hε w)
  have hΘv : ∀ k ∈ (↑Θ : Set ℤ), cell ε η k ⊆ fillCells ε η ↑Θ :=
    fun k hk => cell_subset_fillCells (Finset.mem_coe.1 hk)
  have hτ' : x (vExitTime (killed ε η Θ F0 r) x).toNat ∉
      cellVertices ε η (thickening r (fillCells ε η ↑Θ)) \ ↑Θ :=
    fun hv => vExitTime_toNat_not_mem hτ (cellVertices_thickening_sdiff_subset_killed hη hε hF0 hv)
  have hhs : h ≤ s / 100 := le_trans hh hds
  obtain ⟨hhit, -, -⟩ := bad_path_crosses_all_shells hKne hε hη hr hs hhs x
    (vExitTime (killed ε η Θ F0 r) x).toNat (n + 1) (↑Θ : Set ℤ) hΘv hτ' (fun m _ => hadj_of_nn hε x hnn m)
    hstart (fun m _ => cell_diam_of_univ hε hmesh (x m)) hNs
  have hex : ∀ k ≤ n, ∃ m, (cell ε η (x m) ∩
      twoSidedShell (fillCells ε η ↑Θ) r (shellOffset s (k + 1))).Nonempty := by
    intro k hk
    obtain ⟨m, -, hm⟩ := hhit (k + 1) (by omega) (by omega)
    exact ⟨m, hm⟩
  have hC : ∀ k ≤ n, shellHit ε η (fillCells ε η ↑Θ) r s k x =
      ((hitTime ε η (fillCells ε η ↑Θ) r s x k : ℕ) : ℕ∞) :=
    fun k hk => firstTime_eq_firstShellHit (hex k hk)
  have hzc : ∀ k ≤ n, shellCentre ε η (fillCells ε η ↑Θ) r s d k x =
      gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k))) := by
    intro k hk
    unfold shellCentre
    rw [hC k hk, ENat.toNat_natCast]
  have hTE : ∀ k ≤ n, ((shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat : ℕ∞) =
      shellExit ε η (fillCells ε η ↑Θ) r s d R k x :=
    fun k hk => ENat.natCast_toNat (hfin k hk).1
  have hLE : ∀ k ≤ n, ((testEnd ε η (fillCells ε η ↑Θ) r s d R k x).toNat : ℕ∞) =
      testEnd ε η (fillCells ε η ↑Θ) r s d R k x :=
    fun k hk => ENat.natCast_toNat (hfin k hk).2
  have hsp : ∀ k ≤ n, shellHit ε η (fillCells ε η ↑Θ) r s k x ≤
      ((shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat : ℕ∞) ∧
      x (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat ∉ interiorCellVertices ε η
        (ball (shellCentre ε η (fillCells ε η ↑Θ) r s d k x)
          (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 3)) :=
    fun k hk => firstTime_toNat_spec (P := fun m => shellHit ε η (fillCells ε η ↑Θ) r s k x ≤ (m : ℕ∞) ∧
      x m ∉ interiorCellVertices ε η (ball (shellCentre ε η (fillCells ε η ↑Θ) r s d k x)
        (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 3))) (hfin k hk).1
  have hCT : ∀ k ≤ n, hitTime ε η (fillCells ε η ↑Θ) r s x k ≤
      (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat := by
    intro k hk
    have h1 := (hsp k hk).1
    rw [hC k hk] at h1
    exact_mod_cast h1
  have hTex : ∀ k ≤ n, x (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat ∉ interiorCellVertices ε η
      (ball (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k))))
        (4 * R (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k)))) / 3)) := by
    intro k hk
    have h1 := (hsp k hk).2
    rw [hzc k hk] at h1
    exact h1
  have hTmin : ∀ k ≤ n, ∀ m, hitTime ε η (fillCells ε η ↑Θ) r s x k ≤ m →
      m < (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat →
      x m ∈ interiorCellVertices ε η (ball (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k))))
        (4 * R (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k)))) / 3)) := by
    intro k hk m hm1 hm2
    have hm3 : (m : ℕ∞) < shellExit ε η (fillCells ε η ↑Θ) r s d R k x := by
      rw [← hTE k hk]
      exact_mod_cast hm2
    by_contra hcon
    apply not_of_lt_firstTime (P := fun m => shellHit ε η (fillCells ε η ↑Θ) r s k x ≤ (m : ℕ∞) ∧
      x m ∉ interiorCellVertices ε η (ball (shellCentre ε η (fillCells ε η ↑Θ) r s d k x)
        (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 3))) hm3
    refine ⟨?_, ?_⟩
    · rw [hC k hk]
      exact_mod_cast hm1
    · rw [hzc k hk]
      exact hcon
  have hTL : ∀ k ≤ n, (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat ≤
      (testEnd ε η (fillCells ε η ↑Θ) r s d R k x).toNat := by
    intro k hk
    have h1 : shellExit ε η (fillCells ε η ↑Θ) r s d R k x ≤
        ((testEnd ε η (fillCells ε η ↑Θ) r s d R k x).toNat : ℕ∞) :=
      (firstTime_toNat_spec (P := fun m => shellExit ε η (fillCells ε η ↑Θ) r s d R k x ≤ (m : ℕ∞) ∧
        x m ∉ interiorCellVertices ε η (ball (vertexPoint ε η (x (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat))
          (R (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 4))) (hfin k hk).2).1
    rw [← hTE k hk] at h1
    exact_mod_cast h1
  have hLmin : ∀ k ≤ n, ∀ m, (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat ≤ m →
      m < (testEnd ε η (fillCells ε η ↑Θ) r s d R k x).toNat →
      x m ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat))
        (R (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k)))) / 4)) := by
    intro k hk m hm1 hm2
    have hm3 : (m : ℕ∞) < testEnd ε η (fillCells ε η ↑Θ) r s d R k x := by
      rw [← hLE k hk]
      exact_mod_cast hm2
    have hm4 : shellExit ε η (fillCells ε η ↑Θ) r s d R k x ≤ (m : ℕ∞) := by
      rw [← hTE k hk]
      exact_mod_cast hm1
    by_contra hcon
    apply not_of_lt_firstTime (P := fun m => shellExit ε η (fillCells ε η ↑Θ) r s d R k x ≤ (m : ℕ∞) ∧
      x m ∉ interiorCellVertices ε η (ball (vertexPoint ε η (x (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat))
        (R (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 4))) hm3
    refine ⟨hm4, ?_⟩
    rw [hzc k hk]
    exact hcon
  have hLex : ∀ k ≤ n, x (testEnd ε η (fillCells ε η ↑Θ) r s d R k x).toNat ∉ interiorCellVertices ε η
      (ball (vertexPoint ε η (x (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat))
        (R (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k)))) / 4)) := by
    intro k hk
    have h1 := (firstTime_toNat_spec (P := fun m => shellExit ε η (fillCells ε η ↑Θ) r s d R k x ≤ (m : ℕ∞) ∧
      x m ∉ interiorCellVertices ε η (ball (vertexPoint ε η (x (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat))
        (R (shellCentre ε η (fillCells ε η ↑Θ) r s d k x) / 4))) (hfin k hk).2).2
    rw [← hzc k hk]
    exact h1
  have hzElig : ∀ k ≤ n, Elig (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k)))) := by
    intro k hk
    have h1 := hzE k hk
    rw [hzc k hk] at h1
    exact h1
  have hmesh' : ∀ k ≤ n, CellDiamLe ε η h (ball (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k)))) (2 * R (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k)))))) :=
    fun k _ => cellDiamLe_of_univ hmesh _
  obtain ⟨hTTL, -, hTn, hLn⟩ := shell_chain_pathwise (K := fillCells ε η ↑Θ) (Θv := (↑Θ : Set ℤ))
    (x := x) (n := n) (τ := (vExitTime (killed ε η Θ F0 r) x).toNat)
    hKne hη hε hr hs hs4 hd hh hds (fun m => hadj_of_nn hε x hnn m) hΘv hτ' hstart
    (fun m _ => cell_diam_of_univ hε hmesh (x m)) hNs R Elig hR
    (fun k => gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k))))
    (fun k _ => rfl) hzElig hmesh'
    (fun k => (shellExit ε η (fillCells ε η ↑Θ) r s d R k x).toNat)
    (fun k => (testEnd ε η (fillCells ε η ↑Θ) r s d R k x).toNat)
    hCT hTmin hTex hTL hLmin hLex
  refine ⟨fun j hj _ => ?_, fun j hj _ => ?_, ?_, ?_⟩
  · calc shellExit ε η (fillCells ε η ↑Θ) r s d R j x
        = ((shellExit ε η (fillCells ε η ↑Θ) r s d R j x).toNat : ℕ∞) := (hTE j (by omega)).symm
      _ ≤ ((shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x).toNat : ℕ∞) := by
          exact_mod_cast (hTTL j hj).1
      _ = shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x := hTE (j + 1) (by omega)
  · calc testEnd ε η (fillCells ε η ↑Θ) r s d R j x
        = ((testEnd ε η (fillCells ε η ↑Θ) r s d R j x).toNat : ℕ∞) := (hLE j (by omega)).symm
      _ ≤ ((shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x).toNat : ℕ∞) := by
          exact_mod_cast (hTTL j hj).2
      _ = shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x := hTE (j + 1) (by omega)
  · calc shellExit ε η (fillCells ε η ↑Θ) r s d R n x
        = ((shellExit ε η (fillCells ε η ↑Θ) r s d R n x).toNat : ℕ∞) := (hTE n le_rfl).symm
      _ < ((vExitTime (killed ε η Θ F0 r) x).toNat : ℕ∞) := by exact_mod_cast hTn
      _ = vExitTime (killed ε η Θ F0 r) x := ENat.natCast_toNat hτ
  · calc testEnd ε η (fillCells ε η ↑Θ) r s d R n x
        = ((testEnd ε η (fillCells ε η ↑Θ) r s d R n x).toNat : ℕ∞) := (hLE n le_rfl).symm
      _ ≤ ((vExitTime (killed ε η Θ F0 r) x).toNat : ℕ∞) := by exact_mod_cast hLn
      _ = vExitTime (killed ε η Θ F0 r) x := ENat.natCast_toNat hτ

end Pathwise

end Lemma68ShellPath
end MatedCRT
