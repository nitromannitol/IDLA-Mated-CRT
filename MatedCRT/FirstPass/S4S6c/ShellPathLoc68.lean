import MatedCRT.FirstPass.S4S6c.ShellHde68
import MatedCRT.FirstPass.S6r.ShellPathAe

/-!
# Localized mesh copies of the shell path lemmas (chat 252 §5, §6; fp-S4S6c-shellpath-loc, z8)

The shell path lemmas use a mesh bound on all cells, `CellDiamLe ε η h Set.univ`, but the crossing argument needs it
only along the walk up to its killed exit time and on the shell balls (chat 252, `notes/fp-gaps/CHATGPT-252-idla-z12-mesh-radius-PRO.md`).
This file holds localized copies, with suffix `_meshBall`, of
* `shell_fin_of_path` (`S4S6c/ShellHde68.lean:209`), with the pathwise bound `hdiam` (chat 252 §5);
* `shell_ineqs_path` (`S6r/ShellPath.lean:136`) and `shell_ineqs_ae` (`S6r/ShellPathAe.lean:40`), with the pair
  `hdiam` (pathwise, chat 252 §6) and `hmeshShell` (the per-shell-ball mesh consumed by `shell_chain_pathwise`).

The originals are unchanged. The copies differ from the originals only in the mesh hypotheses and in the sites where
they are consumed; the proofs are otherwise the same. The almost-sure version takes `hdiam` and `hmeshShell` as
almost-sure statements, pathwise in the walk.

Terminology: shells and cell distance (Duplantier-Sheffield); good annuli and the shell chain (Armstrong-Kuusi-Mourrat).
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68ShellPathAe MatedCRT.Lemma68ShellHde68 MatedCRT.Lemma68Geometry

namespace MatedCRT
namespace Lemma68ShellPathLoc68

section Pathwise

variable {ε : ℝ} {η : ℝ → ℂ}

/-- The four shell-order inequalities of `exitQ_le_pow` (S4S6c/WalkBridge68) for the `ShellOmega` times
`T k = shellExit k`, `L k = testEnd k` on one path `x` with intersecting consecutive cells `hadj` and finite exits (`hfin`), the
hitting shells found by `bad_path_crosses_all_shells`, and the shell chain `shell_chain_pathwise`.
Named inputs: `hF0` (`F0 ⊇ {dd < r}`, B2), `hdiam` (mesh on the walk's cells up to its exit time) and `hmeshShell`
(mesh on the shell balls), which replace the universal `hmesh` (chat 252 §6), `hstart`, `hfin`, `hzE` (eligibility). -/
theorem shell_ineqs_path_meshBall {Θ F0 : Finset ℤ} {r s d h : ℝ} {R : ℂ → ℝ} {Elig : ℂ → Prop} {n : ℕ} {x : ℕ → ℤ}
    (hη : Continuous η) (hε : 0 < ε) (hr : 0 < r) (hs : 0 < s) (hs4 : s ≤ r / 4000) (hd : 0 < d)
    (hh : h ≤ d / 100) (hds : d / 100 ≤ s / 100) (hΘne : Θ.Nonempty)
    (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s) (hF0 : ∀ v : ℤ, dd ε η Θ v < r → v ∈ F0)
    (hdiam : ∀ m ≤ (vExitTime (killed ε η Θ F0 r) x).toNat,
      ∀ p ∈ cell ε η (x m), ∀ q ∈ cell ε η (x m), dist p q ≤ h)
    (hmeshShell : ∀ k ≤ n, CellDiamLe ε η h (ball (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k)))) (2 * R (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k))))))) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20)
    (hadj : ∀ m, (cell ε η (x m) ∩ cell ε η (x (m + 1))).Nonempty)
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
    (vExitTime (killed ε η Θ F0 r) x).toNat (n + 1) (↑Θ : Set ℤ) hΘv hτ' (fun m _ => hadj m)
    hstart (fun m hm => hdiam m hm) hNs
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
  obtain ⟨hTTL, -, hTn, hLn⟩ := shell_chain_pathwise (K := fillCells ε η ↑Θ) (Θv := (↑Θ : Set ℤ))
    (x := x) (n := n) (τ := (vExitTime (killed ε η Θ F0 r) x).toNat)
    hKne hη hε hr hs hs4 hd hh hds (fun m => hadj m) hΘv hτ' hstart
    (fun m hm => hdiam m hm) hNs R Elig hR
    (fun k => gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k))))
    (fun k _ => rfl) hzElig hmeshShell
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

/-- The four shell-order inequalities of `exitQ_le_pow_ae` for `T = shellExit`, `L = testEnd`, holding
`srwLaw m a`-almost surely, from the almost-sure path facts `hae` and the environment hypotheses. -/
theorem shell_ineqs_ae_meshBall {ε : ℝ} {η : ℝ → ℂ} {Θ F0 : Finset ℤ} {r s d h : ℝ} {R : ℂ → ℝ} {Elig : ℂ → Prop}
    {n : ℕ} {mm : ℤ → ℤ → ℕ} {a : ℤ}
    (hη : Continuous η) (hε : 0 < ε) (hr : 0 < r) (hs : 0 < s) (hs4 : s ≤ r / 4000) (hd : 0 < d)
    (hh : h ≤ d / 100) (hds : d / 100 ≤ s / 100) (hΘne : Θ.Nonempty)
    (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s) (hF0 : ∀ v : ℤ, dd ε η Θ v < r → v ∈ F0)
    (hdiam : ∀ᵐ x ∂(srwLaw mm a), ∀ m ≤ (vExitTime (killed ε η Θ F0 r) x).toNat,
      ∀ p ∈ cell ε η (x m), ∀ q ∈ cell ε η (x m), dist p q ≤ h)
    (hmeshShell : ∀ᵐ x ∂(srwLaw mm a), ∀ k ≤ n, CellDiamLe ε η h (ball (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k)))) (2 * R (gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η (fillCells ε η ↑Θ) r s x k)))))))
    (hNs : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20)
    (hstart : (cell ε η a ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hmap : ∀ j k : ℤ, mm j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hae : ∀ᵐ x ∂(srwLaw mm a),
      vExitTime (killed ε η Θ F0 r) x ≠ ⊤ ∧
      (∀ k ≤ n, shellExit ε η (fillCells ε η ↑Θ) r s d R k x ≠ ⊤ ∧
        testEnd ε η (fillCells ε η ↑Θ) r s d R k x ≠ ⊤) ∧
      (∀ k ≤ n, Elig (shellCentre ε η (fillCells ε η ↑Θ) r s d k x))) :
    (∀ j < n, ∀ᵐ x ∂(srwLaw mm a),
      shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x < vExitTime (killed ε η Θ F0 r) x →
        shellExit ε η (fillCells ε η ↑Θ) r s d R j x ≤ shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x) ∧
    (∀ j < n, ∀ᵐ x ∂(srwLaw mm a),
      shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x < vExitTime (killed ε η Θ F0 r) x →
        testEnd ε η (fillCells ε η ↑Θ) r s d R j x ≤ shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x) ∧
    (∀ᵐ x ∂(srwLaw mm a),
      shellExit ε η (fillCells ε η ↑Θ) r s d R n x < vExitTime (killed ε η Θ F0 r) x) ∧
    (∀ᵐ x ∂(srwLaw mm a),
      testEnd ε η (fillCells ε η ↑Θ) r s d R n x ≤ vExitTime (killed ε η Θ F0 r) x) := by
  have hall : ∀ᵐ x ∂(srwLaw mm a),
      ((∀ j < n, shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x < vExitTime (killed ε η Θ F0 r) x →
        shellExit ε η (fillCells ε η ↑Θ) r s d R j x ≤ shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x) ∧
      (∀ j < n, shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x < vExitTime (killed ε η Θ F0 r) x →
        testEnd ε η (fillCells ε η ↑Θ) r s d R j x ≤ shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x) ∧
      shellExit ε η (fillCells ε η ↑Θ) r s d R n x < vExitTime (killed ε η Θ F0 r) x ∧
      testEnd ε η (fillCells ε η ↑Θ) r s d R n x ≤ vExitTime (killed ε η Θ F0 r) x) :=
    ((srwLaw_ae_start mm a).and ((ae_cell_adjacent mm a hε hmap).and (hae.and (hdiam.and hmeshShell)))).mono
    fun x hx => by
      obtain ⟨hx0, hadj, ⟨hτ, hfin, hzE⟩, hdx, hmx⟩ := hx
      have hst : (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty := by
        rw [hx0]
        exact hstart
      exact shell_ineqs_path_meshBall hη hε hr hs hs4 hd hh hds hΘne hR hF0 hdx hmx hNs hadj hst hτ hfin hzE
  exact ⟨fun j hj => hall.mono fun x hx => hx.1 j hj,
    fun j hj => hall.mono fun x hx => hx.2.1 j hj,
    hall.mono fun x hx => hx.2.2.1,
    hall.mono fun x hx => hx.2.2.2⟩


/-- **The shell hit, pathwise, with the pathwise mesh bound (deterministic).** Localized copy of `shell_fin_of_path`
(ShellHde68.lean:209, chat 252 §5): the universal mesh `CellDiamLe ε η (d / 100) Set.univ` is replaced by `hdiam`;
the original is unchanged. For a path `x` whose consecutive cells meet, with the killed exit `τ = vExitTime
(killed Θ F0 r) x` finite and the start cell meeting the frontier of the `r/2`-thickening, every shell index `k ≤ n` has
`T_k = shellExit k x ≠ ⊤` and `z_k = shellCentre k x ∈ shortEligible ρ d s`. Here `s = d ^ a`. -/
theorem shell_fin_of_path_meshBall {η : ℝ → ℂ} {ε : ℝ} (hη : Continuous η) (hε : 0 < ε)
    {Θ F0 : Finset ℤ} {ρ r d a : ℝ} {R : ℂ → ℝ} {n : ℕ} (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d)
    (hds : d ≤ d ^ a) (hs4 : d ^ a ≤ r / 4000) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * d ^ a ≤ r / 20)
    (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) (hKb : fillCells ε η ↑Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hRS : ∀ w ∈ shortEligible ρ d a, d ≤ R w ∧ R w ≤ d ^ a)
    {x : ℕ → ℤ}
    (hdiam : ∀ m ≤ (vExitTime (killed ε η Θ F0 r) x).toNat,
      ∀ p ∈ cell ε η (x m), ∀ q ∈ cell ε η (x m), dist p q ≤ d / 100)
    (hadj : ∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty)
    (hst : (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hτ : vExitTime (killed ε η Θ F0 r) x ≠ ⊤) :
    ∀ k ≤ n, shellExit ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x ≠ ⊤ ∧
      shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x ∈ shortEligible ρ d a := by
  intro k hk
  have hKne : (fillCells ε η ↑Θ).Nonempty := ⟨0, h0⟩
  have hs : 0 < d ^ a := Real.rpow_pos_of_pos hd a
  have hlam0 : 0 < shellOffset (d ^ a) (k + 1) := by
    unfold shellOffset
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.2 (Nat.succ_pos k))) hs
  have hlam1 : shellOffset (d ^ a) (k + 1) ≤ r / 20 := by
    unfold shellOffset
    have hk' : ((k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hk
    have hm := mul_le_mul_of_nonneg_right hk' (show (0 : ℝ) ≤ 20 * d ^ a by positivity)
    linarith
  -- the start level 0 and the exit level at least r/2
  obtain ⟨p, hp, hpf⟩ := hst
  have hpinf : Metric.infDist p (fillCells ε η ↑Θ) = r / 2 := infDist_eq_of_mem_frontier hKne hpf
  have hτn : x (vExitTime (killed ε η Θ F0 r) x).toNat ∉ killed ε η Θ F0 r :=
    vExitTime_toNat_not_mem hτ
  obtain ⟨q, hq, hqf⟩ := level_ge_of_not_killed hε hη hr hrρ hF0 hKne hKb hτn
  have hf : Continuous (fun y : ℂ => |Metric.infDist y (fillCells ε η ↑Θ) - r / 2|) :=
    continuous_abs.comp ((Metric.continuous_infDist_pt _).sub continuous_const)
  obtain ⟨i, hi, y, hyc, hy⟩ := exists_index_level hη hε hadj hf hp hq
    (c := shellOffset (d ^ a) (k + 1))
    (by
      show |Metric.infDist p (fillCells ε η ↑Θ) - r / 2| ≤ shellOffset (d ^ a) (k + 1)
      rw [hpinf, sub_self, abs_zero]
      exact hlam0.le)
    (by
      show shellOffset (d ^ a) (k + 1) ≤ |Metric.infDist q (fillCells ε η ↑Θ) - r / 2|
      linarith)
  have hyshell : y ∈ twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1)) := hy
  -- the first hit is at most the killed exit time
  set τ : ℕ := (vExitTime (killed ε η Θ F0 r) x).toNat with hτ_def
  have hitle : shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x ≤ (τ : ℕ∞) := by
    unfold shellHit
    exact (firstTime_le_iff _ τ).2 ⟨i, hi, y, hyc, hyshell⟩
  have hCfin : shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top τ) hitle
  set C : ℕ := (shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x).toNat with hC_def
  have hCspec : (cell ε η (x C) ∩ twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1))).Nonempty :=
    firstTime_toNat_spec (P := fun m => (cell ε η (x m) ∩
      twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1))).Nonempty) hCfin
  obtain ⟨y0, hy0c, hy0⟩ := hCspec
  -- the centre is within 2d/100 of the shell
  have hCle : C ≤ (vExitTime (killed ε η Θ F0 r) x).toNat := by
    have h1 : (C : ℕ∞) ≤ ((vExitTime (killed ε η Θ F0 r) x).toNat : ℕ∞) := by
      rw [hC_def, ENat.natCast_toNat hCfin]
      exact hitle
    exact_mod_cast h1
  have hw : vertexPoint ε η (x C) ∈ cell ε η (x C) := vertexPoint_mem_cell_nonneg hε.le η (x C)
  have hwy : dist (vertexPoint ε η (x C)) y0 ≤ d / 100 :=
    hdiam C hCle _ hw _ hy0c
  have hz_def : shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x
      = Lemma68Window.gridRound (d / 100) (vertexPoint ε η (x C)) := rfl
  have hzy : dist (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) y0 ≤ 2 * (d / 100) := by
    rw [hz_def]
    have h1 := Lemma68Window.dist_gridRound_le (g := d / 100) (div_pos hd (by norm_num))
      (vertexPoint ε η (x C))
    have h2 := dist_triangle (Lemma68Window.gridRound (d / 100) (vertexPoint ε η (x C)))
      (vertexPoint ε η (x C)) y0
    linarith
  have hz_bd := centre_norm_bounds h0 hKb hlam1 hy0 hzy hr hrρ hd hds hs4
  -- the centre lies in the eligible set Z_d
  have hzS : shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x ∈ shortEligible ρ d a := by
    obtain ⟨m, nn, hmn⟩ := gridRound_mem_grid (g := d / 100) (vertexPoint ε η (x C))
    refine ⟨⟨mem_ball_zero_iff.2 hz_bd.2, fun h => ?_⟩, m, nn, ?_⟩
    · have := mem_ball_zero_iff.1 h
      linarith [hz_bd.1]
    · rw [hz_def]
      exact hmn
  obtain ⟨hRlo, hRhi⟩ := hRS _ hzS
  have hR0 : 0 < R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) := lt_of_lt_of_le hd hRlo
  -- the walk at the killed exit time is outside the exit ball
  have hxτB : x τ ∉ interiorCellVertices ε η
      (Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
        (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) / 3)) := by
    intro hmem
    exact hτn (cell_meets_ball_mem_killed hη hε hF0 h0 hy0 hlam1 hzy hz_bd.2 hR0 hRhi hds hs4 hd hr hrρ
      (mem_interiorCellVertices_iff.1 hmem).1)
  have hexit : shellExit ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x ≤ (τ : ℕ∞) := by
    unfold shellExit
    exact (firstTime_le_iff _ τ).2 ⟨τ, le_rfl, hitle, hxτB⟩
  exact ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top τ) hexit, hzS⟩


end Lemma68ShellPathLoc68
end MatedCRT
