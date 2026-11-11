import Mathlib
import MatedCRT.Defs.Map
import MatedCRT.Defs.RandomWalk
import MatedCRT.FirstPass.S6e.Admissible
import MatedCRT.FirstPass.S6r.ShellTest
import MatedCRT.FirstPass.S6r.Window
import MatedCRT.FirstPass.S3S4c

/-!
# Path-level mesh bound up to the exit time

The walk `x` is killed on leaving `killed ε η Θ F0 r` (Admissible.lean); its exit time is
`τ = vExitTime (killed ε η Θ F0 r) x ∈ ℕ ∪ {∞}`. The mesh bound `CellDiamLe ε η (dyadicD r / 100) (ball 0 ρmesh)` is used
only on the cells of the walk vertices `x m` with `m ≤ τ`, and not on the whole plane.

Route (the exact conclusion of `walk_mem_meshBall_upto_vExitTime`).
* For `m < τ`: `x m ∈ killed ⊆ F0` (`S3S4c.lt_vExitTime_iff`), so its cell meets `ball 0 ρ ⊆ ball 0 ρmesh`.
* For `m = τ = n + 1`: `x n ∈ killed` and the cell of `x n` meets `ball 0 ρ`. A point `p` of it and a point `q` of the
  common part of the cells of `x n` and `x (n+1)` (the step `hadj`) satisfy `dist p q ≤ dyadicD r / 100 ≤ ρmesh - ρ` by the
  mesh bound on the cell of `x n`; hence `|q| < ρ + dyadicD r / 100 ≤ ρmesh`, and the exit cell meets `ball 0 ρmesh`.
* For `m = τ = 0`: the start cell meets `ball 0 ρ` (hypothesis `hst`; a start set `K ⊆ ball 0 (ρ / 2)` gives it).

The instance `ρmesh := ρ + dyadicD r / 100` (`diam_upto_vExitTime_exit`) is the radius of the exit-cell mesh bound
`hmeshExit` (MeshExitPw68.lean). No new input: the walk, the killed set and the cells are the definitions.

Terminology: Armstrong-Kuusi-Mourrat (cells `H^ε_a`, mesh), Duplantier-Sheffield (boundary-length parametrisation),
Armitage-Gardiner (balls, open balls `ball 0 ρ`).
-/

open MeasureTheory Set Metric

namespace MatedCRT
namespace Lemma68PathMesh

open Lemma68Admissible Lemma68Window

/-- The walk `x` killed on leaving `killed ε η Θ F0 r` has every vertex `x m`, `m ≤ τ`, in a cell meeting the ball
`ball 0 ρmesh`; the mesh bound is needed only on the cells of the walk up to `τ`. -/
theorem walk_mem_meshBall_upto_vExitTime {ε : ℝ} {η : ℝ → ℂ} {Θ F0 : Finset ℤ} {r ρ ρmesh h : ℝ}
    {x : ℕ → ℤ}
    (hh : 0 ≤ h)
    (hF0 : (F0 : Set ℤ) ⊆ cellVertices ε η (ball (0 : ℂ) ρ))
    (hgap : h ≤ ρmesh - ρ)
    (hmesh : CellDiamLe ε η h (ball (0 : ℂ) ρmesh))
    (hadj : ∀ n : ℕ, (n : ℕ∞) < vExitTime (killed ε η Θ F0 r) x →
      (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    (hst : (cell ε η (x 0) ∩ ball (0 : ℂ) ρ).Nonempty) :
    ∀ m : ℕ, (m : ℕ∞) ≤ vExitTime (killed ε η Θ F0 r) x →
      x m ∈ cellVertices ε η (ball (0 : ℂ) ρmesh) := by
  have hρ : ρ ≤ ρmesh := by linarith
  intro m hm
  by_cases hmτ : (m : ℕ∞) < vExitTime (killed ε η Θ F0 r) x
  · -- `m < τ`: the vertex lies in the killed set, hence in `F0`, hence its cell meets `ball 0 ρ`.
    have hF : x m ∈ F0 := ((S3S4c.lt_vExitTime_iff _ x m).1 hmτ m le_rfl).1
    obtain ⟨p, hp1, hp2⟩ : (cell ε η (x m) ∩ ball (0 : ℂ) ρ).Nonempty := hF0 (Finset.mem_coe.2 hF)
    show (cell ε η (x m) ∩ ball (0 : ℂ) ρmesh).Nonempty
    exact ⟨p, hp1, ball_subset_ball hρ hp2⟩
  · have hτm : (m : ℕ∞) = vExitTime (killed ε η Θ F0 r) x := le_antisymm hm (not_lt.1 hmτ)
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · -- `m = τ = 0`: the start cell meets `ball 0 ρ`.
      subst h0
      obtain ⟨p, hp1, hp2⟩ := hst
      show (cell ε η (x 0) ∩ ball (0 : ℂ) ρmesh).Nonempty
      exact ⟨p, hp1, ball_subset_ball hρ hp2⟩
    · -- `m = τ = n + 1`: the exit cell is adjacent to the cell of `x n`, which meets `ball 0 ρ`.
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hn : (n : ℕ∞) < vExitTime (killed ε η Θ F0 r) x := by
        rw [← hτm]
        exact_mod_cast Nat.lt_succ_self n
      have hnK : x n ∈ killed ε η Θ F0 r := (S3S4c.lt_vExitTime_iff _ x n).1 hn n le_rfl
      obtain ⟨p, hp1, hp2⟩ : (cell ε η (x n) ∩ ball (0 : ℂ) ρ).Nonempty :=
        hF0 (Finset.mem_coe.2 hnK.1)
      obtain ⟨q, hqn, hqn1⟩ := hadj n hn
      have hne : (cell ε η (x n) ∩ ball (0 : ℂ) ρmesh).Nonempty :=
        ⟨p, hp1, ball_subset_ball hρ hp2⟩
      have hdist : dist p q ≤ h := hmesh (x n) hne p hp1 q hqn
      have hpb : dist p 0 < ρ := mem_ball.1 hp2
      have hcomm : dist q p = dist p q := dist_comm q p
      have htri : dist q 0 ≤ dist q p + dist p 0 := dist_triangle q p 0
      have hqb : dist q 0 < ρmesh := by linarith
      show (cell ε η (x (n + 1)) ∩ ball (0 : ℂ) ρmesh).Nonempty
      exact ⟨q, hqn1, mem_ball.2 hqb⟩

/-- The path-level mesh bound: every cell of a walk vertex `x m`, `m ≤ τ`, has diameter at most `h`. This is the form
`hdiam : ∀ n ≤ τ, ∀ p ∈ cell ε η (X n), ∀ q ∈ cell ε η (X n), dist p q ≤ h` of the crossing lemmas
(S6r/Shells/Crossing.lean, S6r/ShellWiring.lean). -/
theorem diam_upto_vExitTime {ε : ℝ} {η : ℝ → ℂ} {Θ F0 : Finset ℤ} {r ρ ρmesh h : ℝ}
    {x : ℕ → ℤ}
    (hh : 0 ≤ h)
    (hF0 : (F0 : Set ℤ) ⊆ cellVertices ε η (ball (0 : ℂ) ρ))
    (hgap : h ≤ ρmesh - ρ)
    (hmesh : CellDiamLe ε η h (ball (0 : ℂ) ρmesh))
    (hadj : ∀ n : ℕ, (n : ℕ∞) < vExitTime (killed ε η Θ F0 r) x →
      (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    (hst : (cell ε η (x 0) ∩ ball (0 : ℂ) ρ).Nonempty) :
    ∀ m : ℕ, (m : ℕ∞) ≤ vExitTime (killed ε η Θ F0 r) x →
      ∀ p ∈ cell ε η (x m), ∀ q ∈ cell ε η (x m), dist p q ≤ h :=
  fun m hm =>
    hmesh (x m) (walk_mem_meshBall_upto_vExitTime hh hF0 hgap hmesh hadj hst m hm)

/-- The instance `ρmesh := ρ + h`: the exit cell of the killed walk is covered by the mesh bound on
`ball 0 (ρ + h)`. With `h = dyadicD r / 100` this is the binder `hmeshExit` of MeshExitPw68.lean. -/
theorem diam_upto_vExitTime_exit {ε : ℝ} {η : ℝ → ℂ} {Θ F0 : Finset ℤ} {r ρ h : ℝ}
    {x : ℕ → ℤ}
    (hh : 0 ≤ h)
    (hF0 : (F0 : Set ℤ) ⊆ cellVertices ε η (ball (0 : ℂ) ρ))
    (hmeshExit : CellDiamLe ε η h (ball (0 : ℂ) (ρ + h)))
    (hadj : ∀ n : ℕ, (n : ℕ∞) < vExitTime (killed ε η Θ F0 r) x →
      (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    (hst : (cell ε η (x 0) ∩ ball (0 : ℂ) ρ).Nonempty) :
    ∀ m : ℕ, (m : ℕ∞) ≤ vExitTime (killed ε η Θ F0 r) x →
      ∀ p ∈ cell ε η (x m), ∀ q ∈ cell ε η (x m), dist p q ≤ h :=
  diam_upto_vExitTime hh hF0 (by linarith) hmeshExit hadj hst

end Lemma68PathMesh
end MatedCRT

#print axioms MatedCRT.Lemma68PathMesh.walk_mem_meshBall_upto_vExitTime
#print axioms MatedCRT.Lemma68PathMesh.diam_upto_vExitTime
#print axioms MatedCRT.Lemma68PathMesh.diam_upto_vExitTime_exit
