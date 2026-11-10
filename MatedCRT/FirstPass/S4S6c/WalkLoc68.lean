import MatedCRT.FirstPass.S4S6c.ShellHdePw68
import MatedCRT.FirstPass.S4S6c.HoneExitGeom68

/-!
# Walk lemmas with the mesh localized to a ball (fp-S4S6c-walk-loc, z12; chat 252 §2, §4)

Localized copies of walk lemmas whose univ-form mesh `CellDiamLe ε η (d / 100) Set.univ` is replaced by the ball form
`CellDiamLe ε η (d / 100) (Metric.ball 0 ρmesh)` with a general `ρmesh` and the gap `d / 100 ≤ ρmesh - ρ`. The consumer
instantiates `d := dyadicD r` and `ρmesh := ρ + dyadicD r / 100` (hmeshExit, MeshExitPw68.lean), which gives the form
`dyadicD r / 100` of the task. The originals are kept unchanged:
* `shellHit_interior_of_mesh_loc`: copy of `shellHit_interior_of_mesh` (HoneExitGeom68.lean:591);
* `hb_ae_of_walk_loc`: copy of `hb_ae_of_walk` (HoneExitGeom68.lean:264); its named hit-cell interiority `hhit` is
  derived from the ball mesh (via `shellHit_interior_of_mesh_loc`) instead of being an input.

No walk-visit input (`walk_mem_meshBall_upto_vExitTime`, PathMesh68.lean) is needed: the mesh is used only on the hit
cell `x t`, and that cell meets the two-sided shell, which lies in `ball 0 ρ` (`twoSidedShell_mem_ball`,
ShellHdePw68.lean:33). So the cell is inside the ball the mesh controls.

Terminology: Armitage-Gardiner (balls and their frontier), Armstrong-Kuusi-Mourrat (cells `H^ε_a`, mesh).
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68WalkLoc

open Lemma68Window Lemma68Omega Lemma68ShellPath Lemma68Admissible

/-- **The hit cell of a shell lies in the interior of the `4R/3`-ball, with the ball mesh.** Copy of
`shellHit_interior_of_mesh` (HoneExitGeom68.lean:591). The hit cell `x t` meets the two-sided shell
`twoSidedShell Kset r (shellOffset s (k+1))` (definition of `shellHit`, S6r/ShellOmega.lean:99). That shell lies in
`ball 0 ρ` (`twoSidedShell_mem_ball`; it needs `Kset ⊆ ball 0 (ρ/2)`, `0 < r ≤ ρ/4`, `shellOffset s (k+1) ≤ r/20`).
So the cell meets `ball 0 ρmesh`, the ball mesh bounds its diameter by `d / 100`, and the path-level lemma
`shellHit_interior_of_cellDiam` (HoneExitGeom68) gives the conclusion. -/
theorem shellHit_interior_of_mesh_loc {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (Kset : Set ℂ)
    {r s d ρ ρmesh : ℝ} {R : ℂ → ℝ}
    (hd : 0 < d) (hK : Kset.Nonempty) (hKb : Kset ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hρ : ρ ≤ ρmesh)
    (hmesh : CellDiamLe ε η (d / 100) (Metric.ball (0 : ℂ) ρmesh))
    (k : ℕ) (x : ℕ → ℤ) (hlam : shellOffset s (k + 1) ≤ r / 20)
    (hR : d ≤ R (shellCentre ε η Kset r s d k x)) (t : ℕ)
    (ht : shellHit ε η Kset r s k x = (t : ℕ∞)) :
    x t ∈ interiorCellVertices ε η
      (ball (shellCentre ε η Kset r s d k x) (4 * R (shellCentre ε η Kset r s d k x) / 3)) := by
  have hfin : shellHit ε η Kset r s k x ≠ ⊤ := by rw [ht]; exact ENat.natCast_ne_top t
  have hdt : (shellHit ε η Kset r s k x).toNat = t := by rw [ht]; simp
  have hsh : (cell ε η (x (shellHit ε η Kset r s k x).toNat)
      ∩ twoSidedShell Kset r (shellOffset s (k + 1))).Nonempty :=
    firstTime_toNat_spec (P := fun m : ℕ => (cell ε η (x m)
      ∩ twoSidedShell Kset r (shellOffset s (k + 1))).Nonempty) hfin
  rw [hdt] at hsh
  obtain ⟨y, hycell, hyS⟩ := hsh
  have hyb : y ∈ Metric.ball (0 : ℂ) ρ :=
    MatedCRT.Lemma68ShellHdePw68.twoSidedShell_mem_ball hK hKb hr hrρ hlam hyS
  have hmeet : (cell ε η (x t) ∩ Metric.ball (0 : ℂ) ρmesh).Nonempty :=
    ⟨y, hycell, Metric.ball_subset_ball hρ hyb⟩
  exact Lemma68HoneExitGeom.shellHit_interior_of_cellDiam hε Kset hd k x hR t ht (hmesh (x t) hmeet)

/-- **`hb` almost surely, with the ball mesh.** Copy of `hb_ae_of_walk` (HoneExitGeom68.lean:264). The named hit-cell
interiority `hhit` is derived from the ball mesh by `shellHit_interior_of_mesh_loc`. The inputs are the centre-radius
bound `hR` (the a.s. form of `d ≤ Rf`, as in `hb_ae_valid_centre_mesh`), the shell geometry `hK`, `hKb`, `hr`, `hrρ`,
and the shell count bound `hNs` (with `0 ≤ s`), from which `shellOffset s (k+1) ≤ r / 20` for `k ≤ n`. -/
theorem hb_ae_of_walk_loc {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε) (Kset : Set ℂ)
    {Rf : ℂ → ℝ} {r s d ρ ρmesh : ℝ} {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {Z : ℕ → (ℕ → ℤ) → ℂ}
    (m : ℤ → ℤ → ℕ) (a : ℤ) (n : ℕ)
    (hdeg : ∀ v, edgeMeasure m v univ ≠ 0 ∧ edgeMeasure m v univ ≠ ⊤)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (cell ε η u) ∩ closure (cell ε η v)).Nonempty)
    (hZ : ∀ k x, Z k x = shellCentre ε η Kset r s d k x)
    (hd : 0 < d) (hK : Kset.Nonempty) (hKb : Kset ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hs0 : 0 ≤ s) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20)
    (hgap : d / 100 ≤ ρmesh - ρ)
    (hmesh : CellDiamLe ε η (d / 100) (Metric.ball (0 : ℂ) ρmesh))
    (hR : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        d ≤ Rf (shellCentre ε η Kset r s d k x)) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        x (shellExit ε η Kset r s d Rf k x).toNat ∈
          cellVertices ε η (sphere (Z k x) (4 * Rf (shellCentre ε η Kset r s d k x) / 3)) := by
  have hρ : ρ ≤ ρmesh := by
    have h0 : 0 ≤ d / 100 := by positivity
    linarith
  have hlam : ∀ k ≤ n, shellOffset s (k + 1) ≤ r / 20 := by
    intro k hk
    have hkn : ((k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hk
    have h1 : 20 * ((k + 1 : ℕ) : ℝ) * s ≤ 20 * ((n + 1 : ℕ) : ℝ) * s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkn (by norm_num)) hs0
    unfold shellOffset
    linarith
  have hhit : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
      ∀ t : ℕ, shellHit ε η Kset r s k x = (t : ℕ∞) →
        x t ∈ interiorCellVertices ε η
          (ball (shellCentre ε η Kset r s d k x) (4 * Rf (shellCentre ε η Kset r s d k x) / 3)) :=
    fun k hk => (hR k hk).mono fun x hx hxm t ht =>
      shellHit_interior_of_mesh_loc hε Kset hd hK hKb hr hrρ hρ hmesh k x (hlam k hk) (hx hxm) t ht
  exact Lemma68HoneExitGeom.hb_ae_of_walk hη Kset m a n hdeg hadj hZ hhit

end Lemma68WalkLoc
end MatedCRT

#print axioms MatedCRT.Lemma68WalkLoc.shellHit_interior_of_mesh_loc
#print axioms MatedCRT.Lemma68WalkLoc.hb_ae_of_walk_loc
