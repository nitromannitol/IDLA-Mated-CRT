import Mathlib
import MatedCRT.FirstPass.S6r.ShellPath
import MatedCRT.Defs.RandomWalk
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk

/-!
# Lemma 6.8 shell inequalities, almost-sure form on the simple random walk (`ShellPathAe`)

`shell_ineqs_path` (ShellPath) gives the four shell-order inequalities of `exitQ_le_pow` pathwise. Here
they are obtained `srwLaw m a`-almost surely, from the almost-sure path facts: consecutive positions have
intersecting cells (`ae_cell_adjacent`, from the map input `hmap`; not nearest-neighbour steps, which the map's
edges do not satisfy), the start `x 0 = a`, finite killed exit `vExitTime (killed ..) x ≠ ⊤` (`srw_killed_top_null`, WalkBridge68),
finite shell exits, and eligibility of the shell centres. The four forms are those of the hypotheses
`hTT`, `hLT`, `hcross`, `hend` of `exitQ_le_pow_ae` (S6r/ExitQAe, WalkBridge68) with `T = shellExit`,
`L = testEnd`; this file avoids importing WalkBridge68 (its `measurable_logKernel` clashes with ShellWiring).
-/

open MeasureTheory
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath

namespace MatedCRT
namespace Lemma68ShellPathAe

/-- Almost surely, consecutive positions of simple random walk on the multigraph `mm` have intersecting cells, from
the map input `hmap` (every edge `mm j k ≠ 0` joins two intersecting cells) and the legality of the steps
(`srwAeAdjacentStep`: a stay or an edge). Stays are harmless since `cell k ≠ ∅`. -/
theorem ae_cell_adjacent (mm : ℤ → ℤ → ℕ) (a : ℤ) {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε)
    (hmap : ∀ j k : ℤ, mm j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) :
    ∀ᵐ x ∂(srwLaw mm a), ∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty := by
  filter_upwards [srwAeAdjacentStep mm a] with x hx j
  rcases hx j with h | h
  · rw [h, Set.inter_self]
    exact cell_nonempty hε (x j)
  · exact hmap _ _ h

/-- The four shell-order inequalities of `exitQ_le_pow_ae` for `T = shellExit`, `L = testEnd`, holding
`srwLaw m a`-almost surely, from the almost-sure path facts `hae` and the environment hypotheses. -/
theorem shell_ineqs_ae {ε : ℝ} {η : ℝ → ℂ} {Θ F0 : Finset ℤ} {r s d h : ℝ} {R : ℂ → ℝ} {Elig : ℂ → Prop}
    {n : ℕ} {mm : ℤ → ℤ → ℕ} {a : ℤ}
    (hη : Continuous η) (hε : 0 < ε) (hr : 0 < r) (hs : 0 < s) (hs4 : s ≤ r / 4000) (hd : 0 < d)
    (hh : h ≤ d / 100) (hds : d / 100 ≤ s / 100) (hΘne : Θ.Nonempty)
    (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s) (hF0 : ∀ v : ℤ, dd ε η Θ v < r → v ∈ F0)
    (hmesh : CellDiamLe ε η h Set.univ) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20)
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
    ((srwLaw_ae_start mm a).and ((ae_cell_adjacent mm a hε hmap).and hae)).mono fun x hx => by
      obtain ⟨hx0, hadj, hτ, hfin, hzE⟩ := hx
      have hst : (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty := by
        rw [hx0]
        exact hstart
      exact shell_ineqs_path hη hε hr hs hs4 hd hh hds hΘne hR hF0 hmesh hNs hadj hst hτ hfin hzE
  exact ⟨fun j hj => hall.mono fun x hx => hx.1 j hj,
    fun j hj => hall.mono fun x hx => hx.2.1 j hj,
    hall.mono fun x hx => hx.2.2.1,
    hall.mono fun x hx => hx.2.2.2⟩

end Lemma68ShellPathAe
end MatedCRT
