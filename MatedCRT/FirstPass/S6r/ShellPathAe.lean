import Mathlib
import MatedCRT.FirstPass.S6r.ShellPath
import MatedCRT.Defs.RandomWalk

/-!
# Lemma 6.8 shell inequalities, almost-sure form on the simple random walk (`ShellPathAe`)

`shell_ineqs_path` (ShellPath) gives the four shell-order inequalities of `exitQ_le_pow` pathwise. Here
they are obtained `srwLaw m a`-almost surely, from the almost-sure path facts: nearest-neighbour steps,
the start `x 0 = a`, finite killed exit `vExitTime (killed ..) x ≠ ⊤` (`srw_killed_top_null`, WalkBridge68),
finite shell exits, and eligibility of the shell centres. The four forms are those of the hypotheses
`hTT`, `hLT`, `hcross`, `hend` of `exitQ_le_pow_ae` (S6r/ExitQAe, WalkBridge68) with `T = shellExit`,
`L = testEnd`; this file avoids importing WalkBridge68 (its `measurable_logKernel` clashes with ShellWiring).
-/

open MeasureTheory
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath

namespace MatedCRT
namespace Lemma68ShellPathAe

/-- The four shell-order inequalities of `exitQ_le_pow_ae` for `T = shellExit`, `L = testEnd`, holding
`srwLaw m a`-almost surely, from the almost-sure path facts `hae` and the environment hypotheses. -/
theorem shell_ineqs_ae {ε : ℝ} {η : ℝ → ℂ} {Θ F0 : Finset ℤ} {r s d h : ℝ} {R : ℂ → ℝ} {Elig : ℂ → Prop}
    {n : ℕ} {mm : ℤ → ℤ → ℕ} {a : ℤ}
    (hη : Continuous η) (hε : 0 < ε) (hr : 0 < r) (hs : 0 < s) (hs4 : s ≤ r / 4000) (hd : 0 < d)
    (hh : h ≤ d / 100) (hds : d / 100 ≤ s / 100) (hΘne : Θ.Nonempty)
    (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s) (hF0 : ∀ v : ℤ, dd ε η Θ v < r → v ∈ F0)
    (hmesh : CellDiamLe ε η h Set.univ) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20)
    (hstart : (cell ε η a ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hae : ∀ᵐ x ∂(srwLaw mm a), (∀ j, x (j + 1) = x j + 1 ∨ x (j + 1) = x j - 1) ∧ x 0 = a ∧
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
    hae.mono fun x hx => by
      obtain ⟨hnn, hx0, hτ, hfin, hzE⟩ := hx
      have hst : (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty := by
        rw [hx0]
        exact hstart
      exact shell_ineqs_path hη hε hr hs hs4 hd hh hds hΘne hR hF0 hmesh hNs hnn hst hτ hfin hzE
  exact ⟨fun j hj => hall.mono fun x hx => hx.1 j hj,
    fun j hj => hall.mono fun x hx => hx.2.1 j hj,
    hall.mono fun x hx => hx.2.2.1,
    hall.mono fun x hx => hx.2.2.2⟩

end Lemma68ShellPathAe
end MatedCRT
