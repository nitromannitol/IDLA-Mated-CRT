import MatedCRT.FirstPass.S6r.ShellOmega
import MatedCRT.FirstPass.S6e.Admissible
import MatedCRT.FirstPass.S6e.GeometryId
import MatedCRT.Defs.RandomWalk

/-!
# The shell-order conclusion of Lemma 6.8 (`ShellOrder`)

`ShellOrderAe ε η Θ F0 r s d R n mm a` is the conjunction of the four almost-sure shell-order inequalities for the
simple random walk on the multigraph `mm` from `a`: spacing of the shell exits `T_j ≤ T_{j+1}`, test ends
`L_j ≤ T_{j+1}` (both under `T_{j+1} < τ_U`), and the crossing `T_n < τ_U`, `L_n ≤ τ_U`.

It is defined in a file that does not import WalkBridge68 (GoodAnnulusHF68 clash), so that both the shell chain
(`ShellPathAe`, `ShellEnvAe`) and the exit assembly (`ShellExitFinal`) can use it.
-/

open MeasureTheory
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible

namespace MatedCRT
namespace Lemma68ShellOrder

/-- The four shell-order inequalities for the walk on `mm` from `a` in environment `η`, almost surely on the path. -/
def ShellOrderAe (ε : ℝ) (η : ℝ → ℂ) (Θ F0 : Finset ℤ) (r s d : ℝ) (R : ℂ → ℝ) (n : ℕ)
    (mm : ℤ → ℤ → ℕ) (a : ℤ) : Prop :=
  (∀ j < n, ∀ᵐ x ∂(srwLaw mm a),
      shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x < vExitTime (killed ε η Θ F0 r) x →
        shellExit ε η (fillCells ε η ↑Θ) r s d R j x ≤ shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x) ∧
  (∀ j < n, ∀ᵐ x ∂(srwLaw mm a),
      shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x < vExitTime (killed ε η Θ F0 r) x →
        testEnd ε η (fillCells ε η ↑Θ) r s d R j x ≤ shellExit ε η (fillCells ε η ↑Θ) r s d R (j + 1) x) ∧
  (∀ᵐ x ∂(srwLaw mm a), shellExit ε η (fillCells ε η ↑Θ) r s d R n x < vExitTime (killed ε η Θ F0 r) x) ∧
  (∀ᵐ x ∂(srwLaw mm a), testEnd ε η (fillCells ε η ↑Θ) r s d R n x ≤ vExitTime (killed ε η Θ F0 r) x)

end Lemma68ShellOrder
end MatedCRT
