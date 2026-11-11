import MatedCRT.FirstPass.S6r.ShellOmega
import MatedCRT.FirstPass.S4S6c.WalkBridge68

/-!
# Lemma 6.8, S8' on path space: the shell times as stopping times of the coordinates

The prefix-local shell times of `ShellOmega.lean` (`shellHit`, `shellExit`, `testEnd`) are stopping times of
`coordFiltration` (`WalkBridge68.lean:33`), by `isStoppingTime_of_prefix`. This file imports `WalkBridge68`,
and is split from `ShellOmega.lean` so that the pathwise shell chain (`ShellWiring.lean`) can be imported with
the shell times.
-/

namespace MatedCRT
namespace Lemma68OmegaStop

open Set Metric MeasureTheory
open Lemma68Window Lemma68WalkBridge Lemma68Omega
open scoped Classical

variable (ε : ℝ) (η : ℝ → ℂ) (K : Set ℂ) (r s d : ℝ) (R : ℂ → ℝ)

/-- A prefix-local functional is a stopping time of the coordinate filtration. -/
theorem isStoppingTime_of_prefixLocal {F : (ℕ → ℤ) → ℕ∞} (hF : PrefixLocal F) :
    IsStoppingTime coordFiltration F := by
  refine isStoppingTime_of_prefix F (fun n => ?_)
  refine ⟨{v | F (fun j => if h : j ≤ n then v ⟨j, Nat.lt_succ_of_le h⟩ else 0) ≤ n}, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq]
  have hagree : ∀ j ≤ n, x j = (fun j : ℕ => if h : j ≤ n then
      (fun k : Fin (n + 1) => x k) ⟨j, Nat.lt_succ_of_le h⟩ else 0) j := by
    intro j hj
    simp [hj]
  exact (hF n x _ hagree n le_rfl).1

/-- Notes (7.20)-(7.35) on path space: the shell hit `C_{k+1}` is a stopping time of the coordinates. -/
theorem isStoppingTime_shellHit (k : ℕ) :
    IsStoppingTime coordFiltration (shellHit ε η K r s k) :=
  isStoppingTime_of_prefixLocal (shellHit_prefixLocal ε η K r s k)

/-- The shell exit `T_k` is a stopping time of the coordinates. -/
theorem isStoppingTime_shellExit (k : ℕ) :
    IsStoppingTime coordFiltration (shellExit ε η K r s d R k) :=
  isStoppingTime_of_prefixLocal (shellExit_prefixLocal ε η K r s d R k)

/-- Notes (7.35): the test end `L_k` is a stopping time of the coordinates. -/
theorem isStoppingTime_testEnd (k : ℕ) :
    IsStoppingTime coordFiltration (testEnd ε η K r s d R k) :=
  isStoppingTime_of_prefixLocal (testEnd_prefixLocal ε η K r s d R k)

end Lemma68OmegaStop
end MatedCRT
