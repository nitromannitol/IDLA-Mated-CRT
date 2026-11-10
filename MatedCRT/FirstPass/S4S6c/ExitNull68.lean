import MatedCRT.Audit.StatementsSec3Sec5M1
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationGreen

/-!
# Almost surely finite exit from a finite set (q2, task fp-S4S6c-envscaling-6-7-6-8; LEMMA68 C2)

The start-level input of the good event `GoodEvent68`: for a finite set `A` of vertices and every start `y`, the walk
leaves `A` almost surely, `srwLaw m y {vExitTime A = ⊤} = 0`. It follows from the finiteness of the expected exit time
(`Audit.StatementsSec3Sec5M1.finite_expectedExitTime`, under local finiteness of the multigraph and the consecutive
edges `m k (k+1) ≠ 0`) and `ae_vExitTime_ne_top_of_expectedExitTime_ne_top` (OccupationGreen).

This file imports the Audit chain (`IDLA.StrongMarkov`), so it is kept apart from `MarkovFixedTime`, whose root names
`measurable_pathShift` and `pathShift_zero` clash with those of `IDLA.StrongMarkov`.
-/

open MeasureTheory

namespace MatedCRT

namespace ExitNull68

/-- The exit from a finite set `A` is almost surely finite from every start `y`. -/
theorem exit_null_of_finite {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {A : Set ℤ} (hA : A.Finite) (y : ℤ) :
    srwLaw m y {x | vExitTime A x = ⊤} = 0 := by
  have h := ae_vExitTime_ne_top_of_expectedExitTime_ne_top m A y
    (MatedCRT.Audit.StatementsSec3Sec5M1.finite_expectedExitTime hlf hcons hA y)
  rw [ae_iff] at h
  simpa using h

end ExitNull68

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.ExitNull68.exit_null_of_finite
