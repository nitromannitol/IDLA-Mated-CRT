import MatedCRT.FirstPass.Derived.SrwLawMeasurable
import MatedCRT.Proofs.WalkPotential.Markov
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement

/-! # Multigraph and cell random-walk transitions -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS
open scoped ENNReal

/-- Matching conductance and positive degree identify a multigraph step with a cell step. -/
theorem srwStep_singleton_eq_cell_transition
    (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m) (H : CellConfig)
    (e : ℤ ≃ H.cells) (a b : ℤ) (hdeg : 0 < mdeg m a)
    (hc : H.c (e a) (e b) = (m a b : ℝ))
    (hpi : H.pi (e a) = (mdeg m a : ℝ)) :
    srwStep m a {b} = ENNReal.ofReal (H.transition (e a) (e b)) := by
  have hsum : (∑' c, (m a c : ℝ≥0∞)) = (mdeg m a : ℝ≥0∞) := by
    rw [← edgeMeasure_univ_eq_tsum, edgeMeasure_univ hlf]
  have hne : (mdeg m a : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdeg)
  rw [srwStep_singleton, hsum]
  rw [CellConfig.transition, hc, hpi,
    ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hdeg), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]
  rw [ite_eq_left ⟨hne, ENNReal.natCast_ne_top _⟩]

end MatedCRT
