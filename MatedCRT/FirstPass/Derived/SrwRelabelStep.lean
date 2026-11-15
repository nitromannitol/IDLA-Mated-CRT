import MatedCRT.FirstPass.Derived.SrwLawMeasurable
import MatedCRT.FirstPass.Derived.BrownianEdgeIntegerShift

/-! # Relabelling multigraph degrees and random-walk steps -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory
open scoped ENNReal

/-- A bijective relabelling preserves the degree, including the infinite-support convention. -/
theorem mdeg_relabel (m : ℤ → ℤ → ℕ) (e : ℤ ≃ ℤ) (a : ℤ) :
    mdeg (fun x y => m (e x) (e y)) a = mdeg m (e a) := by
  exact finsum_comp_equiv e

/-- A bijective relabelling preserves singleton probabilities of the one-step law. -/
theorem srwStep_singleton_relabel (m : ℤ → ℤ → ℕ) (e : ℤ ≃ ℤ) (a b : ℤ) :
    srwStep (fun x y => m (e x) (e y)) a {b} = srwStep m (e a) {e b} := by
  rw [srwStep_singleton, srwStep_singleton]
  rw [e.tsum_eq (fun c => (m (e a) c : ℝ≥0∞))]
  simp only [e.injective.eq_iff]

/-- Translating the boundary paths by an integer mesh shift translates the
one-step probabilities by the same vertex offset. -/
theorem srwStep_bmEdgeCount_timeShift_int (ε : ℝ) (L R : ℝ → ℝ) (m a b : ℤ) :
    srwStep (bmEdgeCount ε (fun t => L (t + ε * m)) (fun t => R (t + ε * m))) a {b} =
      srwStep (bmEdgeCount ε L R) (a + m) {b + m} := by
  let e : ℤ ≃ ℤ := Equiv.addRight m
  have h : bmEdgeCount ε (fun t => L (t + ε * m)) (fun t => R (t + ε * m)) =
      fun x y => bmEdgeCount ε L R (e x) (e y) := by
    funext x y
    exact bmEdgeCount_timeShift_int ε L R m x y
  rw [h]
  exact srwStep_singleton_relabel _ e a b

end MatedCRT
