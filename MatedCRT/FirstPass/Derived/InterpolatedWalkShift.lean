import MatedCRT.FirstPass.Derived.InterpolatedWalkPath
import LatticeProb.Prob.MarkovStepShiftedPath

/-!
# The time shift of the interpolated embedded walk at a step time

For a labelling `v : ℤ → ℂ` of the vertices, a speed `m > 0` and a walk `x : ℕ → ℤ`, shifting the
interpolated embedded walk `interpPathCM v hm x` (a continuous path `ℝ≥0 → ℂ`) by the time `k / m`
is the interpolated embedded walk of the shifted walk `j ↦ x (k + j)`: the shifted path starts at the
vertex `v (x k)` and the interpolation of the remaining steps is unchanged.  This is the step of the
Markov property of the quenched walk law that connects the Markov property of the walk on the vertices
(BG20 Lemma 7.4, Markov step) with the shift `LatticeProb.pathShift` of paths.

* `MatedCRT.linInterp_natCast_add`: `linInterp a (k + r) = linInterp (j ↦ a (k + j)) r` for `r ≥ 0`.
* `MatedCRT.pathShift_interpPathCM`: `pathShift (interpPathCM v hm x) (k / m) = interpPathCM v hm (j ↦ x (k + j))`.
* `MatedCRT.interpPathCM_at_stepTime`: the position of the interpolated walk at the time `k / m` is `v (x k)`.
-/

open Filter Topology MarkovProcess LatticeProb
open scoped NNReal

namespace MatedCRT

/-- Interpolation of a sequence at the time `k + r`, `r ≥ 0`, is the interpolation of the shifted
sequence at the time `r`. -/
theorem linInterp_natCast_add (a : ℕ → ℂ) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    linInterp a ((k : ℝ) + r) = linInterp (fun j => a (k + j)) r := by
  have hfl : ⌊(k : ℝ) + r⌋₊ = k + ⌊r⌋₊ := by
    rw [add_comm, Nat.floor_add_natCast hr, add_comm]
  have hfr : (k : ℝ) + r - ((k + ⌊r⌋₊ : ℕ) : ℝ) = r - (⌊r⌋₊ : ℝ) := by push_cast; ring
  unfold linInterp
  rw [hfl, hfr, add_assoc]

/-- The shifted interpolated embedded walk is the interpolated embedded walk of the shifted walk. -/
theorem pathShift_interpPathCM (v : ℤ → ℂ) {m : ℝ} (hm : 0 < m) (x : ℕ → ℤ) (k : ℕ) :
    pathShift (interpPathCM v hm.le x) ((k / m : ℝ).toNNReal) =
      interpPathCM v hm.le (fun j => x (k + j)) := by
  ext u
  simp only [pathShift_apply, interpPathCM_apply, interpPathFn]
  have hk : 0 ≤ (k : ℝ) / m := div_nonneg (Nat.cast_nonneg k) hm.le
  have h1 : m * (((k / m : ℝ).toNNReal + u : ℝ≥0) : ℝ) = (k : ℝ) + m * (u : ℝ) := by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hk, mul_add, mul_div_cancel₀ _ hm.ne']
  rw [h1]
  exact linInterp_natCast_add (fun j => v (x j)) k (mul_nonneg hm.le u.2)

/-- At the time `k / m` the interpolated embedded walk is at the vertex `v (x k)`. -/
theorem interpPathCM_at_stepTime (v : ℤ → ℂ) {m : ℝ} (hm : 0 < m) (x : ℕ → ℤ) (k : ℕ) :
    interpPathCM v hm.le x ((k / m : ℝ).toNNReal) = v (x k) := by
  have hk : 0 ≤ (k : ℝ) / m := div_nonneg (Nat.cast_nonneg k) hm.le
  have h1 : m * (((k / m : ℝ).toNNReal : ℝ≥0) : ℝ) = (k : ℝ) := by
    rw [Real.coe_toNNReal _ hk, mul_div_cancel₀ _ hm.ne']
  simp only [interpPathCM_apply, interpPathFn]
  rw [h1]
  simp [linInterp]

end MatedCRT
