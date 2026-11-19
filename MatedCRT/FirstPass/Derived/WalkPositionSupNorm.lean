import MatedCRT.FirstPass.Derived.InterpolatedWalkShift

/-!
# The supremum norm of a continuous path on `[0, T]`

The sup norm `X ↦ sup_{s ≤ T} |X s|` is a continuous functional of a continuous path for the compact-open
topology, and it dominates the position of the interpolated embedded walk at every time `j / m ≤ T`.  These are the
two facts used to deduce the tightness of the walk position at the step `j_n` from the convergence in law of the
interpolated walk.

* `supNormUpTo`: the sup norm on `[0, T]`.
* `continuous_supNormUpTo`: it is continuous on `C(ℝ≥0, ℂ)`.
* `norm_apply_le_supNormUpTo`: `|X t| ≤ supNormUpTo T X` for `t ≤ T`.
* `norm_vertex_le_supNormUpTo_interpPathCM`: the vertex `v (x j)` visited at the step `j` satisfies
  `|v (x j)| ≤ supNormUpTo T (interpPathCM v hm x)` when `j / m ≤ T`.
-/

namespace MatedCRT.FirstPass.Derived

open scoped NNReal

/-- The supremum norm of a continuous path on `[0, T]`. -/
noncomputable def supNormUpTo (T : ℝ≥0) (X : C(ℝ≥0, ℂ)) : ℝ :=
  ‖X.restrict (Set.Icc (0 : ℝ≥0) T)‖

theorem continuous_supNormUpTo (T : ℝ≥0) : Continuous (supNormUpTo T) :=
  continuous_norm.comp (ContinuousMap.continuous_restrict _)

theorem norm_apply_le_supNormUpTo {T t : ℝ≥0} (ht : t ≤ T) (X : C(ℝ≥0, ℂ)) :
    ‖X t‖ ≤ supNormUpTo T X :=
  (X.restrict (Set.Icc (0 : ℝ≥0) T)).norm_coe_le_norm ⟨t, zero_le, ht⟩

theorem norm_vertex_le_supNormUpTo_interpPathCM (v : ℤ → ℂ) {m : ℝ} (hm : 0 < m) (x : ℕ → ℤ) (j : ℕ)
    {T : ℝ≥0} (hjT : ((j / m : ℝ).toNNReal) ≤ T) :
    ‖v (x j)‖ ≤ supNormUpTo T (interpPathCM v hm.le x) := by
  have := norm_apply_le_supNormUpTo hjT (interpPathCM v hm.le x)
  rwa [interpPathCM_at_stepTime v hm x j] at this

end MatedCRT.FirstPass.Derived
