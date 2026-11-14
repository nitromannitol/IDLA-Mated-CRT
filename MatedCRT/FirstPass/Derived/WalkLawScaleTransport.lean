import MatedCRT.FirstPass.Derived.StoppedWalkScaling
import LatticeProb.Prob.LevyProkhorovLipschitz
import LatticeProb.Prob.PathSpaceScaling

/-!
# Transport of the Lévy–Prokhorov distance of interpolated walks under a space-time scaling

Let `v k = c * v' k` for a constant `c ≥ 1`, a speed factor `lam ≤ 1` and a speed `m'`.  The interpolated
walk of speed `lam * m'` along `v` is `c` times the interpolated walk of speed `m'` along `v'`, run at the
dilated time `lam * t` (`StoppedWalkScaling.stoppedInterp_scale`).  The map `X ↦ c * X (lam * ·)` of
continuous paths is `c`-Lipschitz for the local uniform metric, so it multiplies the Lévy–Prokhorov
distance of image laws by at most `c`.

* `scaleMap c lam`: the map `X ↦ (t ↦ c * X (lam * t))`, `c`-Lipschitz (`lipschitzWith_scaleMap`).
* `levyProkhorovEDist_walk_scale_le`: if the exit time of the walk (law `Pj` or `Pk`) from `A` is at
  least `lam * m' * T0` outside an event of probability at most `κ` with `exp (-T0) < κ`, and the laws of the
  stopped interpolated walks of speed `m'` along `v'` are within `r`, then the laws of the unstopped
  interpolated walks of speed `lam * m'` along `v` are within `κ + (c * r + κ)`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace StoppedWalkScaling

open MeasureTheory Set LatticeProb
open scoped ENNReal NNReal
open MatedCRT.ExitCouplingGlue

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- The space-time scaling `X ↦ (t ↦ c * X (lam * t))` of a continuous path in `ℂ`. -/
noncomputable def scaleMap (c lam : ℝ≥0) (X : C(ℝ≥0, ℂ)) : C(ℝ≥0, ℂ) :=
  (c : ℝ) • timeScalePath lam X

theorem scaleMap_apply (c lam : ℝ≥0) (X : C(ℝ≥0, ℂ)) (t : ℝ≥0) :
    scaleMap c lam X t = (((c : ℝ) : ℂ)) * X (lam * t) := by
  simp [scaleMap, Complex.real_smul]

/-- `X ↦ c * X (lam * ·)` is `c`-Lipschitz for the local uniform metric when `c ≥ 1` and `lam ≤ 1`. -/
theorem lipschitzWith_scaleMap {c lam : ℝ≥0} (hc : 1 ≤ c) (hlam : lam ≤ 1) :
    LipschitzWith c (scaleMap c lam) := by
  have h := (lipschitzWith_smulPath (F := ℂ) hc).comp (lipschitzWith_timeScalePath (E := ℂ) hlam)
  rw [mul_one] at h
  exact h

/-- **Transport of the Lévy–Prokhorov distance of interpolated walks under space-time scaling.** -/
theorem levyProkhorovEDist_walk_scale_le (Pj Pk : Measure (ℕ → ℤ)) (v v' : ℤ → ℂ) {c : ℝ≥0}
    (hc : 1 ≤ c) (hv : ∀ k, v k = ((c : ℝ) : ℂ) * v' k) {lam : ℝ≥0} (hlam : lam ≤ 1) (m' : ℝ≥0)
    (A : Set ℤ) (T0 κ : ℝ≥0) (hκ : Real.exp (-(T0 : ℝ)) < κ)
    (hj : Pj {X | ¬ ∃ n : ℕ, vExitTime A X = n ∧ ((lam * m' : ℝ≥0) : ℝ) * T0 ≤ n} ≤ κ)
    (hk : Pk {X | ¬ ∃ n : ℕ, vExitTime A X = n ∧ ((lam * m' : ℝ≥0) : ℝ) * T0 ≤ n} ≤ κ) {r : ℝ≥0∞}
    (hr : levyProkhorovEDist (Pj.map (stoppedInterp v' m' A)) (Pk.map (stoppedInterp v' m' A)) ≤ r) :
    levyProkhorovEDist (Pj.map (interpPathCM v (lam * m').coe_nonneg))
      (Pk.map (interpPathCM v (lam * m').coe_nonneg)) ≤ (κ : ℝ≥0∞) + ((c : ℝ≥0∞) * r + κ) := by
  have hmeas' : Measurable (stoppedInterp v' m' A) := measurable_stoppedInterp v' m' A
  have hΦ : Measurable (scaleMap c lam) := (lipschitzWith_scaleMap hc hlam).continuous.measurable
  have hcomp : ∀ P : Measure (ℕ → ℤ), P.map (stoppedInterp v (lam * m') A) =
      (P.map (stoppedInterp v' m' A)).map (scaleMap c lam) := by
    intro P
    rw [Measure.map_map hΦ hmeas']
    congr 1
    funext X
    refine ContinuousMap.ext fun t => ?_
    simp only [Function.comp_apply, scaleMap_apply]
    exact stoppedInterp_scale ((c : ℝ)) v v' hv lam m' A X t
  have h1 := levyProkhorovEDist_walk_stop_le Pj v (lam * m') A T0 κ hκ hj
  have h2 := levyProkhorovEDist_walk_stop_le Pk v (lam * m') A T0 κ hκ hk
  have h3 : levyProkhorovEDist (Pj.map (stoppedInterp v (lam * m') A))
      (Pk.map (stoppedInterp v (lam * m') A)) ≤ (c : ℝ≥0∞) * r := by
    rw [hcomp Pj, hcomp Pk]
    exact (levyProkhorovEDist_map_le_of_lipschitz hc (lipschitzWith_scaleMap hc hlam) hΦ _ _).trans
      (mul_le_mul_right hr _)
  calc levyProkhorovEDist (Pj.map (interpPathCM v (lam * m').coe_nonneg))
        (Pk.map (interpPathCM v (lam * m').coe_nonneg))
      ≤ levyProkhorovEDist (Pj.map (interpPathCM v (lam * m').coe_nonneg))
          (Pj.map (stoppedInterp v (lam * m') A)) +
        levyProkhorovEDist (Pj.map (stoppedInterp v (lam * m') A))
          (Pk.map (interpPathCM v (lam * m').coe_nonneg)) := levyProkhorovEDist_triangle _ _ _
    _ ≤ levyProkhorovEDist (Pj.map (interpPathCM v (lam * m').coe_nonneg))
          (Pj.map (stoppedInterp v (lam * m') A)) +
        (levyProkhorovEDist (Pj.map (stoppedInterp v (lam * m') A))
          (Pk.map (stoppedInterp v (lam * m') A)) +
        levyProkhorovEDist (Pk.map (stoppedInterp v (lam * m') A))
          (Pk.map (interpPathCM v (lam * m').coe_nonneg))) :=
        add_le_add le_rfl (levyProkhorovEDist_triangle _ _ _)
    _ ≤ (κ : ℝ≥0∞) + ((c : ℝ≥0∞) * r + κ) := by
        refine add_le_add h1 (add_le_add h3 ?_)
        rw [levyProkhorovEDist_comm]
        exact h2

end StoppedWalkScaling
end MatedCRT
