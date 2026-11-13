import MatedCRT.FirstPass.Derived.ExitCouplingGlue

/-!
# Scaling and stopping of the interpolated walk (Berestycki–Gwynne (2020), §6.4)

Two deterministic facts about the interpolated embedded walk used to compare the stopped walk with
the unstopped walk and to transport the walk of a cone-rescaled environment.

* `interpPathCM_scale`, `stoppedInterp_scale` (time and space covariance): if `v k = c * v' k` for all
  vertices `k`, then for a speed factor `lam` and a speed `m`, the path of speed `lam * m` for `v`
  is `t ↦ c * (path of speed m for v') (lam * t)`, and the same holds for the walks stopped at their
  exit time from a vertex set.
* `levyProkhorovEDist_walk_stop_le`: the Lévy–Prokhorov edistance (local uniform metric) between the
  laws of the interpolated walk and of the interpolated walk stopped at its exit time from `A` is at
  most `r`, as soon as the exit time is at least `m * T0` and finite outside an event of
  probability at most `r`, and `exp (-T0) < r`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace StoppedWalkScaling

open MeasureTheory Set LatticeProb
open scoped ENNReal NNReal
open MatedCRT.ExitCouplingGlue

/-! ### Time and space covariance -/

theorem interpPathFn_mul_speed (v : ℤ → ℂ) (lam m : ℝ≥0) (x : ℕ → ℤ) (t : ℝ≥0) :
    interpPathFn v ((lam * m : ℝ≥0) : ℝ) x t = interpPathFn v m x (lam * t) := by
  unfold interpPathFn
  congr 1
  push_cast
  ring

theorem interpPathFn_vertex_smul (c : ℝ) (v v' : ℤ → ℂ) (hv : ∀ k, v k = (c : ℂ) * v' k)
    (m : ℝ) (x : ℕ → ℤ) (t : ℝ≥0) :
    interpPathFn v m x t = (c : ℂ) * interpPathFn v' m x t := by
  unfold interpPathFn linInterp
  simp only [hv]
  ring

/-- **Time dilation and scaling of the interpolated walk.**  If `v = c • v'` then the interpolated
walk of speed `lam * m` for `v` is the time dilation by `lam` of `c` times the interpolated walk of
speed `m` for `v'`. -/
theorem interpPathCM_scale (c : ℝ) (v v' : ℤ → ℂ) (hv : ∀ k, v k = (c : ℂ) * v' k) (lam m : ℝ≥0)
    (x : ℕ → ℤ) (t : ℝ≥0) :
    interpPathCM v (lam * m).coe_nonneg x t =
      (c : ℂ) * interpPathCM v' m.coe_nonneg x (lam * t) := by
  simp only [interpPathCM_apply]
  rw [interpPathFn_vertex_smul c v v' hv, interpPathFn_mul_speed]

theorem mul_min_div_speed (lam m τ t : ℝ≥0) :
    lam * min t (τ / (lam * m)) = min (lam * t) (τ / m) := by
  rcases eq_or_ne lam 0 with h0 | h0
  · subst h0
    simp
  · rw [mul_min_of_nonneg _ _ (zero_le), ← mul_div_assoc, mul_div_mul_left _ _ h0]

/-- **Time dilation and scaling of the stopped interpolated walk.** -/
theorem stoppedInterp_scale (c : ℝ) (v v' : ℤ → ℂ) (hv : ∀ k, v k = (c : ℂ) * v' k)
    (lam m : ℝ≥0) (A : Set ℤ) (X : ℕ → ℤ) (t : ℝ≥0) :
    stoppedInterp v (lam * m) A X t = (c : ℂ) * stoppedInterp v' m A X (lam * t) := by
  unfold stoppedInterp
  simp only [LatticeProb.stopPath_apply]
  rw [interpPathCM_scale c v v' hv, mul_min_div_speed _ _ _ _]

/-! ### Stopped versus unstopped walk -/

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- The interpolated walk and the walk stopped at its exit time agree up to the exit time, hence
are at `dUnif`-distance at most `exp (-τ / m)`. -/
theorem dUnif_interp_stoppedInterp_le (v : ℤ → ℂ) (m : ℝ≥0) (A : Set ℤ) (X : ℕ → ℤ) :
    dUnif (interpPathCM v m.coe_nonneg X) (stoppedInterp v m A X) ≤
      Real.exp (-((((vExitTime A X).toNat : ℝ≥0) / m : ℝ≥0) : ℝ)) := by
  have h := dUnif_le_of_forall_dist_le (X := interpPathCM v m.coe_nonneg X)
    (Y := stoppedInterp v m A X) (((vExitTime A X).toNat : ℝ≥0) / m) (δ := 0) (fun t ht => by
      have hmin : min t (((vExitTime A X).toNat : ℝ≥0) / m) = t := min_eq_left ht
      have : stoppedInterp v m A X t = interpPathCM v m.coe_nonneg X t := by
        unfold stoppedInterp
        simp only [LatticeProb.stopPath_apply, hmin]
      rw [this, dist_self])
  simpa using h

theorem stoppedInterp_zero_speed (v : ℤ → ℂ) (A : Set ℤ) (X : ℕ → ℤ) :
    stoppedInterp v 0 A X = interpPathCM v (0 : ℝ≥0).coe_nonneg X := by
  ext t
  unfold stoppedInterp
  simp only [LatticeProb.stopPath_apply, interpPathCM_apply, interpPathFn, NNReal.coe_zero,
    zero_mul]

/-- **Stopped versus unstopped walk, Lévy–Prokhorov bound.**  If, outside an event of measure at most
`r`, the exit time from `A` is finite and at least `m * T0`, and `exp (-T0) < r`, then the laws of
the interpolated walk and of the interpolated walk stopped at its exit time from `A` are within `r`
in the Lévy–Prokhorov edistance for the local uniform metric. -/
theorem levyProkhorovEDist_walk_stop_le (P : Measure (ℕ → ℤ)) (v : ℤ → ℂ) (m : ℝ≥0) (A : Set ℤ)
    (T0 r : ℝ≥0) (hr : Real.exp (-(T0 : ℝ)) < r)
    (hbad : P {X | ¬ ∃ n : ℕ, vExitTime A X = n ∧ (m : ℝ) * T0 ≤ n} ≤ r) :
    levyProkhorovEDist (P.map (interpPathCM v m.coe_nonneg)) (P.map (stoppedInterp v m A)) ≤ r := by
  rcases eq_or_ne m 0 with h0 | h0
  · subst h0
    have : stoppedInterp v 0 A = interpPathCM v (0 : ℝ≥0).coe_nonneg := funext (stoppedInterp_zero_speed v A)
    rw [this, levyProkhorovEDist_self]
    exact zero_le
  · have hm : 0 < m := pos_iff_ne_zero.2 h0
    refine levyProkhorovEDist_map_le_of_bad P (measurable_interpPathCM v m.coe_nonneg)
      (measurable_stoppedInterp v m A) r (le_trans (measure_mono ?_) hbad)
    intro X hX
    by_contra hnot
    have hex : ∃ n : ℕ, vExitTime A X = n ∧ (m : ℝ) * T0 ≤ n := not_not.1 hnot
    obtain ⟨n, hn, hmn⟩ := hex
    have hT : (T0 : ℝ) ≤ (((vExitTime A X).toNat : ℝ≥0) / m : ℝ≥0) := by
      rw [hn, ENat.toNat_natCast]
      push_cast
      rw [le_div_iff₀ (by exact_mod_cast hm)]
      linarith
    have hd := dUnif_interp_stoppedInterp_le v m A X
    have hlt : dUnif (interpPathCM v m.coe_nonneg X) (stoppedInterp v m A X) < r :=
      lt_of_le_of_lt hd (lt_of_le_of_lt (Real.exp_le_exp.2 (neg_le_neg hT)) hr)
    have hedist : edist (interpPathCM v m.coe_nonneg X) (stoppedInterp v m A X) < (r : ℝ≥0∞) := by
      rw [edist_dist, dUnifMetricSpace_dist, ← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff ((Real.exp_pos _).trans hr)).2 hlt
    exact absurd hX (not_le.2 hedist)

end StoppedWalkScaling
end MatedCRT
