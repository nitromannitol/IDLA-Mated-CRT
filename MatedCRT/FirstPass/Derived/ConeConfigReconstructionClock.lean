import LatticeProb.LQG.MassReparamBorel

/-!
# The inverse mass clock along a curve on one time block

`LatticeProb.LQG.massClockInv_eq_of_massParam` identifies the inverse mass clock of a curve `L` with the clock `v` when
`L ∘ v` is parametrized by the mass of `μ` at all times. For the reconstruction of the local configurations of a
quantum cone from the area measure on an annulus (`ConeConfigReconstruction`), the mass clock is known only on one
time block of the curve. This file proves the identity on the block:

* `massClockInv_eq_of_posBlock`: if the mass clock is `v⁻¹` on `[0, v T]`, at least `T` after `v T` and nonpositive
  before `0`, then `massClockInv μ L = v` on `[0, T)`;
* `massClockInv_eq_of_negBlock`: if the mass clock is `v⁻¹` on `[v (-T), 0]`, at most `-T` before `v (-T)` and positive
  after `0`, then `massClockInv μ L = v` on `(-T, 0]`.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace MatedCRT

open LatticeProb.LQG (massClock massClockInv iInf_rat_ite_lt_eq)

variable {E : Type*} [MeasurableSpace E]

/-- The inverse mass clock is `v t` as soon as the mass clock crosses `t` exactly at the rationals above `v t`. -/
theorem massClockInv_eq_of_forall_rat_iff {μ : Measure E} {L : ℝ → E} {t s : ℝ}
    (hiff : ∀ q : ℚ, t < massClock μ L q ↔ s < (q : ℝ)) : massClockInv μ L t = s := by
  unfold massClockInv
  simp_rw [hiff]
  rw [iInf_rat_ite_lt_eq, EReal.toReal_coe]

/-- **The inverse mass clock on a positive block.** -/
theorem massClockInv_eq_of_posBlock {μ : Measure E} {L : ℝ → E} {v : ℝ ≃o ℝ} (hv0 : v 0 = 0) {T : ℝ}
    (hin : ∀ q, 0 ≤ q → q ≤ v T → massClock μ L q = v.symm q)
    (hafter : ∀ q, v T < q → T ≤ massClock μ L q) (hbefore : ∀ q, q < 0 → massClock μ L q ≤ 0)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) : massClockInv μ L t = v t := by
  have hvt0 : 0 ≤ v t := by rw [← hv0]; exact v.monotone ht0
  have hvtT : v t < v T := v.lt_iff_lt.2 htT
  refine massClockInv_eq_of_forall_rat_iff fun q => ?_
  rcases lt_or_ge (q : ℝ) 0 with hq0 | hq0
  · have h1 := hbefore q hq0
    constructor
    · intro h; linarith
    · intro h; linarith
  rcases le_or_gt (q : ℝ) (v T) with hqT | hqT
  · rw [hin q hq0 hqT, ← v.lt_iff_lt, v.apply_symm_apply]
  · have h1 := hafter q hqT
    constructor
    · intro _; linarith
    · intro _; linarith

/-- **The inverse mass clock on a negative block.** -/
theorem massClockInv_eq_of_negBlock {μ : Measure E} {L : ℝ → E} {v : ℝ ≃o ℝ} (hv0 : v 0 = 0) {T : ℝ}
    (hin : ∀ q, v (-T) ≤ q → q ≤ 0 → massClock μ L q = v.symm q)
    (hbefore : ∀ q, q < v (-T) → massClock μ L q ≤ -T) (hafter : ∀ q, 0 < q → 0 < massClock μ L q)
    {t : ℝ} (htT : -T < t) (ht0 : t ≤ 0) : massClockInv μ L t = v t := by
  have hvt0 : v t ≤ 0 := by rw [← hv0]; exact v.monotone ht0
  have hvtT : v (-T) < v t := v.lt_iff_lt.2 htT
  refine massClockInv_eq_of_forall_rat_iff fun q => ?_
  rcases lt_or_ge 0 (q : ℝ) with hq0 | hq0
  · have h1 := hafter q hq0
    constructor
    · intro _; linarith
    · intro _; linarith
  rcases le_or_gt (v (-T)) (q : ℝ) with hqT | hqT
  · rw [hin q hqT hq0, ← v.lt_iff_lt, v.apply_symm_apply]
  · have h1 := hbefore q hqT
    constructor
    · intro h; linarith
    · intro h; linarith

end MatedCRT
