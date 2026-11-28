import Mathlib

/-!
# A measurable regularization of real paths indexed by `ℝ≥0`

A path `p : ℝ≥0 → ℝ` is a point of the product space `ℝ≥0 → ℝ` with the product σ-algebra, for which the
pairing of a path with a test function is in general not measurable. The dyadic regularization `regPath p t` is the
limit of `p (⌊2ⁿ t⌋ / 2ⁿ)` as `n → ∞`; it is jointly measurable in `(p, t)` for the product σ-algebra on paths
(each approximant reads `p` at countably many times) and it equals `p t` whenever `p` is continuous at `t`.

Dyadic approximation of the time along `⌊2ⁿ t⌋ / 2ⁿ` is the standard device for measurable versions of
processes with continuous paths.
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace MatedCRT

/-- The dyadic floor `⌊2ⁿ t⌋ / 2ⁿ` of a time `t`. -/
noncomputable def dyadicFloor (n : ℕ) (t : ℝ≥0) : ℝ≥0 := ((⌊(t : ℝ) * 2 ^ n⌋₊ : ℕ) : ℝ≥0) / 2 ^ n

theorem coe_dyadicFloor (n : ℕ) (t : ℝ≥0) :
    (dyadicFloor n t : ℝ) = (⌊(t : ℝ) * 2 ^ n⌋₊ : ℝ) / 2 ^ n := by
  simp [dyadicFloor]

theorem dyadicFloor_le (n : ℕ) (t : ℝ≥0) : (dyadicFloor n t : ℝ) ≤ t := by
  rw [coe_dyadicFloor, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem sub_le_dyadicFloor (n : ℕ) (t : ℝ≥0) : (t : ℝ) - (1 / 2) ^ n ≤ dyadicFloor n t := by
  rw [coe_dyadicFloor, le_div_iff₀ (by positivity)]
  have h := Nat.lt_floor_add_one ((t : ℝ) * 2 ^ n)
  have e : ((t : ℝ) - (1 / 2) ^ n) * 2 ^ n = (t : ℝ) * 2 ^ n - 1 := by
    rw [sub_mul, one_div, inv_pow, inv_mul_cancel₀ (by positivity)]
  rw [e]
  linarith

theorem tendsto_dyadicFloor (t : ℝ≥0) : Tendsto (fun n => dyadicFloor n t) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have h0 : Tendsto (fun n : ℕ => (t : ℝ) - (1 / 2) ^ n) atTop (𝓝 ((t : ℝ) - 0)) :=
    tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  rw [sub_zero] at h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds
    (fun n => sub_le_dyadicFloor n t) (fun n => dyadicFloor_le n t)

open Classical in
/-- The dyadic regularization of a path: the limit of `p (⌊2ⁿ t⌋ / 2ⁿ)` (junk `0` if it does not exist). -/
noncomputable def regPath (p : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := limUnder atTop fun n : ℕ => p (dyadicFloor n t)

theorem regPath_eq_of_continuousAt {p : ℝ≥0 → ℝ} {t : ℝ≥0} (hp : ContinuousAt p t) : regPath p t = p t :=
  ((hp.tendsto.comp (tendsto_dyadicFloor t))).limUnder_eq

theorem regPath_eq_of_continuous {p : ℝ≥0 → ℝ} (hp : Continuous p) : regPath p = p :=
  funext fun _ => regPath_eq_of_continuousAt hp.continuousAt

theorem measurable_dyadicFloor_eval (n : ℕ) :
    Measurable fun q : (ℝ≥0 → ℝ) × ℝ≥0 => q.1 (dyadicFloor n q.2) := by
  have h1 : Measurable fun r : (ℝ≥0 → ℝ) × ℕ => r.1 ((r.2 : ℝ≥0) / 2 ^ n) :=
    measurable_from_prod_countable_left fun m => measurable_pi_apply ((m : ℝ≥0) / 2 ^ n)
  have h2 : Measurable fun q : (ℝ≥0 → ℝ) × ℝ≥0 => (q.1, ⌊(q.2 : ℝ) * 2 ^ n⌋₊) :=
    measurable_fst.prodMk
      (Nat.measurable_floor.comp ((NNReal.continuous_coe.measurable.comp measurable_snd).mul_const _))
  exact h1.comp h2

/-- **The dyadic regularization is jointly measurable** in the path (product σ-algebra) and the time. -/
theorem measurable_regPath : Measurable fun q : (ℝ≥0 → ℝ) × ℝ≥0 => regPath q.1 q.2 := by
  refine StronglyMeasurable.measurable ?_
  exact StronglyMeasurable.limUnder fun n => (measurable_dyadicFloor_eval n).stronglyMeasurable

end MatedCRT
