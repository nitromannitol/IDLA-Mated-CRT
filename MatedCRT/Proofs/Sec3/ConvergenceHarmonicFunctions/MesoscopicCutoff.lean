import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! # Mesoscopic cutoff for boundary excursions -/

namespace MatedCRT

open Filter Set
open scoped Topology

/-- The boundary-excursion cutoff in `LEMMA36-REPLACEMENT.md`, equation
`exponents`: the first annulus radius is at least the permitted annulus
scale, is strictly more than one hundred cell diameters, and is comparable
to `ε` raised to the smaller exponent. -/
theorem mesoscopic_cutoff_bounds {ε a b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let d := ε ^ a
    let ℓ := 100 * d + ε ^ b
    ε ^ b ≤ ℓ ∧ d < ℓ / 100 ∧
      ε ^ min a b ≤ ℓ ∧ ℓ ≤ 101 * ε ^ min a b := by
  dsimp only
  have ha : 0 < ε ^ a := Real.rpow_pos_of_pos hε _
  have hb : 0 < ε ^ b := Real.rpow_pos_of_pos hε _
  have hamin : ε ^ a ≤ ε ^ min a b :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_left _ _)
  have hbmin : ε ^ b ≤ ε ^ min a b :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_right _ _)
  refine ⟨by linarith, by linarith, ?_, by linarith⟩
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    linarith
  · rw [min_eq_right hba]
    linarith

/-- A quantitative comparison between the boundary-excursion cutoff and a
smaller power of the mesh size. -/
theorem mesoscopic_cutoff_le_smaller_power {ε a b p : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : ε ^ (min a b - p) ≤ 1 / 808) :
    4 * (100 * ε ^ a + ε ^ b) ≤ ε ^ p / 2 := by
  have hbound := (mesoscopic_cutoff_bounds (a := a) (b := b) hε hε1).2.2.2
  have hp : 0 < ε ^ p := Real.rpow_pos_of_pos hε _
  have hmul := mul_le_mul_of_nonneg_right hsmall (le_of_lt hp)
  have heq : ε ^ (min a b - p) * ε ^ p = ε ^ min a b := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  rw [heq] at hmul
  linarith

/-- If the power is smaller than both cutoff exponents, the comparison holds
for all sufficiently small positive mesh sizes. -/
theorem mesoscopic_cutoff_eventually_le_smaller_power {a b p : ℝ}
    (hp : p < min a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      4 * (100 * ε ^ a + ε ^ b) ≤ ε ^ p / 2 := by
  have hd : 0 < min a b - p := sub_pos.mpr hp
  have hf : Filter.Tendsto (fun x : ℝ => x ^ (min a b - p)) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow (ne_of_gt hd)] using
      (Real.continuousAt_rpow_const 0 (min a b - p) (Or.inr (le_of_lt hd))).tendsto
  have hv : {x : ℝ | x ^ (min a b - p) < 1 / 808} ∈ 𝓝 (0 : ℝ) :=
    hf (Iio_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro ε hε hεδ
  have hsmall : ε ^ (min a b - p) ≤ 1 / 808 := le_of_lt (hδsub (by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hε] using
      (lt_of_lt_of_le hεδ (min_le_left δ 1))))
  exact mesoscopic_cutoff_le_smaller_power hε
    (le_of_lt (lt_of_lt_of_le hεδ (min_le_right δ 1))) hsmall

end MatedCRT
