import HarmonicBalls.Proofs.Sec6.BrownianUnitIncrements
import MatedCRT.Proofs.Sec3.KilledOccupation.RemovedTail

/-!
# Geometric tail of the exit time of planar Brownian motion from a disc

Before its exit time `σ = exitNN z r b` from the disc `ball z r`, a planar Brownian path `b` stays in the disc, so
every unit increment `b (k + 1) - b k` with `k + 1 < σ` has modulus less than `2 r`. The real parts of the unit
increments are independent standard Gaussians, hence for every start point `y` and every `m : ℕ`,
`P_y(m < σ) ≤ q^m` with `q = P(|N(0,1)| < 2 r) < 1`.
-/

open MeasureTheory Set Metric MarkovProcess ProbabilityTheory HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The probability `P(-2r < N(0,1) < 2r)` that a standard Gaussian increment stays below `2 r` in modulus. -/
noncomputable def unitIncrementStayProb (r : ℝ) : ℝ≥0∞ :=
  gaussianReal 0 1 (Ioo (-(2 * r)) (2 * r))

theorem unitIncrementStayProb_lt_one (r : ℝ) : unitIncrementStayProb r < 1 := by
  have hpos : gaussianReal 0 1 (Ici (2 * r)) ≠ 0 := by
    intro hz
    have hv := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)) hz
    simp at hv
  have hsub : Ioo (-(2 * r)) (2 * r) ⊆ (Ici (2 * r))ᶜ := fun x hx => by
    simp only [mem_compl_iff, mem_Ici, not_le]
    exact hx.2
  calc unitIncrementStayProb r ≤ gaussianReal 0 1 (Ici (2 * r))ᶜ := measure_mono hsub
    _ = 1 - gaussianReal 0 1 (Ici (2 * r)) := prob_compl_eq_one_sub measurableSet_Ici
    _ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos

/-- Before the exit time from `ball z r`, a path is in `ball z r`. -/
theorem mem_ball_of_lt_exitNN {z : ℂ} {r : ℝ} {b : ContinuousPath ℂ} {s : ℝ≥0}
    (hs : s < exitNN z r b) : b s ∈ ball z r := by
  by_contra h
  have hle : HarmonicBalls.pathExitTime (ball z r) ⇑b ≤ (s : ℝ≥0∞) := sInf_le ⟨s, rfl, h⟩
  have hle' := ENNReal.toNNReal_mono ENNReal.coe_ne_top hle
  rw [ENNReal.toNNReal_coe] at hle'
  exact absurd hs (not_lt.mpr hle')

/-- **Geometric tail of the exit time.** For planar Brownian motion started at any `y`,
`P_y(m < σ) ≤ q^m`, where `σ = exitNN z r` is the exit time of `ball z r` and `q = P(|N(0,1)| < 2r)`. -/
theorem planarBrownianMotion_lt_exitNN_le_pow (z y : ℂ) (r : ℝ) (m : ℕ) :
    planarBrownianMotion y {b | ((m : ℝ≥0)) < exitNN z r b} ≤ unitIncrementStayProb r ^ m := by
  have hmk : ∀ k : ℕ, Measurable (fun p : ContinuousPath ℝ => p ((k : ℝ≥0) + 1) - p k) := fun _ =>
    (ContinuousPath.measurable_coordinateProcess _).sub (ContinuousPath.measurable_coordinateProcess _)
  have hm : Measurable (fun b : ContinuousPath ℂ => (reImPath b).1) :=
    measurable_fst.comp measurable_reImPath
  have hAm : MeasurableSet (⋂ k ∈ Finset.range m,
      (fun p : ContinuousPath ℝ => p ((k : ℝ≥0) + 1) - p k) ⁻¹' Ioo (-(2 * r)) (2 * r)) :=
    Finset.measurableSet_biInter _ fun k _ => hmk k measurableSet_Ioo
  have hsub : {b : ContinuousPath ℂ | ((m : ℝ≥0)) < exitNN z r b} ⊆
      (fun b : ContinuousPath ℂ => (reImPath b).1) ⁻¹' (⋂ k ∈ Finset.range m,
        (fun p : ContinuousPath ℝ => p ((k : ℝ≥0) + 1) - p k) ⁻¹' Ioo (-(2 * r)) (2 * r)) := by
    intro b hb
    have hb' : (m : ℝ≥0) < exitNN z r b := hb
    simp only [mem_preimage, mem_iInter, Finset.mem_range, reImPath_fst_apply]
    intro k hk
    have h1 : (k : ℝ≥0) < exitNN z r b :=
      lt_of_le_of_lt (by exact_mod_cast hk.le) hb'
    have h2 : (k : ℝ≥0) + 1 < exitNN z r b :=
      lt_of_le_of_lt (by exact_mod_cast Nat.succ_le_of_lt hk) hb'
    have hb1 := mem_ball_of_lt_exitNN h1
    have hb2 := mem_ball_of_lt_exitNN h2
    rw [mem_ball, dist_eq_norm] at hb1 hb2
    have htri : ‖b ((k : ℝ≥0) + 1) - b k‖ ≤ ‖b ((k : ℝ≥0) + 1) - z‖ + ‖b k - z‖ := by
      calc ‖b ((k : ℝ≥0) + 1) - b k‖ = ‖(b ((k : ℝ≥0) + 1) - z) - (b k - z)‖ := by
            congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have hre : |(b ((k : ℝ≥0) + 1)).re - (b k).re| < 2 * r := by
      rw [← Complex.sub_re]
      linarith [Complex.abs_re_le_norm (b ((k : ℝ≥0) + 1) - b k)]
    exact abs_lt.mp hre
  calc planarBrownianMotion y {b | ((m : ℝ≥0)) < exitNN z r b}
      ≤ planarBrownianMotion y ((fun b : ContinuousPath ℂ => (reImPath b).1) ⁻¹' (⋂ k ∈ Finset.range m,
        (fun p : ContinuousPath ℝ => p ((k : ℝ≥0) + 1) - p k) ⁻¹' Ioo (-(2 * r)) (2 * r))) :=
        measure_mono hsub
    _ = brownianMotion y.re (⋂ k ∈ Finset.range m,
        (fun p : ContinuousPath ℝ => p ((k : ℝ≥0) + 1) - p k) ⁻¹' Ioo (-(2 * r)) (2 * r)) := by
        rw [← Measure.map_apply hm hAm, planarBrownianMotion_map_re]
    _ = ∏ k ∈ Finset.range m, brownianMotion y.re
        ((fun p : ContinuousPath ℝ => p ((k : ℝ≥0) + 1) - p k) ⁻¹' Ioo (-(2 * r)) (2 * r)) :=
        (iIndepFun_realBrownian_unit_increments y.re).measure_inter_preimage_eq_mul _
          (sets := fun _ => Ioo (-(2 * r)) (2 * r)) fun _ _ => measurableSet_Ioo
    _ = ∏ _k ∈ Finset.range m, unitIncrementStayProb r := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← Measure.map_apply (hmk k) measurableSet_Ioo,
          (realBrownian_unit_increment_hasLaw y.re k).map_eq]
        rfl
    _ = unitIncrementStayProb r ^ m := by rw [Finset.prod_const, Finset.card_range]

/-- The geometric tail at a real time: `P_y(t < σ) ≤ q^⌊t⌋`. -/
theorem planarBrownianMotion_lt_exitNN_le_pow_floor (z y : ℂ) (r : ℝ) (t : ℝ≥0) :
    planarBrownianMotion y {b | t < exitNN z r b} ≤ unitIncrementStayProb r ^ ⌊t⌋₊ := by
  have hfl : ((⌊t⌋₊ : ℕ) : ℝ≥0) ≤ t := Nat.floor_le t.2
  refine le_trans (measure_mono ?_) (planarBrownianMotion_lt_exitNN_le_pow z y r ⌊t⌋₊)
  intro b hb
  have hb' : t < exitNN z r b := hb
  exact lt_of_le_of_lt hfl hb'

end MatedCRT.KilledOccupation
