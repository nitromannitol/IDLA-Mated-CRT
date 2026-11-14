import MatedCRT.FirstPass.Derived.BrownianExitTimeTail
import MatedCRT.FirstPass.Derived.BrownianIncrementSmallBall

/-!
# Two-time small-ball bound for planar Brownian motion killed on exiting a disc

For a planar Brownian motion `b` started at `y`, the exit time `exitNN z r b` of the disc `B(z, r)`, two
distinct times `u ≠ v`, `a ≥ 0` and `θ ∈ [0, 1]`:

`P_y(u ≤ τ, v ≤ τ, ‖b u - b v‖ < a) ≤ (q ^ (⌊max u v⌋₊ - 1)) ^ θ · (a ² / |u - v|) ^ (1 - θ)`,

where `q = unitIncrementStayProb r < 1`. The first factor is the exponential tail of the exit time
(`planarBrownianMotion_lt_exitNN_le_pow`), the second is the small-ball bound of a Gaussian increment
(`planarBrownianMotion_norm_increment_lt_le`); they are combined by `min (α, β) ≤ α ^ θ β ^ (1 - θ)`.

* `planarBrownianMotion_le_exitNN_le_pow_floor_sub_one`: `P_y(t ≤ τ) ≤ q ^ (⌊t⌋₊ - 1)`.
* `planarBrownianMotion_twoTime_norm_sub_lt_le`: the two-time bound.
-/

open MeasureTheory Set Metric MarkovProcess ProbabilityTheory HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- Being still inside the disc at time `t` has probability at most `q ^ (⌊t⌋₊ - 1)`, with
`q = unitIncrementStayProb r`. -/
theorem planarBrownianMotion_le_exitNN_le_pow_floor_sub_one (z y : ℂ) (r : ℝ) (t : ℝ≥0) :
    planarBrownianMotion y {b | t ≤ exitNN z r b} ≤ unitIncrementStayProb r ^ (⌊t⌋₊ - 1) := by
  rcases Nat.eq_zero_or_pos ⌊t⌋₊ with h0 | hpos
  · rw [h0, Nat.zero_sub, pow_zero]
    exact prob_le_one
  · obtain ⟨n, hn⟩ : ∃ n, ⌊t⌋₊ = n + 1 := ⟨⌊t⌋₊ - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ≥0) ≤ t := Nat.floor_le t.2
    rw [hn] at hfl
    refine le_trans (measure_mono fun b hb => ?_) (planarBrownianMotion_lt_exitNN_le_pow z y r n)
    have hb' : t ≤ exitNN z r b := hb
    show ((n : ℝ≥0)) < exitNN z r b
    have hlt : (n : ℝ≥0) < ((n + 1 : ℕ) : ℝ≥0) := by exact_mod_cast Nat.lt_succ_self n
    exact lt_of_lt_of_le hlt (hfl.trans hb')

/-- **Two-time small-ball bound for killed planar Brownian motion.** For distinct times `u ≠ v`, `a ≥ 0`
and `θ ∈ [0, 1]`, the probability that the Brownian motion started at `y` is still inside `B(z, r)` at both
times and that `‖b u - b v‖ < a` is at most `(q ^ (⌊max u v⌋₊ - 1)) ^ θ · (a ² / |u - v|) ^ (1 - θ)`,
with `q = unitIncrementStayProb r`. -/
theorem planarBrownianMotion_twoTime_norm_sub_lt_le (z y : ℂ) (r : ℝ) {u v : ℝ≥0} (huv : u ≠ v)
    {a : ℝ} (ha : 0 ≤ a) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    planarBrownianMotion y {b | u ≤ exitNN z r b ∧ v ≤ exitNN z r b ∧ ‖b u - b v‖ < a} ≤
      (unitIncrementStayProb r ^ (⌊max u v⌋₊ - 1)) ^ θ *
        ENNReal.ofReal (a ^ 2 / |(u : ℝ) - v|) ^ (1 - θ) := by
  obtain ⟨E, hE⟩ : ∃ E : Set (ContinuousPath ℂ),
      E = {b | u ≤ exitNN z r b ∧ v ≤ exitNN z r b ∧ ‖b u - b v‖ < a} := ⟨_, rfl⟩
  rw [← hE]
  have hA : planarBrownianMotion y E ≤ unitIncrementStayProb r ^ (⌊max u v⌋₊ - 1) := by
    refine le_trans (measure_mono fun b hb => ?_)
      (planarBrownianMotion_le_exitNN_le_pow_floor_sub_one z y r (max u v))
    rw [hE] at hb
    exact max_le hb.1 hb.2.1
  have hB : planarBrownianMotion y E ≤ ENNReal.ofReal (a ^ 2 / |(u : ℝ) - v|) := by
    refine le_trans (measure_mono fun b hb => ?_)
      (planarBrownianMotion_norm_increment_lt_le y huv.symm ha)
    rw [hE] at hb
    exact hb.2.2
  calc planarBrownianMotion y E
      = planarBrownianMotion y E ^ θ * planarBrownianMotion y E ^ (1 - θ) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hθ0 (by linarith), add_sub_cancel, ENNReal.rpow_one]
    _ ≤ _ := mul_le_mul' (ENNReal.rpow_le_rpow hA hθ0) (ENNReal.rpow_le_rpow hB (by linarith))

end MatedCRT.KilledOccupation
