import MatedCRT.Proofs.Sec4.ConvergenceDivisible.TimeChange

/-! Continuity of paths under a continuous increasing LQG clock. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- A time-change clock attains every nonnegative value. -/
theorem IsTimeChangeClock.surjective_toNNReal {f : ℝ≥0 → ℝ}
    (hf : IsTimeChangeClock f) : Function.Surjective (fun s => Real.toNNReal (f s)) := by
  intro t
  obtain ⟨s, hs⟩ := (hf.tendsto_atTop.eventually (eventually_ge_atTop (t : ℝ))).exists
  have ht : (t : ℝ) ∈ Icc (f 0) (f s) := by
    constructor
    · simpa only [hf.map_zero] using t.coe_nonneg
    · exact hs
  obtain ⟨u, _, hu⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ s from bot_le)
    hf.continuous.continuousOn ht
  refine ⟨u, ?_⟩
  change Real.toNNReal (f u) = t
  rw [hu]
  simp only [Real.toNNReal_coe]

/-- The right-continuous clock inverse is strictly increasing for an LQG
 time-change clock. -/
theorem IsTimeChangeClock.strictMono_clockInverse {f : ℝ≥0 → ℝ}
    (hf : IsTimeChangeClock f) : StrictMono (clockInverse f) := by
  intro t u htu
  obtain ⟨s, rfl⟩ := IsTimeChangeClock.surjective_toNNReal hf t
  obtain ⟨r, rfl⟩ := IsTimeChangeClock.surjective_toNNReal hf u
  rw [clockInverse_clockValue hf.map_zero hf.strictMono,
    clockInverse_clockValue hf.map_zero hf.strictMono]
  apply hf.strictMono.lt_iff_lt.mp
  have hs : 0 ≤ f s := by simpa [hf.map_zero] using hf.strictMono.monotone (show 0 ≤ s from bot_le)
  have hr : 0 ≤ f r := by simpa [hf.map_zero] using hf.strictMono.monotone (show 0 ≤ r from bot_le)
  have htu' : (Real.toNNReal (f s) : ℝ) < (Real.toNNReal (f r) : ℝ) := by exact_mod_cast htu
  simpa only [Real.coe_toNNReal _ hs, Real.coe_toNNReal _ hr] using htu'

/-- The inverse of a time-change clock is continuous. -/
theorem IsTimeChangeClock.continuous_clockInverse {f : ℝ≥0 → ℝ}
    (hf : IsTimeChangeClock f) : Continuous (clockInverse f) := by
  apply (IsTimeChangeClock.strictMono_clockInverse hf).monotone.continuous_of_surjective
  intro s
  exact ⟨Real.toNNReal (f s), clockInverse_clockValue hf.map_zero hf.strictMono s⟩

/-- A Brownian path run with a valid clock is continuous. -/
theorem continuous_liouvilleBrownianPath {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} (hF : IsTimeChangeClock (F b)) :
    Continuous (liouvilleBrownianPath F b) :=
  b.continuous.comp (IsTimeChangeClock.continuous_clockInverse hF)

/-- The deterministic linear time rescaling preserves continuity. -/
theorem continuous_rescaledLBMPath {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} {m : ℝ} (hF : IsTimeChangeClock (F b)) :
    Continuous (rescaledLBMPath F m b) :=
  (continuous_liouvilleBrownianPath hF).comp (continuous_const.mul continuous_id)

end MatedCRT
