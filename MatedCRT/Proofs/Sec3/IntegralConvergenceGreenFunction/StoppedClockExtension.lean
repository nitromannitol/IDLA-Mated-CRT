import MatedCRT.Proofs.LBM.TimeChangeContinuity

/-! # Extending a stopped clock -/

namespace MatedCRT

open Filter HarmonicBalls Set
open scoped NNReal

/-- A clock stopped at `T`, continued with unit speed after `T`. -/
noncomputable def stoppedClockExtension (F : ℝ≥0 → ℝ) (T : ℝ≥0) (t : ℝ≥0) : ℝ :=
  F (min t T) + max ((t : ℝ) - T) 0

/-- The extension agrees with the original clock up to the stopping time. -/
theorem stoppedClockExtension_eq {F : ℝ≥0 → ℝ} {T t : ℝ≥0} (ht : t ≤ T) :
    stoppedClockExtension F T t = F t := by
  have ht' : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  simp [stoppedClockExtension, min_eq_left ht, max_eq_right (sub_nonpos.mpr ht')]

/-- A continuous strictly increasing clock becomes an infinite-lifetime clock
when continued with unit speed after a finite stopping time. -/
theorem stoppedClockExtension_isTimeChangeClock {F : ℝ≥0 → ℝ} (T : ℝ≥0)
    (hzero : F 0 = 0) (hcont : Continuous F) (hmono : StrictMono F) :
    IsTimeChangeClock (stoppedClockExtension F T) := by
  have hnonneg : ∀ t, 0 ≤ F t := by
    intro t
    simpa [hzero] using hmono.monotone (show 0 ≤ t from bot_le)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [stoppedClockExtension, hzero]
  · unfold stoppedClockExtension
    fun_prop
  · intro s t hst
    have hle : F (min s T) ≤ F (min t T) := hmono.monotone (min_le_min_right T hst.le)
    have hst' : (s : ℝ) < t := by exact_mod_cast hst
    by_cases ht : t ≤ T
    · have hs : s ≤ T := hst.le.trans ht
      simp only [stoppedClockExtension, min_eq_left hs, min_eq_left ht,
        max_eq_right (sub_nonpos.mpr (show (s : ℝ) ≤ T by exact_mod_cast hs)),
        max_eq_right (sub_nonpos.mpr (show (t : ℝ) ≤ T by exact_mod_cast ht)), add_zero]
      exact hmono hst
    · have ht' : (T : ℝ) < t := by exact_mod_cast (lt_of_not_ge ht)
      by_cases hs : s ≤ T
      · have hlt : F s ≤ F T := hmono.monotone hs
        simp only [stoppedClockExtension, min_eq_left hs, min_eq_right (le_of_lt (lt_of_not_ge ht)),
          max_eq_right (sub_nonpos.mpr (show (s : ℝ) ≤ T by exact_mod_cast hs)),
          max_eq_left (sub_nonneg.mpr ht'.le)]
        linarith
      · have hs' : (T : ℝ) < s := by exact_mod_cast (lt_of_not_ge hs)
        simp only [stoppedClockExtension, min_eq_right (le_of_lt (lt_of_not_ge hs)),
          min_eq_right (le_of_lt (lt_of_not_ge ht)),
          max_eq_left (sub_nonneg.mpr hs'.le), max_eq_left (sub_nonneg.mpr ht'.le)]
        linarith
  · apply tendsto_atTop.2
    intro y
    filter_upwards [eventually_ge_atTop (Real.toNNReal (max 0 (y + (T : ℝ) + 1)))] with t ht
    have ht' : max 0 (y + (T : ℝ) + 1) ≤ (t : ℝ) := by
      have := NNReal.coe_le_coe.mpr ht
      simpa [Real.coe_toNNReal _ (le_max_left _ _)] using this
    have hh := hnonneg (min t T)
    have hm : (t : ℝ) - T ≤ max ((t : ℝ) - T) 0 := le_max_left _ _
    dsimp [stoppedClockExtension]
    have := le_max_right (0 : ℝ) (y + (T : ℝ) + 1)
    linarith

/-- Before the terminal clock time, the inverse does not change when the
clock is continued with unit speed. This remains true when the original
clock has finite lifetime. -/
theorem stoppedClockExtension_inverse_eq {F : ℝ≥0 → ℝ} {T u : ℝ≥0}
    (hzero : F 0 = 0) (hcont : Continuous F) (hmono : StrictMono F)
    (hu : (u : ℝ) ≤ F T) :
    clockInverse (stoppedClockExtension F T) u = clockInverse F u := by
  have hu' : (u : ℝ) ∈ Icc (F 0) (F T) := ⟨by simp [hzero], hu⟩
  obtain ⟨s, hs, hFs⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ T from bot_le)
    hcont.continuousOn hu'
  have hclock := stoppedClockExtension_isTimeChangeClock T hzero hcont hmono
  have hFs' : stoppedClockExtension F T s = (u : ℝ) := by
    rw [stoppedClockExtension_eq hs.2, hFs]
  have heq : Real.toNNReal (F s) = u := by rw [hFs, Real.toNNReal_coe]
  calc
    clockInverse (stoppedClockExtension F T) u =
        clockInverse (stoppedClockExtension F T)
          (Real.toNNReal (stoppedClockExtension F T s)) := by rw [hFs', Real.toNNReal_coe]
    _ = s := clockInverse_clockValue hclock.map_zero hclock.strictMono s
    _ = clockInverse F u := by rw [← heq, clockInverse_clockValue hzero hmono]

end MatedCRT
