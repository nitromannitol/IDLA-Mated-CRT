import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenTruncationProbability

/-! Elementary boundary properties of the continuum exit potential. -/

namespace MatedCRT

open Set Metric MeasureTheory _root_.HarmonicBalls

/-- The normalization constant is nonnegative, including in the degenerate
case where the median is zero. -/
theorem MatedCRTEnv.c₀_nonneg {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) :
    0 ≤ S.c₀ := by
  unfold MatedCRTEnv.c₀ MatedCRTEnv.m₀
  exact div_nonneg (by norm_num) (medianOf_nonneg _)

/-- The continuum exit potential is nonnegative. -/
theorem normalizedExitGreenPotential_nonneg {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ω : Ω) (x : ℂ) :
    0 ≤ normalizedExitGreenPotential S r z ω x := by
  apply mul_nonneg (div_nonneg S.c₀_nonneg (by norm_num))
  apply integral_nonneg
  intro y
  exact greenFunction_nonneg isBounded_ball x y

/-- The continuum exit potential vanishes outside its domain, in particular
on its boundary. -/
theorem normalizedExitGreenPotential_eq_zero_of_not_mem
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {r : ℝ} {z x : ℂ}
    (hx : x ∉ ball z r) (ω : Ω) : normalizedExitGreenPotential S r z ω x = 0 := by
  simp [normalizedExitGreenPotential, greenFunction_of_notMem_left hx]

theorem normalizedExitGreenPotential_eq_zero_on_sphere
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {r : ℝ} {z x : ℂ}
    (hx : x ∈ sphere z r) (ω : Ω) : normalizedExitGreenPotential S r z ω x = 0 := by
  apply normalizedExitGreenPotential_eq_zero_of_not_mem S _ ω
  rw [mem_sphere] at hx
  rw [mem_ball]
  linarith

end MatedCRT
