import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenTruncationProbability

/-! Elementary boundary properties of the continuum exit potential. -/

namespace MatedCRT

open Set Metric MeasureTheory Topology _root_.HarmonicBalls

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

/-- A continuous function on a closed ball which vanishes on the boundary is
uniformly small in a sufficiently thin boundary layer. -/
theorem exists_boundary_layer_of_continuousOn {z : ℂ} {r : ℝ} (hr : 0 < r)
    {f : ℂ → ℝ} (hf : ContinuousOn f (closedBall z r))
    (hzero : ∀ x ∈ sphere z r, f x = 0) {t : ℝ} (ht : 0 < t) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧ ∀ x ∈ closedBall z r \ closedBall z r', |f x| < t := by
  let K := closedBall z r
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall z r)
  have hc : Continuous (fun x : K => f x) := continuousOn_iff_continuous_domRestrict.mp hf
  let B : Set K := {x | t ≤ |f x|}
  have hBc : IsClosed B := isClosed_le continuous_const hc.abs
  have hcompact : IsCompact B := hBc.isCompact
  by_cases hB : B.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn hB
      ((continuous_const : Continuous (fun _ : K => z)).dist continuous_subtype_val).continuousOn
    have hxr : dist z x < r := by
      have hxle : dist z x ≤ r := by
        have hx := mem_closedBall.mp x.property
        rwa [dist_comm] at hx
      by_contra hn
      have hxeq : dist z x = r := le_antisymm hxle (le_of_not_gt hn)
      have hxsphere : (x : ℂ) ∈ sphere z r := by
        rw [mem_sphere, dist_comm]
        exact hxeq
      have hx0 := hzero x hxsphere
      change t ≤ |f x| at hx
      rw [hx0, abs_zero] at hx
      linarith
    let r' := max (r / 2) ((dist z x + r) / 2)
    have hr'0 : 0 < r' := (by linarith : 0 < r / 2).trans_le (le_max_left _ _)
    have hr'r : r' < r := max_lt (by linarith) (by linarith)
    refine ⟨r', hr'0, hr'r, ?_⟩
    intro y hy
    by_contra hn
    have hyB : (⟨y, hy.1⟩ : K) ∈ B := le_of_not_gt hn
    have hdist := hmax hyB
    change dist z y ≤ dist z x at hdist
    have hyr : r' < dist y z := lt_of_not_ge hy.2
    have hxle := le_max_right (r / 2) ((dist z x + r) / 2)
    rw [dist_comm y z] at hyr
    linarith
  · refine ⟨r / 2, by linarith, by linarith, ?_⟩
    intro y hy
    by_contra hn
    exact hB ⟨⟨y, hy.1⟩, le_of_not_gt hn⟩

end MatedCRT
