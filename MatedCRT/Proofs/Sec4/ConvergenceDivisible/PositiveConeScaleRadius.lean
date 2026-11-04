import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianMaximumIntegrable

/-! # Positivity of cone scale radii from radial asymptotics -/

namespace MatedCRT

open Filter Set MeasureTheory HarmonicBalls Topology

/-- A continuous radial function which tends to opposite infinities has a
bounded nonempty level set at every height, with positive supremum. -/
theorem positive_sSup_radial_level {f : ℝ → ℝ} (a : ℝ)
    (hf : ContinuousOn f (Ioi 0))
    (hzero : Tendsto f (𝓝[>] (0 : ℝ)) atBot)
    (hinf : Tendsto f atTop atTop) :
    0 < sSup {r : ℝ | 0 < r ∧ f r = a} := by
  obtain ⟨δ, hδ, hδbound⟩ := exists_pos_of_eventually_nhdsGT ((tendsto_atBot.1 hzero) (a - 1))
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_atTop.1 hinf) (a + 1))
  let x := δ / 2
  let y := max M δ
  have hx : 0 < x := by dsimp [x]; positivity
  have hxy : x ≤ y := by dsimp [x, y]; linarith [le_max_right M δ]
  have hfx : f x ≤ a := by
    have h := hδbound x hx (by dsimp [x]; linarith)
    linarith
  have hfy : a ≤ f y := by
    have h := hM y (le_max_left M δ)
    linarith
  have hc : ContinuousOn f (Icc x y) := hf.mono fun _ hr => lt_of_lt_of_le hx hr.1
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc hxy hc ⟨hfx, hfy⟩
  have hrpos : 0 < r := lt_of_lt_of_le hx hr.1
  have hbdd : BddAbove {r : ℝ | 0 < r ∧ f r = a} := by
    refine ⟨M, ?_⟩
    intro z hz
    by_contra hn
    have h := hM z (le_of_lt (lt_of_not_ge hn))
    linarith [hz.2]
  exact hrpos.trans_le (le_csSup hbdd ⟨hrpos, hfr⟩)

/-- Positive cone scale radii follow from the two radial limits. -/
theorem coneScaleRadius_pos_of_radial_limits {γ b : ℝ} {hcirc : ℝ → ℂ → ℝ}
    (hf : ContinuousOn (fun r : ℝ => hcirc r 0 + lqgQ γ * Real.log r) (Ioi 0))
    (hzero : Tendsto (fun r : ℝ => hcirc r 0 + lqgQ γ * Real.log r)
      (𝓝[>] (0 : ℝ)) atBot)
    (hinf : Tendsto (fun r : ℝ => hcirc r 0 + lqgQ γ * Real.log r) atTop atTop) :
    0 < coneScaleRadius γ hcirc b :=
  positive_sSup_radial_level (γ⁻¹ * Real.log b) hf hzero hinf

end MatedCRT
