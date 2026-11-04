import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthFromConeScaling

/-! # Exhaustion by radial level sets -/

namespace MatedCRT

open Filter Set MeasureTheory

/-- If a radial function is bounded above on every bounded interval away from
negative radii, the suprema of its positive level sets escape to infinity as
the levels increase. Positivity of each supremum supplies both existence and
boundedness of the corresponding level set. -/
theorem tendsto_sSup_positive_levelSets
    (f : ℝ → ℝ) (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (hlocal : ∀ M : ℝ, 0 < M → BddAbove (f '' Ioc 0 M))
    (hpos : ∀ n : ℕ, 0 < sSup {r : ℝ | 0 < r ∧ f r = a n}) :
    Tendsto (fun n => sSup {r : ℝ | 0 < r ∧ f r = a n}) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  obtain ⟨C, hC⟩ := hlocal (max M 1) (by positivity)
  filter_upwards [(tendsto_atTop.1 ha) (C + 1)] with n hn
  have hne : {r : ℝ | 0 < r ∧ f r = a n}.Nonempty := by
    by_contra h
    have he : {r : ℝ | 0 < r ∧ f r = a n} = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hp := hpos n
    simp [he] at hp
  have hbdd : BddAbove {r : ℝ | 0 < r ∧ f r = a n} := by
    by_contra h
    have hp := hpos n
    rw [csSup_of_not_bddAbove h] at hp
    simp at hp
  obtain ⟨r, hr, hfr⟩ := hne
  have hMr : max M 1 < r := by
    by_contra h
    have hfrC : f r ≤ C := hC ⟨r, ⟨hr, le_of_not_gt h⟩, rfl⟩
    linarith
  exact (le_max_left M 1).trans ((le_of_lt hMr).trans (le_csSup hbdd ⟨hr, hfr⟩))

/-- Positive integer-mass cone scale radii tend to infinity whenever the
radial cone expression is bounded above on each bounded positive interval. -/
theorem coneScaleRadius_tendsto_of_radial_bound
    {γ : ℝ} (hγ : 0 < γ) (hcirc : ℝ → ℂ → ℝ)
    (hlocal : ∀ M : ℝ, 0 < M →
      BddAbove ((fun r => hcirc r 0 + HarmonicBalls.lqgQ γ * Real.log r) '' Ioc 0 M))
    (hpos : ∀ n : ℕ, 0 < coneScaleRadius γ hcirc ((n : ℝ) + 1)) :
    Tendsto (fun n : ℕ => coneScaleRadius γ hcirc ((n : ℝ) + 1)) atTop atTop := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have ha : Tendsto (fun n : ℕ => γ⁻¹ * Real.log ((n : ℝ) + 1)) atTop atTop :=
    (Real.tendsto_log_atTop.comp hnat).const_mul_atTop (inv_pos.mpr hγ)
  exact tendsto_sSup_positive_levelSets _ _ ha hlocal hpos

end MatedCRT
