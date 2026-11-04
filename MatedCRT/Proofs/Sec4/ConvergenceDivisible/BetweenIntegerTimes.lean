import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianIntegerStrongLaw

/-! # Extension from integer times using oscillation bounds -/

namespace MatedCRT

open Filter Topology MeasureTheory HarmonicBalls

/-- Sublinear growth at integer times extends to all positive times if the
oscillations on consecutive unit intervals are sublinear. -/
theorem tendsto_div_atTop_of_integer_and_oscillation {f : ℝ → ℝ}
    (hinteger : Tendsto (fun n : ℕ => f n / (n : ℝ)) atTop (𝓝 0))
    (hosc : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      (n : ℝ) ≤ t → t ≤ n + 1 → |f t - f n| ≤ ε * n) :
    Tendsto (fun t : ℝ => f t / t) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : 0 < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hinteger) (ε / 2) he
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hosc (ε / 2) he)
  let N := max (max N₁ N₂) 1
  refine ⟨N, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg N) ht
  let n := ⌊t⌋₊
  have hnN : N ≤ n := (Nat.le_floor_iff ht0).2 ht
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hnN
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht0
  have htpos : 0 < t := lt_of_lt_of_le hnpos hnt
  have htn : t ≤ (n : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one t)
  have hnN₁ : N₁ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hnN)
  have hnN₂ : N₂ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hnN)
  have hsmall : |f n| < (ε / 2) * n := by
    have h := hN₁ n hnN₁
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hnpos] at h
    exact (div_lt_iff₀ hnpos).mp h
  have hosc' : |f t - f n| ≤ (ε / 2) * n := hN₂ n hnN₂ t hnt htn
  have habs : |f t| < ε * t := by
    have htri : |f t| ≤ |f t - f n| + |f n| := by
      simpa using abs_add_le (f t - f n) (f n)
    have hmul : (ε / 2) * n ≤ (ε / 2) * t := mul_le_mul_of_nonneg_left hnt he.le
    linarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos htpos]
  exact (div_lt_iff₀ htpos).mpr habs

/-- It remains to control unit-interval oscillations of the centered radial
process in order to obtain convergence-event measurability. -/
theorem convergenceDivisibleEventMeasurable_of_radial_oscillation
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hscale : ConeEnvironmentScalingStep 𝒮) (hpos : ConeScaleRadiusStep)
    (hosc : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ᵐ ω ∂S.P, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
        (n : ℝ) ≤ t → t ≤ n + 1 →
        |(S.hcirc ω (Real.exp (-t)) 0 - γ * t) -
          (S.hcirc ω (Real.exp (-(n : ℝ))) 0 - γ * n)| ≤ ε * n) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_sublinear_radial 𝒮 h27 hscale hpos
  intro γ hγ hγ2 Ω _ S hS
  filter_upwards [hS.isQuantumCone.ae_radial_integer_sublinear,
    hosc γ hγ hγ2 Ω S hS] with ω hi ho
  exact tendsto_div_atTop_of_integer_and_oscillation hi ho

end MatedCRT
