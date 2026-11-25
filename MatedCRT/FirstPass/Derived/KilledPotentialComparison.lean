import MatedCRT.FirstPass.Derived.DiscGreenPotentialConvergence
import MatedCRT.FirstPass.Derived.KilledPotentialGreen

/-!
# Killed potentials of vaguely convergent rates on a disc

For a Borel rate `f ≥ 0` the potential of the occupation functional of Brownian motion killed on exiting the disc
`B_R = B(0, R)` is twice the Green potential of the measure `f(y) dy`:
`u_f(x) = 2 G_{B_R}(f dy)(x)` (`killedPotential_ball_eq_ofReal_greenPotential`).

If the rates `f_n` have a common upper power growth `∫_{B(z, s)} f_n ≤ s^β` and a common mass bound on `B_R`, and
`f_n(y) dy → ν₀` vaguely on the closed disc for a measure `ν₀` with the same bounds, then the killed potentials
`u_{f_n}` are eventually uniformly within `δ` of `2 G_{B_R} ν₀` on `B_R`
(`eventually_forall_killedPotential_ball_near`, from the uniform convergence of Green potentials,
`eventually_forall_abs_greenPotential_ball_sub_lt`), and `G_{B_R} ν₀` is bounded on the closed disc
(`exists_forall_greenPotential_ball_le`, from its Hölder continuity). Two such families with the same limit `ν₀`
therefore have eventually uniformly close and uniformly bounded killed potentials, the input of the comparison of
their occupation functionals (Armitage–Gardiner, §4.3; Fukushima–Oshima–Takeda (2011), §5.1).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology
open scoped NNReal ENNReal

namespace MatedCRT

open HarmonicBalls

/-- **The killed potential is twice the Green potential of the density measure.** For a Borel rate `f ≥ 0` and `x`
such that `G_{B_R}(x, ·)` is integrable for `f(y) dy`, `u_f(x) = 2 ∫ G_{B_R}(x, y) f(y) dy`. -/
theorem killedPotential_ball_eq_ofReal_greenPotential {R : ℝ} (hR : 0 < R) {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    {x : ℂ} (hint : Integrable (greenFunction (ball 0 R) x) (volume.withDensity f)) :
    killedPotential (ball 0 R) f x =
      ENNReal.ofReal (2 * greenPotential (ball 0 R) (volume.withDensity f) x) := by
  have hG0 : ∀ y, 0 ≤ greenFunction (ball (0 : ℂ) R) x y := fun y => greenFunction_nonneg isBounded_ball x y
  rw [killedPotential_ball_eq_lintegral_greenFunction hR hf x, greenPotential, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal (hint.const_mul 2)
      (ae_of_all _ fun y => mul_nonneg zero_le_two (hG0 y)),
    lintegral_withDensity_eq_lintegral_mul _ hf
      ((measurable_greenFunction isOpen_ball x).const_mul 2).ennreal_ofReal]
  exact lintegral_congr fun y => mul_comm _ _

variable {R r₀ β m : ℝ}

/-- **The Green potential of a measure with upper power growth is bounded on the closed disc.** -/
theorem exists_forall_greenPotential_ball_le (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β) (hm : 0 ≤ m)
    {ν₀ : Measure ℂ}
    (hup₀ : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, ν₀ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hmass₀ : ν₀ (ball 0 R) ≤ ENNReal.ofReal m) :
    ∃ M : ℝ, ∀ x ∈ closedBall (0 : ℂ) R, greenPotential (ball 0 R) ν₀ x ≤ M := by
  refine ⟨greenPotential (ball 0 R) ν₀ 0 +
    greenPotentialHolderConstant β r₀ m * R ^ greenPotentialHolderExponent β, fun x hx => ?_⟩
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  have h := (abs_greenPotential_ball_sub_le hR hr₀ hβ hm hup₀ hmass₀).2 x hx 0 h0
  rw [sub_zero] at h
  have hp : ‖x‖ ^ greenPotentialHolderExponent β ≤ R ^ greenPotentialHolderExponent β :=
    Real.rpow_le_rpow (norm_nonneg x) (mem_closedBall_zero_iff.1 hx) (greenPotentialHolderExponent_pos hβ).le
  have hp' := mul_le_mul_of_nonneg_left hp (greenPotentialHolderConstant_nonneg hβ hr₀ hm)
  have h1 := (abs_le.1 h).2
  linarith

/-- **Killed potentials of vaguely convergent rates.** Under a common upper power growth and a common mass bound on
`B_R` for the measures `f_n(y) dy` and `ν₀`, if `f_n(y) dy → ν₀` vaguely on the closed disc, then for every `δ > 0`,
eventually, `u_{f_n}` is within `δ` of `2 G_{B_R} ν₀` on `B_R`. -/
theorem eventually_forall_killedPotential_ball_near (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β) (hm : 0 ≤ m)
    {f : ℕ → ℂ → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) {ν₀ : Measure ℂ}
    (hup : ∀ n, ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      volume.withDensity (f n) (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hmass : ∀ n, volume.withDensity (f n) (ball 0 R) ≤ ENNReal.ofReal m)
    (hup₀ : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, ν₀ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hmass₀ : ν₀ (ball 0 R) ≤ ENNReal.ofReal m)
    (hvague : ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 R →
      Tendsto (fun n => ∫ y, F y ∂(volume.withDensity (f n))) atTop (𝓝 (∫ y, F y ∂ν₀)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ x ∈ ball (0 : ℂ) R,
      killedPotential (ball 0 R) (f n) x ≤
          ENNReal.ofReal (2 * greenPotential (ball 0 R) ν₀ x) + ENNReal.ofReal δ ∧
        ENNReal.ofReal (2 * greenPotential (ball 0 R) ν₀ x) ≤
          killedPotential (ball 0 R) (f n) x + ENNReal.ofReal δ := by
  filter_upwards [eventually_forall_abs_greenPotential_ball_sub_lt hR hr₀ hβ hm hup hmass hup₀ hmass₀ hvague
    (half_pos hδ)] with n hn x hx
  have hint := (abs_greenPotential_ball_sub_le hR hr₀ hβ hm (hup n) (hmass n)).1 x
  rw [killedPotential_ball_eq_ofReal_greenPotential hR (hf n) hint]
  obtain ⟨h1, h2⟩ := abs_lt.1 (hn x (ball_subset_closedBall hx))
  constructor
  · exact (ENNReal.ofReal_le_ofReal
      (show 2 * greenPotential (ball 0 R) (volume.withDensity (f n)) x ≤
        2 * greenPotential (ball 0 R) ν₀ x + δ by linarith)).trans ENNReal.ofReal_add_le
  · exact (ENNReal.ofReal_le_ofReal
      (show 2 * greenPotential (ball 0 R) ν₀ x ≤
        2 * greenPotential (ball 0 R) (volume.withDensity (f n)) x + δ by linarith)).trans ENNReal.ofReal_add_le

end MatedCRT
