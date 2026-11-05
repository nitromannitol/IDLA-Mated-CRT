import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusChoice

/-! Geometric margins for the delayed shell radii.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

/-- A decreasing-prefix upper cutoff and the deterministic radius floor give
all geometric margins needed by the logarithmic shell contraction. -/
theorem delayed_shell_margins_of_envelope
    (O : ℕ → ℝ) (K α F ε ω U D R ρ c dd : ℝ) (n : ℕ)
    (hc : 0 ≤ c)
    (hcut : ∀ k < n, (∀ j < k, O (j + 1) ≤ O j) →
      delayedShellRadius O K α F k ≤ U)
    (hD : D ≤ F / 2) (hambient : U + R ≤ ρ)
    (hclosure : R + U / 4 + D < ρ / 2)
    (hmargin : R + (((c / 8) * U + D) + U / 4) + D + U / 4 ≤ ρ)
    (hmin : 10 * ε ^ ω ≤ (c / 8) * F) (hmax : (c / 8) * U ≤ dd) :
    ∀ k < n, (∀ j < k, O (j + 1) ≤ O j) →
      let r := delayedShellRadius O K α F k
      D ≤ r / 2 ∧ r + R ≤ ρ ∧ R + r / 4 + D < ρ / 2 ∧
      R + (((c / 8) * r + D) + r / 4) + D + r / 4 ≤ ρ ∧
      10 * ε ^ ω ≤ (c / 8) * r ∧ (c / 8) * r ≤ dd := by
  intro k hk hprev
  exact shell_margins_of_radius_bounds ε ω _ F U D R ρ c dd hc
    ((delayedShellRadius_bounds O K α F).2.2 k) (hcut k hk hprev)
    hD hambient hclosure hmargin hmin hmax


/-- A shell centered inside the half-radius ball has a positive upper cutoff
that makes the ambient margins valid for every sufficiently small diameter. -/
theorem shell_radius_cutoff_of_half_radius_gap
    (R ρ c dd : ℝ) (hR : 0 ≤ R) (hgap : R < ρ / 2)
    (hc : c ≤ 1) (hdd : 0 < dd) :
    let U := min 1 (min dd ((ρ / 2 - R) / 4))
    0 < U ∧ U ≤ 1 ∧ U ≤ dd ∧
    ∀ D : ℝ, 0 ≤ D → D ≤ U →
      U + R ≤ ρ ∧ R + U / 4 + D < ρ / 2 ∧
      R + (((c / 8) * U + D) + U / 4) + D + U / 4 ≤ ρ ∧
      (c / 8) * U ≤ dd := by
  let U := min 1 (min dd ((ρ / 2 - R) / 4))
  have hU : 0 < U := by dsimp [U]; positivity
  have hU1 : U ≤ 1 := min_le_left _ _
  have hUdd : U ≤ dd := (min_le_right _ _).trans (min_le_left _ _)
  have hUgap : U ≤ (ρ / 2 - R) / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hU, hU1, hUdd, ?_⟩
  intro D hD hDU
  have hcU : (c / 8) * U ≤ U := by
    have hh := mul_le_mul_of_nonneg_right (show c / 8 ≤ 1 by linarith) hU.le
    simpa only [one_mul] using hh
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · exact hcU.trans hUdd

end MatedCRT.Sec7
