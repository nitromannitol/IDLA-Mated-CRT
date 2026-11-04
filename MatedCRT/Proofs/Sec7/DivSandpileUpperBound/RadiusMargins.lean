import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusEnvelope

/-! Uniform radius bounds imply the geometric shell margins. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- A larger mesh exponent beats any fixed coefficient times a smaller mesh
exponent near zero. -/
theorem eventually_mul_rpow_lt_mul_rpow
    {a b A B : ℝ} (hab : b < a) (hB : 0 < B) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, A * ε ^ a < B * ε ^ b := by
  have hpow := tendsto_rpow_nhdsGT_zero (sub_pos.mpr hab)
  have hlim : Tendsto (fun ε : ℝ => A * ε ^ (a - b)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hpow.const_mul A
  filter_upwards [self_mem_nhdsWithin, (tendsto_order.1 hlim).2 B hB] with ε hε hsmall
  have hmul := mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hε b)
  have hpow' : ε ^ (a - b) * ε ^ b = ε ^ a := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  calc
    A * ε ^ a = (A * ε ^ (a - b)) * ε ^ b := by rw [← hpow']; ring
    _ < B * ε ^ b := hmul

/-- A polynomial shell-radius floor with a smaller exponent lies above the
minimum radius required by the survival estimate. -/
theorem eventually_shell_survival_floor
    {ω q c : ℝ} (hqω : q < ω) (hc : 0 < c) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 10 * ε ^ ω < (c / 8) * ε ^ q :=
  eventually_mul_rpow_lt_mul_rpow hqω (by positivity)

/-- Lower and upper radius envelopes supply the geometric margins required by
the local mass and survival estimates. -/
theorem shell_margins_of_radius_bounds
    (ε ω r L U D R ρ c dd : ℝ)
    (hc : 0 ≤ c) (hr : L ≤ r) (hrU : r ≤ U)
    (hD : D ≤ L / 2) (hambient : U + R ≤ ρ)
    (hclosure : R + U / 4 + D < ρ / 2)
    (hmargin : R + (((c / 8) * U + D) + U / 4) + D + U / 4 ≤ ρ)
    (hmin : 10 * ε ^ ω ≤ (c / 8) * L) (hmax : (c / 8) * U ≤ dd) :
    D ≤ r / 2 ∧ r + R ≤ ρ ∧ R + r / 4 + D < ρ / 2 ∧
      R + (((c / 8) * r + D) + r / 4) + D + r / 4 ≤ ρ ∧
      10 * ε ^ ω ≤ (c / 8) * r ∧ (c / 8) * r ≤ dd := by
  have hc' : 0 ≤ c / 8 := by positivity
  have hcr := mul_le_mul_of_nonneg_left hr hc'
  have hcrU := mul_le_mul_of_nonneg_left hrU hc'
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  exact ⟨hmin.trans hcr, hcrU.trans hmax⟩

/-- A positive survival cutoff above the shell radius also bounds the smaller
radius at which the survival estimate is tested. -/
theorem shell_test_radius_le_cutoff
    (c r dd : ℝ) (hc : c ≤ 1) (hr : 0 ≤ r) (hdd : r ≤ dd) :
    (c / 8) * r ≤ dd := by
  have h := mul_le_mul_of_nonneg_right (show c / 8 ≤ 1 by linarith) hr
  linarith

end MatedCRT.Sec7
