import LatticeProb.Analysis.ShellRadiusMargins
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusEnvelope

/-! Uniform radius bounds imply the geometric shell margins. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- A larger mesh exponent beats any fixed coefficient times a smaller mesh
exponent near zero. -/
theorem eventually_mul_rpow_lt_mul_rpow
    {a b A B : ℝ} (hab : b < a) (hB : 0 < B) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, A * ε ^ a < B * ε ^ b :=
  LatticeProb.ShellRadiusMargins.eventually_mul_rpow_lt_mul_rpow hab hB

/-- A polynomial shell-radius floor with a smaller exponent lies above the
minimum radius required by the survival estimate. -/
theorem eventually_shell_survival_floor
    {ω q c : ℝ} (hqω : q < ω) (hc : 0 < c) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 10 * ε ^ ω < (c / 8) * ε ^ q :=
  LatticeProb.ShellRadiusMargins.eventually_shell_survival_floor hqω hc

/-- One polynomial radius floor simultaneously dominates the cell diameter
and the minimum scale in the survival estimate. -/
theorem exists_shell_radius_floor_exponent
    {ω d c : ℝ} (hω : 0 < ω) (hd : 0 < d) (hc : 0 < c) :
    ∃ q : ℝ, 0 < q ∧ q < ω ∧ q < d ∧
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ε ^ d ≤ ε ^ q / 2 ∧ 10 * ε ^ ω ≤ (c / 8) * ε ^ q :=
  LatticeProb.ShellRadiusMargins.exists_shell_radius_floor_exponent hω hd hc

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
      10 * ε ^ ω ≤ (c / 8) * r ∧ (c / 8) * r ≤ dd :=
  LatticeProb.ShellRadiusMargins.shell_margins_of_radius_bounds ε ω r L U D R ρ c dd
    hc hr hrU hD hambient hclosure hmargin hmin hmax

/-- A positive survival cutoff above the shell radius also bounds the smaller
radius at which the survival estimate is tested. -/
theorem shell_test_radius_le_cutoff
    (c r dd : ℝ) (hc : c ≤ 1) (hr : 0 ≤ r) (hdd : r ≤ dd) :
    (c / 8) * r ≤ dd :=
  LatticeProb.ShellRadiusMargins.shell_test_radius_le_cutoff c r dd hc hr hdd

end MatedCRT.Sec7
