import LatticeProb.Analysis.ShellRadiusMargins
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LocalMass
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Radius choices and strict local-mass slack in the shell iteration. -/

namespace MatedCRT.Sec7

/-- Raising the lower bound on the shell radius to a positive power recovers
the odometer factor, including when the odometer is zero. -/
theorem shell_odometer_factor_le_radius_rpow
    {O ε K r β : ℝ} (hO : 0 ≤ O) (hε : 0 < ε) (hK : 0 ≤ K)
    (hβ : 0 < β) (hr : (O * ε * K) ^ (1 / β) ≤ r) :
    O * ε * K ≤ r ^ β :=
  LatticeProb.ShellRadiusMargins.shell_odometer_factor_le_radius_rpow hO hε hK hβ hr

/-- A strict coefficient margin makes the mass-bound estimate strictly
smaller than the hypothesis of Lemma 6.8. The factor `a` is the ratio between
the test radius and the shell radius. -/
theorem shell_strict_local_mass_slack
    {O ε K r β a s₁ C : ℝ}
    (hO : 0 ≤ O) (hε : 0 < ε) (hr : 0 < r)
    (ha : 0 < a) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * a ^ β * K) (hpower : O * ε * K ≤ r ^ β) :
    C * O < s₁ * (a * r) ^ β / ε :=
  LatticeProb.ShellRadiusMargins.shell_strict_local_mass_slack hO hε hr ha hs₁ hcoeff hpower

/-- A deterministic choice of radius coefficient leaves strict slack for
the mass bound, even if its constant is zero. -/
theorem exists_shell_radius_coefficient
    {a β s₁ C : ℝ} (ha : 0 < a) (hs₁ : 0 < s₁) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ C < s₁ * a ^ β * K :=
  LatticeProb.ShellRadiusMargins.exists_shell_radius_coefficient ha hs₁ hC

/-- The shell-radius formula and a strict coefficient choice together imply
the local-mass slack, with any nonnegative radius floor. -/
theorem shell_strict_local_mass_slack_of_radius
    {O ε K r β a s₁ C : ℝ}
    (hO : 0 ≤ O) (hε : 0 < ε) (hK : 0 ≤ K) (hr : 0 < r) (hβ : 0 < β)
    (ha : 0 < a) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * a ^ β * K)
    (hradius : (O * ε * K) ^ (1 / β) ≤ r) :
    C * O < s₁ * (a * r) ^ β / ε :=
  LatticeProb.ShellRadiusMargins.shell_strict_local_mass_slack_of_radius
    hO hε hK hr hβ ha hs₁ hcoeff hradius

/-- The doubled-recentering shell has test radius `c r / 8` and meets the
strict local-mass condition for the explicit radius coefficient. -/
theorem shell_local_count_lt_of_radius
    {ε ρ r R u D c O K β s₁ C : ℝ} {η : ℝ → ℂ} {A Λ Θ : Set ℤ}
    (hη : Continuous η) (hΛ : Λ.Finite) (hAΛ : A ⊆ Λ)
    (hO : 0 ≤ O) (hε : 0 < ε) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hr : 0 < r) (hβ : 0 < β) (hc : 0 < c) (hs₁ : 0 < s₁)
    (hcoeff : C < s₁ * (c / 8) ^ β * K)
    (hradius : (O * ε * K) ^ (1 / β) ≤ r)
    (hΘ : fillCells ε η Θ ⊆ Metric.ball 0 R)
    (hinner : A ⊆ (cellVertices ε η (Metric.thickening (r / 4) (fillCells ε η Θ)))ᶜ)
    (houter : A ⊆ cellVertices ε η (Metric.thickening u (fillCells ε η Θ)))
    (hdiam : ∀ a ∈ A, Metric.diam (cell ε η a) ≤ D)
    (hmargin : R + u + D + r / 4 ≤ ρ)
    (hmass : ∀ w : ℂ,
      cellVertices ε η (Metric.ball w (r / 4)) ⊆ cellVertices ε η (Metric.ball 0 ρ) \ Θ →
      ((cellVertices ε η (Metric.ball w (c * (r / 4))) ∩ Λ).ncard : ℝ) ≤ C * O) :
    ∀ z : ℂ, ((A ∩ cellVertices ε η (Metric.ball z ((c / 8) * r))).ncard : ℝ) <
      s₁ * ((c / 8) * r) ^ β / ε := by
  have hslack := shell_strict_local_mass_slack_of_radius hO hε hK hr hβ
    (by positivity : 0 < c / 8) hs₁ hcoeff hradius
  have hcount := shell_local_count_lt_of_mass_bound hη hΛ hAΛ (mul_nonneg hC hO) hslack
    hΘ hinner houter hdiam hmargin hmass
  convert hcount using 1
  ring

/-- The lower scale required by the survival event also places the larger
mass-test ball above the mesh-dependent scale, when its exponent is chosen
at least as large as the survival exponent. -/
theorem shell_mass_test_above_scale
    {ε ω βₘ c r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hω : ω ≤ βₘ)
    (hc : c ≤ 1) (hr : 0 ≤ r) (hmin : 10 * ε ^ ω ≤ (c / 8) * r) :
    ε ^ βₘ ≤ r / 4 :=
  LatticeProb.ShellRadiusMargins.shell_mass_test_above_scale hε hε1 hω hc hr hmin

end MatedCRT.Sec7
