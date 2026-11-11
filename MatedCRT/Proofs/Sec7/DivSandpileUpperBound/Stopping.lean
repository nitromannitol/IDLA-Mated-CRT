import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Iteration
import MatedCRT.LPStaging.Analysis.GeometricShellSums
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Stopping-time and radius estimates for the shell iteration. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- A maximum which contracts whenever it exceeds a positive threshold reaches
that threshold in finitely many steps. -/
theorem exists_shell_maximum_le_threshold (O : ℕ → ℝ) (q B : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hB : 0 < B)
    (hstep : ∀ k, B < O k → O (k + 1) ≤ q * O k) :
    ∃ n, O n ≤ B :=
  LatticeProb.GeometricShellSums.exists_shell_maximum_le_threshold O q B hq hq1 hB hstep

/-- Before the first threshold crossing, the number of shell steps is bounded
by the logarithm of the initial-to-threshold odometer ratio. -/
theorem shell_steps_lt_log_ratio (O : ℕ → ℝ) (q B : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hB : 0 < B) (n : ℕ)
    (hbefore : B < O n)
    (hstep : ∀ k < n, O (k + 1) ≤ q * O k) :
    (n : ℝ) < Real.log (O 0 / B) / (-Real.log q) :=
  LatticeProb.GeometricShellSums.shell_steps_lt_log_ratio O q B hq hq1 hB n hbefore hstep

/-- The first crossing exists and is at most one more than the logarithmic bound
for the previous shell. The contraction is only required before crossing. -/
theorem exists_first_shell_threshold_with_log_bound (O : ℕ → ℝ) (q B : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hB : 0 < B) (hinitial : B < O 0)
    (hstep : ∀ k, B < O k → O (k + 1) ≤ q * O k) :
    ∃ τ : ℕ, O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (τ : ℝ) < Real.log (O 0 / B) / (-Real.log q) + 1 :=
  LatticeProb.GeometricShellSums.exists_first_shell_threshold_with_log_bound
    O q B hq hq1 hB hinitial hstep

/-- The logarithmic odometer ratio in the second phase of the iteration. -/
theorem log_initial_to_threshold (C ε ω : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    Real.log ((C / ε) / ε ^ (-ω)) =
      Real.log C + (1 - ω) * Real.log ε⁻¹ :=
  LatticeProb.GeometricShellSums.log_initial_to_threshold C ε ω hC hε

/-- For an initial maximum at most `C / ε` and threshold `ε ^ (-ω)`, the
first threshold crossing has the logarithmic bound used in Step 2. -/
theorem exists_first_shell_threshold_log_scale (O : ℕ → ℝ) (q C ε ω : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hC : 0 < C) (hε : 0 < ε)
    (hinitial : ε ^ (-ω) < O 0) (hupper : O 0 ≤ C / ε)
    (hstep : ∀ k, ε ^ (-ω) < O k → O (k + 1) ≤ q * O k) :
    ∃ τ : ℕ, O τ ≤ ε ^ (-ω) ∧ (∀ k < τ, ε ^ (-ω) < O k) ∧
      (τ : ℝ) < (Real.log C + (1 - ω) * Real.log ε⁻¹) / (-Real.log q) + 1 :=
  LatticeProb.GeometricShellSums.exists_first_shell_threshold_log_scale
    O q C ε ω hq hq1 hC hε hinitial hupper hstep

/-- A maximum-based radius reduces to its geometric branch while it is strictly
above the floor. This uses an inequality, not equality for the maximum. -/
theorem shell_radius_le_geometric_above_floor {r A q R : ℝ} {k : ℕ}
    (hr : r ≤ max (A * q ^ k) R) (hfloor : R < r) : r ≤ A * q ^ k :=
  LatticeProb.GeometricShellSums.shell_radius_le_geometric_above_floor hr hfloor

/-- A uniformly bounded tail contributes at most its length times the floor. -/
theorem shell_radius_tail_sum_le (r : ℕ → ℝ) (R : ℝ) (n : ℕ)
    (hr : ∀ k < n, r k ≤ R) : ∑ k ∈ Finset.range n, r k ≤ (n : ℝ) * R :=
  LatticeProb.GeometricShellSums.shell_radius_tail_sum_le r R n hr

/-- The radius at the next shell inherits geometric decay from the current
odometer maximum, up to the prescribed floor. The exponent retains the index
shift in the definition of the radius. -/
theorem shell_radius_from_odometer_contraction
    (O r : ℕ → ℝ) (q K α R : ℝ) (n : ℕ)
    (hq : 0 ≤ q) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hO : ∀ k ≤ n, 0 ≤ O k)
    (hstep : ∀ k < n, O (k + 1) ≤ q * O k)
    (hr : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) R) :
    ∀ k < n, r (k + 1) ≤ max (((O 0 * K) ^ α) * (q ^ α) ^ k) R :=
  LatticeProb.GeometricShellSums.shell_radius_from_odometer_contraction
    O r q K α R n hq hK hα hO hstep hr

/-- A maximum of a geometric radius and a nonnegative floor is bounded in
total by the geometric series plus the accumulated floor. -/
theorem shell_radii_max_sum_le (r : ℕ → ℝ) (A q R : ℝ)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq1 : q < 1) (hR : 0 ≤ R) (n : ℕ)
    (hr : ∀ k < n, r k ≤ max (A * q ^ k) R) :
    ∑ k ∈ Finset.range n, r k ≤ A / (1 - q) + (n : ℝ) * R :=
  LatticeProb.GeometricShellSums.shell_radii_max_sum_le r A q R hA hq hq1 hR n hr

/-- For the paper's shifted radius definition, a contracting odometer gives a
geometric-series bound plus the radius floor and the initial radius. -/
theorem shell_radii_sum_from_odometer_contraction
    (O r : ℕ → ℝ) (q K α R : ℝ) (n : ℕ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hK : 0 ≤ K) (hα : 0 < α) (hR : 0 ≤ R)
    (hO : ∀ k ≤ n, 0 ≤ O k)
    (hstep : ∀ k < n, O (k + 1) ≤ q * O k)
    (hr : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) R) :
    ∑ k ∈ Finset.range (n + 1), r k ≤
      r 0 + (O 0 * K) ^ α / (1 - q ^ α) + (n : ℝ) * R :=
  LatticeProb.GeometricShellSums.shell_radii_sum_from_odometer_contraction
    O r q K α R n hq hq1 hK hα hR hO hstep hr

/-- First threshold crossing with the radius indexed by the previous maximum.
This combines the stopping-time estimate with the radius formula, including the
initial radius and the cell-diameter error. -/
theorem exists_shell_threshold_with_shifted_radius_budget
    (O r : ℕ → ℝ) (q K α R D C ε ω δ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hK : 0 ≤ K) (hα : 0 < α)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hC : 0 < C) (hε : 0 < ε)
    (hO : ∀ k, 0 ≤ O k) (hinitial : ε ^ (-ω) < O 0) (hupper : O 0 ≤ C / ε)
    (hstep : ∀ k, ε ^ (-ω) < O k → O (k + 1) ≤ q * O k)
    (hr : ∀ k, r (k + 1) ≤ max ((O k * K) ^ α) R)
    (hbudget : let L := (Real.log C + (1 - ω) * Real.log ε⁻¹) / (-Real.log q) + 1
      r 0 + (O 0 * K) ^ α / (1 - q ^ α) + L * R + (L + 1) * (2 * D) ≤ δ) :
    ∃ n : ℕ, O n ≤ ε ^ (-ω) ∧
      (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D) ≤ δ :=
  LatticeProb.GeometricShellSums.exists_shell_threshold_with_shifted_radius_budget
    O r q K α R D C ε ω δ hq hq1 hK hα hR hD hC hε hO hinitial hupper hstep hr hbudget

/-- The geometric, floor, and cell-diameter contributions fit a common
iteration budget when the stopping index has a deterministic upper bound. -/
theorem shell_iteration_budget_le (r : ℕ → ℝ) (A q R D L : ℝ)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq1 : q < 1) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (n : ℕ) (hn : (n : ℝ) ≤ L)
    (hr : ∀ k < n, r k ≤ max (A * q ^ k) R) :
    (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D) ≤
      A / (1 - q) + L * R + (L + 1) * (2 * D) :=
  LatticeProb.GeometricShellSums.shell_iteration_budget_le r A q R D L hA hq hq1 hR hD n hn hr

/-- Fixed-factor odometer contraction and a logarithmic radius budget give a
stopping shell with both a small boundary maximum and controlled total growth. -/
theorem exists_shell_threshold_with_iteration_budget
    (O r : ℕ → ℝ) (q p C ε ω A R D δ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hp : 0 ≤ p) (hp1 : p < 1)
    (hC : 0 < C) (hε : 0 < ε) (hA : 0 ≤ A) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hinitial : ε ^ (-ω) < O 0) (hupper : O 0 ≤ C / ε)
    (hstep : ∀ k, ε ^ (-ω) < O k → O (k + 1) ≤ q * O k)
    (hr : ∀ k, (∀ j < k, ε ^ (-ω) < O j) → r k ≤ max (A * p ^ k) R)
    (hbudget : let L := (Real.log C + (1 - ω) * Real.log ε⁻¹) / (-Real.log q) + 1
      A / (1 - p) + L * R + (L + 1) * (2 * D) ≤ δ) :
    ∃ n : ℕ, O n ≤ ε ^ (-ω) ∧
      (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D) ≤ δ :=
  LatticeProb.GeometricShellSums.exists_shell_threshold_with_iteration_budget
    O r q p C ε ω A R D δ hq hq1 hp hp1 hC hε hA hR hD hinitial hupper hstep hr hbudget

/-- The floor-scale contribution to the total radius vanishes, even with a
logarithmic number of shell steps. -/
theorem tendsto_shell_floor_log_bound (A B ω : ℝ) (hω : 0 < ω) :
    Tendsto (fun ε : ℝ => (A + B * Real.log ε⁻¹) * ε ^ ω) (𝓝[>] 0) (𝓝 0) :=
  LatticeProb.GeometricShellSums.tendsto_shell_floor_log_bound A B ω hω

/-- With logarithmically many shells, power-law radius floors and cell diameters do not
contribute to the limiting spatial budget. -/
theorem tendsto_shell_iteration_budget
    (A p a b R D ω ζ : ℝ) (hω : 0 < ω) (hζ : 0 < ζ) :
    Tendsto (fun ε : ℝ => A / (1 - p) +
      (a + b * Real.log ε⁻¹) * (R * ε ^ ω) +
      (a + b * Real.log ε⁻¹ + 1) * (2 * (D * ε ^ ζ)))
      (𝓝[>] 0) (𝓝 (A / (1 - p))) :=
  LatticeProb.GeometricShellSums.tendsto_shell_iteration_budget A p a b R D ω ζ hω hζ

/-- Any strict margin above the geometric contribution eventually covers the
floor and cell-diameter terms in the shell budget. -/
theorem eventually_shell_iteration_budget_lt
    (A p a b R D ω ζ δ : ℝ) (hω : 0 < ω) (hζ : 0 < ζ)
    (hδ : A / (1 - p) < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      A / (1 - p) + (a + b * Real.log ε⁻¹) * (R * ε ^ ω) +
        (a + b * Real.log ε⁻¹ + 1) * (2 * (D * ε ^ ζ)) < δ :=
  LatticeProb.GeometricShellSums.eventually_shell_iteration_budget_lt
    A p a b R D ω ζ δ hω hζ hδ

/-- The logarithmic first-crossing bound yields an admissible shell budget at
all sufficiently small scales whenever the geometric contribution has a strict
margin below the target. -/
theorem eventually_first_crossing_budget_lt
    (A p q C ω R D α β δ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hδ : A / (1 - p) < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      let L := (Real.log C + (1 - ω) * Real.log ε⁻¹) / (-Real.log q) + 1
      A / (1 - p) + L * (R * ε ^ α) + (L + 1) * (2 * (D * ε ^ β)) < δ :=
  LatticeProb.GeometricShellSums.eventually_first_crossing_budget_lt
    A p q C ω R D α β δ hα hβ hδ

/-- At sufficiently small scales, every fixed-factor shell iteration satisfying
the stated odometer and radius bounds reaches its threshold within the target
spatial budget. -/
theorem eventually_exists_shell_threshold_with_budget
    (q p C ω A R D α β δ : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hp : 0 ≤ p) (hp1 : p < 1)
    (hC : 0 < C) (hA : 0 ≤ A) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hα : 0 < α) (hβ : 0 < β) (hδ : A / (1 - p) < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ O r : ℕ → ℝ,
      ε ^ (-ω) < O 0 → O 0 ≤ C / ε →
      (∀ k, ε ^ (-ω) < O k → O (k + 1) ≤ q * O k) →
      (∀ k, (∀ j < k, ε ^ (-ω) < O j) →
        r k ≤ max (A * p ^ k) (R * ε ^ α)) →
      ∃ n : ℕ, O n ≤ ε ^ (-ω) ∧
        (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * (D * ε ^ β)) ≤ δ :=
  LatticeProb.GeometricShellSums.eventually_exists_shell_threshold_with_budget
    q p C ω A R D α β δ hq hq1 hp hp1 hC hA hR hD hα hβ hδ

end MatedCRT.Sec7
