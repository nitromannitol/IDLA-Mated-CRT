import MatedCRT.Proofs.LBM.ExitPosition
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit
import HarmonicBalls.Proofs.Sec6.BoundedHarmonicExit
import HarmonicBalls.Proofs.Sec4.Sweep

/-!
# The exit distribution of planar Brownian motion from a disc is harmonic measure

For boundary data `φ` continuous on the closed disc `cl B_r(z)` and a starting point `x ∈ B_r(z)`,
`E_x[φ(𝓑_{τ_{B_r(z)}})]` is the Poisson integral `P_{B_r(z)}[φ](x)` (Kakutani 1944; Mörters-Peres,
*Brownian Motion*, Theorems 3.12 and 3.44). The proof applies the harmonic representation of bounded
continuous harmonic functions (HB `Section6.harmonic_eq_integral_planarBrownian_exitTime`, through the
planar Brownian generator `Δ/2`) to the Poisson modification of a continuous bounded extension of `φ`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess InnerProductSpace
open scoped ENNReal NNReal

/-- The exit position of a continuous path is its value at MarkovProcess's exit time. -/
theorem pathExitPosition_eq_eval_exitTime (U : Set ℂ) (b : ContinuousPath ℂ) :
    pathExitPosition U b = b ((ContinuousPath.exitTime U b).toNNReal) := by
  simp only [pathExitPosition]
  rfl

/-- Planar Brownian motion started inside a disc leaves it on its boundary circle. -/
theorem ae_planarBrownianMotion_pathExitPosition_mem_sphere {z x : ℂ} {r : ℝ}
    (hx : x ∈ ball z r) :
    ∀ᵐ b : ContinuousPath ℂ ∂planarBrownianMotion x,
      pathExitPosition (ball z r) b ∈ sphere z r := by
  filter_upwards [ae_planarBrownianMotion_eval_zero x,
    ae_planarBrownianMotion_exit_any_ball_lt_top x z r] with b hstart hfin
  apply frontier_ball_subset_sphere
  exact pathExitPosition_mem_frontier_of_continuous isOpen_ball b.continuous
    (by simpa [hstart] using hx) hfin

/-- **Harmonic measure of a disc.** For `φ` continuous on `cl B_r(z)` and `x ∈ B_r(z)`,
`E_x[φ(𝓑_{τ_{B_r(z)}})] = P_{B_r(z)}[φ](x)`. -/
theorem integral_pathExitPosition_eq_discPoissonIntegral {z : ℂ} {r : ℝ} (hr : 0 < r)
    {φ : ℂ → ℝ} (hφ : ContinuousOn φ (closedBall z r)) {x : ℂ} (hx : x ∈ ball z r) :
    ∫ b, φ (pathExitPosition (ball z r) b) ∂planarBrownianMotion x =
      discPoissonIntegral φ z r x := by
  set ψ : ℂ → ℝ := φ ∘ ballRetraction z r with hψdef
  have hψ : Continuous ψ :=
    hφ.comp_continuous (continuous_ballRetraction z hr) (ballRetraction_mem z hr)
  obtain ⟨M, hM⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hφ
  have hψM : ∀ y, ‖ψ y‖ ≤ M := fun y => hM _ (ballRetraction_mem z hr y)
  have hψφ : ∀ y ∈ closedBall z r, ψ y = φ y := fun y hy => by
    simp only [hψdef, Function.comp_apply, ballRetraction_of_mem z hr hy]
  set q := discSweep Set.univ z r ψ with hqdef
  have hD : IsSweepDisc Set.univ z r := ⟨hr, subset_univ _⟩
  have hq : Continuous q := continuousOn_univ.mp
    (continuousOn_discSweep isOpen_univ hψ.continuousOn)
  have hci : CircleIntegrable ψ z r := hD.circleIntegrable hψ.continuousOn
  have hh : HarmonicOnNhd q (ball z r) := by
    intro y hy
    have heq : q =ᶠ[𝓝 y] discPoissonIntegral ψ z r := by
      filter_upwards [isOpen_ball.mem_nhds hy] with w hw
      exact discSweep_of_mem hD hw
    exact (harmonicAt_congr_nhds heq).2 (harmonicOnNhd_discPoissonIntegral hci y hy)
  have hbound : ∀ y, ‖q y‖ ≤ M := by
    intro y
    by_cases hy : y ∈ ball z r
    · rw [show q y = discPoissonIntegral ψ z r y from discSweep_of_mem hD hy]
      have hb (w : ℂ) : -M ≤ ψ w ∧ ψ w ≤ M := abs_le.mp (by simpa using hψM w)
      have hlo := le_discPoissonIntegral hci hy (fun ζ _ => (hb ζ).1)
      have hhi : discPoissonIntegral ψ z r y ≤ M := by
        rw [← discPoissonIntegral_const M hy]
        exact discPoissonIntegral_mono hci continuousOn_const.circleIntegrable' hy
          (fun ζ _ => (hb ζ).2)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hlo, hhi⟩
    · rw [show q y = ψ y from discSweep_of_not (fun h => hy h.2)]
      exact hψM y
  have he := Section6.harmonic_eq_integral_planarBrownian_exitTime isOpen_ball isBounded_ball
    hq hh hbound hx
  have hEq : ∀ᵐ b : ContinuousPath ℂ ∂planarBrownianMotion x,
      q (b ((ContinuousPath.exitTime (ball z r) b).toNNReal)) =
        φ (pathExitPosition (ball z r) b) := by
    filter_upwards [ae_planarBrownianMotion_pathExitPosition_mem_sphere hx] with b hb
    rw [← pathExitPosition_eq_eval_exitTime, hqdef,
      discSweep_of_not (fun h => (sphere_disjoint_ball.ne_of_mem hb h.2) rfl),
      hψφ _ (sphere_subset_closedBall hb)]
  rw [integral_congr_ae hEq] at he
  rw [← he, show q x = discPoissonIntegral ψ z r x from discSweep_of_mem hD hx]
  refine Real.circleAverage_congr_sphere fun ζ hζ => ?_
  rw [abs_of_pos hr] at hζ
  simp only [Pi.smul_apply', hψφ ζ (sphere_subset_closedBall hζ)]

end MatedCRT
