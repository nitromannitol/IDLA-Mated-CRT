import MatedCRT.FirstPass.Derived.LogarithmicPotential
import MatedCRT.FirstPass.Derived.PlanarBrownianExitDynkin

/-!
# Expected occupation integrals before exit via the logarithmic potential

Let `D ⊆ ℂ` be a bounded open set, `y ∈ D`, `τ_D` the exit time of planar Brownian motion `𝓑^y`
from `D`, and `U g (x) = ∫ N(x, w) g(w) dw` the logarithmic potential of `g` (Newtonian kernel
`N(x, w) = -(2π)⁻¹ log |x - w|`). For smooth compactly supported `g`,

  `E_y ∫_0^{τ_D} g(𝓑_s) ds = 2 (U g(y) - E_y U g(𝓑_{τ_D}))`.

Proof: `Δ U g = -g`; Dynkin's formula at `τ_D` for `χ · U g`, with a smooth bump `χ` equal to `1`
near the closure of `D`. The path stays in `D` before `τ_D` and exits through `∂D`.
-/

open MeasureTheory Set Filter InnerProductSpace Laplacian MarkovProcess HarmonicBalls
  HarmonicBalls.Section6
open scoped ContDiff ENNReal NNReal Topology

namespace MatedCRT.KilledOccupation

/-- **Expected occupation integral before exit.** For a bounded open `D`, `y ∈ D` and a smooth
compactly supported `g`, `E_y ∫_0^{τ_D} g(𝓑_s) ds = 2 (U g(y) - E_y U g(𝓑_{τ_D}))`, where `U g` is
the logarithmic potential of `g`. -/
theorem integral_occupation_exitTime_eq_logPotential {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {y : ℂ} (hy : y ∈ D) :
    ∫ p, (∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ), g (p s.toNNReal))
        ∂(planarBrownianMotion y) =
      2 * (logPotential g y - ∫ p, logPotential g (p ((ContinuousPath.exitTime D p).toNNReal))
        ∂(planarBrownianMotion y)) := by
  obtain ⟨R, hR⟩ := hDb.subset_closedBall (0 : ℂ)
  let χ : ContDiffBump (0 : ℂ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  have hU : ContDiff ℝ ∞ (logPotential g) := contDiff_logPotential hg hgc
  have hclD : closure D ⊆ Metric.ball (0 : ℂ) (|R| + 1) := by
    refine (closure_minimal hR Metric.isClosed_closedBall).trans ?_
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    linarith [le_abs_self R]
  have hfeq : ∀ w ∈ Metric.ball (0 : ℂ) (|R| + 1), χ w * logPotential g w = logPotential g w := by
    intro w hw
    rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hw), one_mul]
  have hΔ : ∀ w ∈ Metric.ball (0 : ℂ) (|R| + 1),
      Δ (fun v ↦ χ v * logPotential g v) w = -g w := by
    intro w hw
    have heq : (fun v ↦ χ v * logPotential g v) =ᶠ[𝓝 w] logPotential g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
      exact hfeq v hv
    rw [(laplacian_congr_nhds heq).eq_of_nhds,
      laplacian_logPotential (hg.of_le (by norm_num)) hgc]
  have hdyn := planarBrownianMotion_exit_dynkin hD hDb (χ.contDiff.mul hU)
    χ.hasCompactSupport.mul_right y
  beta_reduce at hdyn
  -- the exit position lies on `∂D`, where `χ = 1`
  have hend : ∫ p, χ (p ((ContinuousPath.exitTime D p).toNNReal)) *
        logPotential g (p ((ContinuousPath.exitTime D p).toNNReal)) ∂(planarBrownianMotion y) =
      ∫ p, logPotential g (p ((ContinuousPath.exitTime D p).toNNReal))
        ∂(planarBrownianMotion y) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_planarBrownianMotion_eval_zero y,
      ae_planarBrownian_exitTime_bounded_lt_top y hDb] with p h0 hfin
    have h0D : p 0 ∈ D := by rw [h0]; exact hy
    have hmem := ContinuousPath.coordinate_exitTime_mem_frontier D hD p h0D hfin.ne
    exact hfeq _ (hclD (frontier_subset_closure hmem))
  -- before exit the path stays in `D`, where `Δ (χ · U g) = -g`
  have hdrift : ∀ p : ContinuousPath ℂ,
      (∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ),
        Δ (fun v ↦ χ v * logPotential g v) (p s.toNNReal)) =
      -∫ s in (0 : ℝ)..((ContinuousPath.exitTime D p).toNNReal : ℝ), g (p s.toNNReal) := by
    intro p
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    have hsingle : ∀ᵐ s : ℝ, s ≠ ((ContinuousPath.exitTime D p).toNNReal : ℝ) := by
      rw [ae_iff]
      simpa only [Ne, not_not, Set.ofPred_eq_eq_singleton] using
        measure_singleton (((ContinuousPath.exitTime D p).toNNReal : ℝ))
    filter_upwards [hsingle] with s hs hmem
    rw [Set.uIoc_of_le (NNReal.coe_nonneg _)] at hmem
    have hlt : s.toNNReal < (ContinuousPath.exitTime D p).toNNReal :=
      (Real.toNNReal_lt_iff_lt_coe hmem.1.le).mpr (lt_of_le_of_ne hmem.2 hs)
    have hpD : p s.toNNReal ∈ D := ContinuousPath.mem_of_lt_exitTime D p _
      (lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hlt) ENNReal.coe_toNNReal_le_self)
    exact hΔ _ (hclD (subset_closure hpD))
  rw [hend, hfeq y (hclD (subset_closure hy))] at hdyn
  simp only [hdrift, integral_neg] at hdyn
  linarith [hdyn]

end MatedCRT.KilledOccupation
