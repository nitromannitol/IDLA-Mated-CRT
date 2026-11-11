import MatedCRT.FirstPass.S4S6c.CircleIntegrability
import LatticeProb.Analysis.CircleKernelBounds

/-!
# Uniform bound on the corrected kernel over the good annulus

For `u` with `‖u - z‖ ≤ 2R` and `v = circleMap z (3R/2) θ`, the corrected kernel `K(u,v) = log(R/|u-v|) + 1` satisfies
`K ≥ -a₀` with `a₀ = log 4 - 1` (since `|u - v| ≤ 4R`), and its circle average is at most `log R + 1 - log(3R/2)`
(the closed form `circleAverage_kernel_eq` drops the nonnegative `log⁺` term). Consequently
`∫_{(0,2π]} |K(u, circleMap θ)| dθ ≤ 2π (log R + 1 - log(3R/2) + 2a₀)` uniformly in `u`: the integrable majorant used for
the joint integrability (`CircleIntegrability.lean`). Open: the product integrability itself and the Fubini assembly.

The seven statements below are the specialisations of the general kernel bounds of `LatticeProb.CircleKernelBounds`
(`MatedCRT/LPStaging/Analysis/CircleKernelBounds.lean`, a copy of the LatticeProb module); the proofs are citations.
-/

open MeasureTheory Real Set Metric

namespace MatedCRT

/-- The distance of a point of the circle `∂B_t(z)` from its centre is `|t|`. -/
theorem norm_circleMap_sub_center' (z : ℂ) (t θ : ℝ) : ‖z - circleMap z t θ‖ = |t| :=
  LatticeProb.CircleKernelBounds.norm_circleMap_sub_center' z t θ

/-- `log 4 ≥ 1`, so that `a₀ = log 4 - 1 ≥ 0`. -/
theorem one_le_log_four : 1 ≤ Real.log 4 :=
  LatticeProb.CircleKernelBounds.one_le_log_four

/-- The kernel is bounded below on the annulus: `log(R/|u-v|) + 1 ≥ 1 - log 4` when `|u-v| ≤ 4R`. -/
theorem kernel_ge_neg {R : ℝ} {u v : ℂ} (huv : ‖u - v‖ ≤ 4 * R) :
    -(Real.log 4 - 1) ≤ Real.log (R / ‖u - v‖) + 1 :=
  LatticeProb.CircleKernelBounds.kernel_ge_neg huv

/-- **Closed form of the circle average of the kernel** (the equality behind `circleAverage_kernel_ge_one_sub_log_two`). -/
theorem circleAverage_kernel_eq {z u : ℂ} {R : ℝ} (hR : 0 < R) :
    circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) =
      (Real.log R + 1) - (Real.log (3 * R / 2) + Real.posLog ((3 * R / 2)⁻¹ * ‖z - u‖)) :=
  LatticeProb.CircleKernelBounds.circleAverage_kernel_eq hR

/-- The circle average of the kernel is at most `log R + 1 - log(3R/2)`. -/
theorem circleAverage_kernel_le {z u : ℂ} {R : ℝ} (hR : 0 < R) :
    circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) ≤
      (Real.log R + 1) - Real.log (3 * R / 2) :=
  LatticeProb.CircleKernelBounds.circleAverage_kernel_le hR

/-- The integral of the kernel over `(0, 2π]` is at most `2π (log R + 1 - log(3R/2))`. -/
theorem integral_kernel_Ioc_le {z u : ℂ} {R : ℝ} (hR : 0 < R) :
    ∫ θ in Ioc 0 (2 * π), (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1) ≤
      2 * π * ((Real.log R + 1) - Real.log (3 * R / 2)) :=
  LatticeProb.CircleKernelBounds.integral_kernel_Ioc_le hR

/-- **Uniform bound on the absolute kernel over the annulus.** For `‖u - z‖ ≤ 2R`,
`∫_{(0,2π]} |K(u, circleMap θ)| dθ ≤ 2π (log R + 1 - log(3R/2) + 2(log 4 - 1))`. -/
theorem integral_norm_kernel_le {z u : ℂ} {R : ℝ} (hR : 0 < R) (hu : ‖u - z‖ ≤ 2 * R) :
    ∫ θ in Ioc 0 (2 * π), ‖Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1‖ ≤
      2 * π * ((Real.log R + 1) - Real.log (3 * R / 2) + 2 * (Real.log 4 - 1)) :=
  LatticeProb.CircleKernelBounds.integral_norm_kernel_le hR hu

end MatedCRT
