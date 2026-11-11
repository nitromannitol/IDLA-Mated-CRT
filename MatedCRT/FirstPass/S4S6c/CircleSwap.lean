import Mathlib

/-!
# Lemma 1 of the Lemma 6.8 argument: Fubini over the good annulus and the circle

, "Lemma 1", proof, eq. (6): `M ≤ κ₀⁻¹ C_A m` comes from averaging `F(v) = ∫_A K(u,v) dμ(u)` over the circle
`v = z + t e^{iθ}`, `t = 3R/2`, and interchanging the integrals in `u` (over `A`) and `θ` (over `(0, 2π]`).
This file proves the interchange `∫_A (circle average of K(u,·)) dμ(u) = circle average of F` for a jointly measurable
kernel with joint integrability. The joint integrability is a SEPARATE step (OPEN): it follows from
the closed-form slice averages `circleAverage (log ‖· - u‖) z t = log t + log⁺(t⁻¹ ‖z - u‖)` of Mathlib together with the
lower bound `K ≥ -a₀` on the annulus; it is taken here as the explicit hypothesis `hjoint`.
-/

open MeasureTheory Real Set

namespace MatedCRT

/-- **Fubini over the annulus and the circle.** Swapping the average over `θ` with the integral over `u ∈ A`. -/
theorem integral_circleAverage_swap {A : Set ℂ} (μ : Measure ℂ) [SFinite μ] {z : ℂ} {t : ℝ}
    (K : ℂ → ℂ → ℝ)
    (hjoint : Integrable (fun p : ℂ × ℝ => K p.1 (circleMap z t p.2))
      ((μ.restrict A).prod (volume.restrict (Ioc 0 (2 * π))))) :
    ∫ u in A, circleAverage (fun v => K u v) z t ∂μ =
      circleAverage (fun v => ∫ u in A, K u v ∂μ) z t := by
  simp only [circleAverage_def, integral_smul]
  congr 1
  simp only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  exact integral_integral_swap (f := fun u θ => K u (circleMap z t θ)) hjoint

end MatedCRT
