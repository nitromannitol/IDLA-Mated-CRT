import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CellIntegral
import MatedCRT.Defs.Setting
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Degree-weighted integrals of rescaled vertex functions -/

namespace MatedCRT.GreenEnvironment

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- On each cell, a rescaled vertex function is almost everywhere constant,
so it factors out of the integral against any test function. -/
theorem setIntegral_mul_rescale_cell {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (a : ℤ) (m : ℝ) (u : ℤ → ℝ) (f : ℂ → ℝ) :
    (∫ x in cell ε η a, f x * rescale m ε η u x ∂μ) =
      (∫ x in cell ε η a, f x ∂μ) * (m⁻¹ * u a) := by
  calc
    (∫ x in cell ε η a, f x * rescale m ε η u x ∂μ) =
        ∫ x in cell ε η a, f x * (m⁻¹ * u a) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_vertexOf_eq_on_cell hη hp hε a] with x hx
      simp [rescale, hx]
    _ = (∫ x in cell ε η a, f x ∂μ) * (m⁻¹ * u a) := integral_mul_const _ _

/-- A degree-weighted integral of a rescaled vertex function is the sum of
its contributions from the individual cells. -/
theorem integral_degreeWeightedMeasure_mul_rescale {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (t : ℝ) (u : ℤ → ℝ) (f : ℂ → ℝ)
    (hint : Integrable (fun x => f x * rescale t ε η u x)
      (degreeWeightedMeasure m ε η μ)) :
    (∫ x, f x * rescale t ε η u x ∂degreeWeightedMeasure m ε η μ) =
      ∑' a : ℤ, (matedDeg m a : ℝ) *
        ((∫ x in cell ε η a, f x ∂μ) * (t⁻¹ * u a)) := by
  rw [degreeWeightedMeasure, integral_sum_measure hint]
  apply tsum_congr
  intro a
  rw [integral_smul_measure, setIntegral_mul_rescale_cell hη hp hε]
  simp

end MatedCRT.GreenEnvironment
