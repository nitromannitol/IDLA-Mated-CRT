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

/-- The cell integral of a test differs from its value at the embedded vertex
by at most the cell mass times the oscillation of the test on that cell. -/
theorem abs_setIntegral_sub_vertexPoint_le {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (a : ℤ)
    (f : ℂ → ℝ) (δ : ℝ) (hf : IntegrableOn f (cell ε η a) μ)
    (hosc : ∀ x ∈ cell ε η a, |f x - f (vertexPoint ε η a)| ≤ δ) :
    |(∫ x in cell ε η a, f x ∂μ) - ε * f (vertexPoint ε η a)| ≤ δ * ε := by
  have hfinite : μ (cell ε η a) < ∞ := by
    rw [measure_cell_of_area_parametrized hη hε]
    exact ENNReal.ofReal_lt_top
  have hc : IntegrableOn (fun _ => f (vertexPoint ε η a)) (cell ε η a) μ :=
    integrableOn_const hfinite.ne
  have hb := norm_setIntegral_le_of_norm_le_const_ae' hfinite
    (f := fun x => f x - f (vertexPoint ε η a)) (C := δ)
    (Filter.Eventually.of_forall (fun x hx => by simpa [Real.norm_eq_abs] using hosc x hx))
  rw [integral_sub hf hc] at hb
  simpa [Real.norm_eq_abs, measureReal_def, measure_cell_of_area_parametrized hη hε,
    ENNReal.toReal_ofReal hε.le, mul_comm] using hb

end MatedCRT.GreenEnvironment
