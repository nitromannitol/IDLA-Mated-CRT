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

/-- On a finite collection of cells, the total error from replacing the test
integral by its embedded vertex value is controlled by the common oscillation. -/
theorem abs_integral_degreeWeightedMeasure_sub_vertex_sum_le
    {μ : Measure ℂ} {η : ℝ → ℂ} (hη : IsAreaParametrized μ η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (t : ℝ) (u : ℤ → ℝ) (f : ℂ → ℝ) (δ : ℝ) (F : Finset ℤ)
    (hint : Integrable (fun x => f x * rescale t ε η u x)
      (degreeWeightedMeasure m ε η μ))
    (hzero : ∀ a ∉ F, (matedDeg m a : ℝ) *
      ((∫ x in cell ε η a, f x ∂μ) * (t⁻¹ * u a)) = 0)
    (hf : ∀ a ∈ F, IntegrableOn f (cell ε η a) μ)
    (hosc : ∀ a ∈ F, ∀ x ∈ cell ε η a, |f x - f (vertexPoint ε η a)| ≤ δ) :
    |(∫ x, f x * rescale t ε η u x ∂degreeWeightedMeasure m ε η μ) -
      ∑ a ∈ F, (matedDeg m a : ℝ) *
        ((ε * f (vertexPoint ε η a)) * (t⁻¹ * u a))| ≤
      δ * ∑ a ∈ F, ((matedDeg m a : ℝ) * ε * |t⁻¹ * u a|) := by
  rw [integral_degreeWeightedMeasure_mul_rescale hη hp hε m t u f hint,
    tsum_eq_sum (s := F) hzero, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ F, |(matedDeg m a : ℝ) *
        ((∫ x in cell ε η a, f x ∂μ) * (t⁻¹ * u a)) -
        (matedDeg m a : ℝ) * ((ε * f (vertexPoint ε η a)) * (t⁻¹ * u a))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ F, δ * ((matedDeg m a : ℝ) * ε * |t⁻¹ * u a|) := by
      apply Finset.sum_le_sum
      intro a ha
      have hh := abs_setIntegral_sub_vertexPoint_le hη hε a f δ (hf a ha) (hosc a ha)
      have hid : (matedDeg m a : ℝ) * ((∫ x in cell ε η a, f x ∂μ) * (t⁻¹ * u a)) -
          (matedDeg m a : ℝ) * ((ε * f (vertexPoint ε η a)) * (t⁻¹ * u a)) =
          ((matedDeg m a : ℝ) * (t⁻¹ * u a)) *
            ((∫ x in cell ε η a, f x ∂μ) - ε * f (vertexPoint ε η a)) := by ring
      rw [hid, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have hdeg : (0 : ℝ) ≤ matedDeg m a := Nat.cast_nonneg _
      nlinarith [mul_nonneg hdeg (abs_nonneg (t⁻¹ * u a)),
        mul_le_mul_of_nonneg_left hh (mul_nonneg hdeg (abs_nonneg (t⁻¹ * u a)))]
    _ = δ * ∑ a ∈ F, ((matedDeg m a : ℝ) * ε * |t⁻¹ * u a|) := by
      rw [Finset.mul_sum]

/-- The cell mass and degree cancel the normalization of the Green kernel,
leaving the Green-function occupation summand. -/
theorem degree_mul_cell_mass_mul_scaled_greenKernel
    (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) (ε t value : ℝ)
    (hε : ε ≠ 0) (hdeg : matedDeg m b ≠ 0) :
    (matedDeg m b : ℝ) *
      ((ε * value) * (t⁻¹ * (ε⁻¹ * greenKernel m A a b))) =
      t⁻¹ * greenFn m A a b * value := by
  have hdeg' : (matedDeg m b : ℝ) ≠ 0 := by exact_mod_cast hdeg
  unfold greenKernel
  change (matedDeg m b : ℝ) *
      ((ε * value) * (t⁻¹ * (ε⁻¹ * (greenFn m A a b / (matedDeg m b : ℝ))))) = _
  field_simp

/-- The degree-weighted Green-kernel integral differs from the corresponding
finite Green-function occupation sum by at most the test oscillation times
the total occupation mass. -/
theorem abs_integral_degreeWeightedMeasure_sub_green_sum_le
    {μ : Measure ℂ} {η : ℝ → ℂ} (hη : IsAreaParametrized μ η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) (f : ℂ → ℝ) (δ : ℝ) (F : Finset ℤ)
    (hint : Integrable (fun x => f x * rescale t ε η
      (fun b => ε⁻¹ * greenKernel m A a b) x) (degreeWeightedMeasure m ε η μ))
    (hzero : ∀ b ∉ F, (matedDeg m b : ℝ) *
      ((∫ x in cell ε η b, f x ∂μ) * (t⁻¹ * (ε⁻¹ * greenKernel m A a b))) = 0)
    (hdeg : ∀ b ∈ F, matedDeg m b ≠ 0)
    (hf : ∀ b ∈ F, IntegrableOn f (cell ε η b) μ)
    (hosc : ∀ b ∈ F, ∀ x ∈ cell ε η b, |f x - f (vertexPoint ε η b)| ≤ δ) :
    |(∫ x, f x * rescale t ε η (fun b => ε⁻¹ * greenKernel m A a b) x
        ∂degreeWeightedMeasure m ε η μ) -
      ∑ b ∈ F, t⁻¹ * greenFn m A a b * f (vertexPoint ε η b)| ≤
      δ * ∑ b ∈ F, t⁻¹ * greenFn m A a b := by
  have hbound := abs_integral_degreeWeightedMeasure_sub_vertex_sum_le hη hp hε
    m t (fun b => ε⁻¹ * greenKernel m A a b) f δ F hint hzero hf hosc
  have hvertex : (∑ b ∈ F, (matedDeg m b : ℝ) *
      ((ε * f (vertexPoint ε η b)) * (t⁻¹ * (ε⁻¹ * greenKernel m A a b)))) =
      ∑ b ∈ F, t⁻¹ * greenFn m A a b * f (vertexPoint ε η b) := by
    apply Finset.sum_congr rfl
    intro b hb
    exact degree_mul_cell_mass_mul_scaled_greenKernel m A a b ε t _ hε.ne' (hdeg b hb)
  have hmass : (∑ b ∈ F, (matedDeg m b : ℝ) * ε *
      |t⁻¹ * (ε⁻¹ * greenKernel m A a b)|) =
      ∑ b ∈ F, t⁻¹ * greenFn m A a b := by
    apply Finset.sum_congr rfl
    intro b hb
    have hg : 0 ≤ greenKernel m A a b := by
      unfold greenKernel
      exact div_nonneg (by unfold greenFn; exact ENNReal.toReal_nonneg) (Nat.cast_nonneg _)
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ht.le)
      (mul_nonneg (inv_nonneg.mpr hε.le) hg))]
    have hid := degree_mul_cell_mass_mul_scaled_greenKernel m A a b ε t 1 hε.ne' (hdeg b hb)
    simpa only [mul_one, mul_assoc] using hid
  rw [hvertex, hmass] at hbound
  exact hbound

/-- Cells disjoint from the test's support contribute zero to the
weighted-cell expansion. -/
theorem weighted_cell_integral_eq_zero_of_not_mem_cellVertices_tsupport
    {μ : Measure ℂ} {η : ℝ → ℂ} {ε t : ℝ} (m : ℤ → ℤ → ℕ)
    (u : ℤ → ℝ) (f : ℂ → ℝ) {a : ℤ}
    (ha : a ∉ cellVertices ε η (tsupport f)) :
    (matedDeg m a : ℝ) * ((∫ x in cell ε η a, f x ∂μ) * (t⁻¹ * u a)) = 0 := by
  have hi : (∫ x in cell ε η a, f x ∂μ) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply Function.notMem_support.mp
    intro hf
    exact ha ⟨x, hx, subset_tsupport f hf⟩
  simp [hi]

/-- The occupation-sum estimate applies when the finite collection covers
every cell meeting the test's support. -/
theorem abs_integral_degreeWeightedMeasure_sub_green_sum_le_of_support
    {μ : Measure ℂ} {η : ℝ → ℂ} (hη : IsAreaParametrized μ η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) (f : ℂ → ℝ) (δ : ℝ) (F : Finset ℤ)
    (hint : Integrable (fun x => f x * rescale t ε η
      (fun b => ε⁻¹ * greenKernel m A a b) x) (degreeWeightedMeasure m ε η μ))
    (hcover : ∀ b ∈ cellVertices ε η (tsupport f), b ∈ F)
    (hdeg : ∀ b ∈ F, matedDeg m b ≠ 0)
    (hf : ∀ b ∈ F, IntegrableOn f (cell ε η b) μ)
    (hosc : ∀ b ∈ F, ∀ x ∈ cell ε η b, |f x - f (vertexPoint ε η b)| ≤ δ) :
    |(∫ x, f x * rescale t ε η (fun b => ε⁻¹ * greenKernel m A a b) x
        ∂degreeWeightedMeasure m ε η μ) -
      ∑ b ∈ F, t⁻¹ * greenFn m A a b * f (vertexPoint ε η b)| ≤
      δ * ∑ b ∈ F, t⁻¹ * greenFn m A a b := by
  apply abs_integral_degreeWeightedMeasure_sub_green_sum_le hη hp hε ht m A a f δ F hint
  · intro b hb
    exact weighted_cell_integral_eq_zero_of_not_mem_cellVertices_tsupport (μ := μ) (t := t)
      m (fun b => ε⁻¹ * greenKernel m A a b) f (fun h => hb (hcover b h))
  · exact hdeg
  · exact hf
  · exact hosc

end MatedCRT.GreenEnvironment
