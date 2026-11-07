import MatedCRT.Defs.GaussianMultiplicativeChaos
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Energy of a finite-time path occupation measure -/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

/-- The occupation measure of a path over the finite time interval `[0,T]`. -/
noncomputable def pathOccupationMeasure {E : Type*} [MeasurableSpace E]
    (b : ℝ → E) (T : ℝ) : Measure E :=
  (volume.restrict (Icc (0 : ℝ) T)).map b

instance pathOccupationMeasure_finite {E : Type*} [MeasurableSpace E]
    (b : ℝ → E) (T : ℝ) : IsFiniteMeasure (pathOccupationMeasure b T) := by
  unfold pathOccupationMeasure
  exact Measure.isFiniteMeasure_map _ _

/-- A measurable path occupation measure has total mass equal to elapsed time. -/
theorem pathOccupationMeasure_univ {E : Type*} [MeasurableSpace E]
    {b : ℝ → E} (hb : Measurable b) (T : ℝ) :
    pathOccupationMeasure b T Set.univ = ENNReal.ofReal T := by
  rw [pathOccupationMeasure, Measure.map_apply hb MeasurableSet.univ]
  simp [Real.volume_Icc]

/-- If a path remains in a measurable set throughout the interval, its
occupation measure is concentrated on that set. -/
theorem pathOccupationMeasure_compl_eq_zero {E : Type*} [MeasurableSpace E]
    {b : ℝ → E} (hb : Measurable b) (T : ℝ) {D : Set E} (hD : MeasurableSet D)
    (hpath : ∀ t ∈ Icc (0 : ℝ) T, b t ∈ D) :
    pathOccupationMeasure b T Dᶜ = 0 := by
  rw [pathOccupationMeasure, Measure.map_apply hb hD.compl]
  rw [Measure.restrict_apply (hD.compl.preimage hb)]
  have he : (b ⁻¹' D)ᶜ ∩ Icc (0 : ℝ) T = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact ht.1 (hpath t ht.2)
  simp [he]

/-- A measurable nonnegative kernel has the same energy against the path
occupation measure as its double time integral along the path. -/
theorem pathOccupationMeasure_kernel_energy {E : Type*} [MeasurableSpace E]
    {b : ℝ → E} (hb : Measurable b) (T : ℝ) {k : E × E → ℝ≥0∞}
    (hk : Measurable k) :
    (∫⁻ x, ∫⁻ y, k (x, y) ∂(pathOccupationMeasure b T) ∂(pathOccupationMeasure b T)) =
      ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ t in Icc (0 : ℝ) T, k (b s, b t) := by
  rw [pathOccupationMeasure, lintegral_map hk.lintegral_prod_right' hb]
  apply lintegral_congr
  intro s
  exact lintegral_map (hk.comp (measurable_const.prodMk measurable_id)) hb

/-- Finite time-integrated Riesz energy along a path yields a finite-dimensional
energy bound for its occupation measure. -/
theorem pathOccupationMeasure_finiteDimensionalEnergy {E : Type*}
    [MetricSpace E] [MeasurableSpace E] {b : ℝ → E} (hb : Measurable b)
    (T d : ℝ)
    (hkernel : ∀ δ : ℝ, 0 < δ → Measurable
      (fun p : E × E => rieszEnergyKernel (d - δ) p.1 p.2))
    (henergy : ∀ δ : ℝ, 0 < δ →
      (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ t in Icc (0 : ℝ) T,
        rieszEnergyKernel (d - δ) (b s) (b t)) < ⊤) :
    HasFiniteDimensionalEnergy (pathOccupationMeasure b T) d := by
  intro δ hδ
  rw [pathOccupationMeasure_kernel_energy hb T (hkernel δ hδ)]
  exact henergy δ hδ

end MatedCRT
