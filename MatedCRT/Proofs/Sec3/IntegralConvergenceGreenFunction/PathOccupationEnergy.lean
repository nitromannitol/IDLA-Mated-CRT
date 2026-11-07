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

/-- The Riesz energy kernel is measurable, including its diagonal value. -/
theorem measurable_rieszEnergyKernel {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (a : ℝ) :
    Measurable (fun p : E × E => rieszEnergyKernel a p.1 p.2) := by
  have hd : Measurable (fun p : E × E => dist p.1 p.2) := by fun_prop
  have hz : MeasurableSet {p : E × E | dist p.1 p.2 = 0} :=
    (measurableSet_singleton (0 : ℝ)).preimage hd
  have hp : Measurable (fun p : E × E => dist p.1 p.2 ^ (-a)) := by
    simp_rw [Real.rpow_def_of_nonneg dist_nonneg]
    apply Measurable.ite hz
    · split_ifs <;> fun_prop
    · fun_prop
  unfold rieszEnergyKernel
  by_cases ha : 0 < a
  · simp only [ha, and_true]
    exact Measurable.ite hz measurable_const hp.ennreal_ofReal
  · simp only [ha, and_false, ↓reduceIte]
    exact hp.ennreal_ofReal

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

/-- On a second-countable metric space, the time-integrated Riesz-energy
bound alone implies finite-dimensional energy of the occupation measure. -/
theorem pathOccupationMeasure_finiteDimensionalEnergy_of_increment_energy {E : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {b : ℝ → E} (hb : Measurable b) (T d : ℝ)
    (henergy : ∀ δ : ℝ, 0 < δ →
      (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ t in Icc (0 : ℝ) T,
        rieszEnergyKernel (d - δ) (b s) (b t)) < ⊤) :
    HasFiniteDimensionalEnergy (pathOccupationMeasure b T) d :=
  pathOccupationMeasure_finiteDimensionalEnergy hb T d
    (fun δ _ => measurable_rieszEnergyKernel (d - δ)) henergy

/-- A finite expected increment energy implies finite pathwise energy almost
surely, by Tonelli's theorem. -/
theorem ae_finite_increment_energy_of_expectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (F : Ω → ℝ → ℝ → ℝ≥0∞) (T : ℝ)
    (hF : Measurable (fun p : Ω × ℝ × ℝ => F p.1 p.2.1 p.2.2))
    (hfinite : (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ t in Icc (0 : ℝ) T,
      ∫⁻ ω, F ω s t ∂P) < ⊤) :
    ∀ᵐ ω ∂P, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ t in Icc (0 : ℝ) T,
      F ω s t) < ⊤ := by
  let ν := volume.restrict (Icc (0 : ℝ) T)
  have h₁ : Measurable (fun p : (Ω × ℝ) × ℝ => F p.1.1 p.1.2 p.2) := by
    exact hF.comp (show Measurable (fun p : (Ω × ℝ) × ℝ => (p.1.1, p.1.2, p.2)) by fun_prop)
  have h₂ : Measurable (fun p : Ω × ℝ => ∫⁻ t, F p.1 p.2 t ∂ν) :=
    h₁.lintegral_prod_right'
  have h₃ : Measurable (fun ω => ∫⁻ s, ∫⁻ t, F ω s t ∂ν ∂ν) :=
    h₂.lintegral_prod_right'
  apply ae_lt_top h₃
  have heq : (∫⁻ ω, ∫⁻ s, ∫⁻ t, F ω s t ∂ν ∂ν ∂P) =
      ∫⁻ s, ∫⁻ t, ∫⁻ ω, F ω s t ∂P ∂ν ∂ν := by
    rw [lintegral_lintegral_swap h₂.aemeasurable]
    apply lintegral_congr
    intro s
    apply lintegral_lintegral_swap
    exact (hF.comp (show Measurable (fun p : Ω × ℝ => (p.1, s, p.2)) by fun_prop)).aemeasurable
  rw [heq]
  exact hfinite.ne

/-- A finite time integral of expected Riesz increments gives almost-sure
finite energy for the occupation measure at the same exponent. -/
theorem ae_pathOccupationMeasure_riesz_energy_lt_top
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (b : Ω → ℝ → E) (hb : Measurable (fun p : Ω × ℝ => b p.1 p.2))
    (T a : ℝ)
    (hfinite : (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ t in Icc (0 : ℝ) T,
      ∫⁻ ω, rieszEnergyKernel a (b ω s) (b ω t) ∂P) < ⊤) :
    ∀ᵐ ω ∂P, (∫⁻ x, ∫⁻ y, rieszEnergyKernel a x y
      ∂(pathOccupationMeasure (b ω) T) ∂(pathOccupationMeasure (b ω) T)) < ⊤ := by
  have hm : Measurable (fun p : Ω × ℝ × ℝ =>
      rieszEnergyKernel a (b p.1 p.2.1) (b p.1 p.2.2)) := by
    change Measurable ((fun p : E × E => rieszEnergyKernel a p.1 p.2) ∘
      (fun p : Ω × ℝ × ℝ => (b p.1 p.2.1, b p.1 p.2.2)))
    apply (measurable_rieszEnergyKernel a).comp
    exact (hb.comp (show Measurable (fun p : Ω × ℝ × ℝ => (p.1, p.2.1)) by fun_prop)).prodMk
      (hb.comp (show Measurable (fun p : Ω × ℝ × ℝ => (p.1, p.2.2)) by fun_prop))
  filter_upwards [ae_finite_increment_energy_of_expectation P _ T hm hfinite] with ω hω
  have hbω : Measurable (b ω) := hb.comp (show Measurable (fun t : ℝ => (ω, t)) by fun_prop)
  rw [pathOccupationMeasure_kernel_energy hbω T (measurable_rieszEnergyKernel a)]
  exact hω

end MatedCRT
