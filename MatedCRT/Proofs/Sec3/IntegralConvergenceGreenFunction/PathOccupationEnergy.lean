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

/-- Finite-dimensional Riesz energy passes to a smaller measure. -/
theorem HasFiniteDimensionalEnergy.of_le {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] {μ ν : Measure E} {d : ℝ} (hμν : μ ≤ ν)
    (hν : HasFiniteDimensionalEnergy ν d) : HasFiniteDimensionalEnergy μ d := by
  intro δ hδ
  exact lt_of_le_of_lt (lintegral_mono' hμν (fun x =>
    lintegral_mono' hμν (fun _ => le_rfl))) (hν δ hδ)

/-- Occupation before an earlier time is dominated by occupation before a
later time. This also applies to a finite stopping time path by path. -/
theorem pathOccupationMeasure_mono {E : Type*} [MeasurableSpace E]
    {b : ℝ → E} (hb : Measurable b) {S T : ℝ} (hST : S ≤ T) :
    pathOccupationMeasure b S ≤ pathOccupationMeasure b T := by
  apply Measure.map_mono _ hb
  exact Measure.restrict_mono_set volume (Icc_subset_Icc_right hST)

/-- Finite-dimensional energy on a deterministic interval transfers to every
earlier stopping time. -/
theorem pathOccupationMeasure_finiteDimensionalEnergy_of_le {E : Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] {b : ℝ → E}
    (hb : Measurable b) {S T d : ℝ} (hST : S ≤ T)
    (henergy : HasFiniteDimensionalEnergy (pathOccupationMeasure b T) d) :
    HasFiniteDimensionalEnergy (pathOccupationMeasure b S) d :=
  henergy.of_le (pathOccupationMeasure_mono hb hST)

/-- Finite energy at every integer horizon gives finite energy at every
finite path-dependent horizon, on a single almost-sure event. -/
theorem ae_pathOccupationMeasure_finiteDimensionalEnergy_all_horizons
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [PseudoMetricSpace E] [MeasurableSpace E] (b : Ω → ℝ → E)
    (hb : ∀ᵐ ω ∂P, Measurable (b ω)) (d : ℝ)
    (henergy : ∀ n : ℕ, ∀ᵐ ω ∂P,
      HasFiniteDimensionalEnergy (pathOccupationMeasure (b ω) n) d) :
    ∀ᵐ ω ∂P, ∀ T : ℝ,
      HasFiniteDimensionalEnergy (pathOccupationMeasure (b ω) T) d := by
  filter_upwards [hb, ae_all_iff.mpr henergy] with ω hbω hω T
  obtain ⟨n, hn⟩ := exists_nat_ge T
  exact pathOccupationMeasure_finiteDimensionalEnergy_of_le hbω hn (hω n)

/-- On all metric spaces, a nonnegative lower-order Riesz kernel is bounded
by one plus a higher-order kernel. -/
theorem rieszEnergyKernel_le_one_add {E : Type*} [PseudoMetricSpace E]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (x y : E) :
    rieszEnergyKernel a x y ≤ 1 + rieszEnergyKernel b x y := by
  unfold rieszEnergyKernel
  by_cases hz : dist x y = 0
  · by_cases hapos : 0 < a
    · have hbpos : 0 < b := lt_of_lt_of_le hapos hab
      simp [hz, hapos, hbpos]
    · simp only [hz, hapos, and_false, ↓reduceIte]
      have ha0 : a = 0 := le_antisymm (le_of_not_gt hapos) ha
      simp [ha0]
  · have hp : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hz)
    simp only [hz, false_and, ↓reduceIte]
    by_cases hd : dist x y ≤ 1
    · have h := Real.rpow_le_rpow_of_exponent_ge hp hd (neg_le_neg hab)
      exact (ENNReal.ofReal_le_ofReal h).trans (le_add_self)
    · have h := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hd) (neg_nonpos.mpr ha)
      exact (ENNReal.ofReal_le_ofReal h).trans (by simp)

/-- For a finite measure, finite Riesz energy at a positive exponent implies
finite energy at every smaller nonnegative exponent. -/
theorem rieszEnergy_lt_top_of_le {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [IsFiniteMeasure μ] {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : (∫⁻ x, ∫⁻ y, rieszEnergyKernel b x y ∂μ ∂μ) < ⊤) :
    (∫⁻ x, ∫⁻ y, rieszEnergyKernel a x y ∂μ ∂μ) < ⊤ := by
  have hbound : (∫⁻ x, ∫⁻ y, rieszEnergyKernel a x y ∂μ ∂μ) ≤
      ∫⁻ x, ∫⁻ y, (1 + rieszEnergyKernel b x y) ∂μ ∂μ := by
    exact lintegral_mono fun x => lintegral_mono fun y =>
      rieszEnergyKernel_le_one_add ha hab x y
  apply lt_of_le_of_lt hbound
  simp_rw [lintegral_add_left measurable_const]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact lintegral_const_lt_top (ne_of_lt (lintegral_const_lt_top (by simp)))
  · exact hb

/-- A countable cofinal family of nonnegative exponents gives finite energy
at every nonnegative exponent below the limiting dimension on one event. -/
theorem ae_rieszEnergy_lt_top_of_countable_cofinal
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Ω → Measure E) [∀ ω, IsFiniteMeasure (μ ω)] (d : ℝ) (q : ℕ → ℝ)
    (hcofinal : ∀ a : ℝ, 0 ≤ a → a < d → ∃ n, a ≤ q n)
    (henergy : ∀ n, ∀ᵐ ω ∂P,
      (∫⁻ x, ∫⁻ y, rieszEnergyKernel (q n) x y ∂(μ ω) ∂(μ ω)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, 0 ≤ a → a < d →
      (∫⁻ x, ∫⁻ y, rieszEnergyKernel a x y ∂(μ ω) ∂(μ ω)) < ⊤ := by
  filter_upwards [ae_all_iff.mpr henergy] with ω hω a ha had
  obtain ⟨n, hn⟩ := hcofinal a ha had
  exact rieszEnergy_lt_top_of_le (μ ω) ha hn (hω n)

/-- At a nonpositive exponent, the Riesz kernel is bounded on a set of
bounded diameter. -/
theorem rieszEnergyKernel_le_of_dist_le {E : Type*} [PseudoMetricSpace E]
    {a R : ℝ} (ha : a ≤ 0) {x y : E} (hR : dist x y ≤ R) :
    rieszEnergyKernel a x y ≤ ENNReal.ofReal (R ^ (-a)) := by
  simp only [rieszEnergyKernel, not_lt_of_ge ha, and_false, ↓reduceIte]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow dist_nonneg hR (neg_nonneg.mpr ha))

/-- A finite measure whose pairs have bounded distance almost everywhere has
finite Riesz energy at every nonpositive exponent. -/
theorem rieszEnergy_lt_top_of_ae_bounded {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ] {a R : ℝ}
    (ha : a ≤ 0) (hR : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, dist x y ≤ R) :
    (∫⁻ x, ∫⁻ y, rieszEnergyKernel a x y ∂μ ∂μ) < ⊤ := by
  have hbound : (∫⁻ x, ∫⁻ y, rieszEnergyKernel a x y ∂μ ∂μ) ≤
      ∫⁻ _x, ∫⁻ _y, ENNReal.ofReal (R ^ (-a)) ∂μ ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [hR] with x hx
    apply lintegral_mono_ae
    filter_upwards [hx] with y hy
    exact rieszEnergyKernel_le_of_dist_le ha hy
  apply lt_of_le_of_lt hbound
  exact lintegral_const_lt_top (ne_of_lt (lintegral_const_lt_top ENNReal.ofReal_ne_top))

/-- Countably many cofinal energy estimates and almost-sure bounded diameter
establish the full finite-dimensional energy condition. -/
theorem ae_hasFiniteDimensionalEnergy_of_countable_cofinal
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Ω → Measure E) [∀ ω, IsFiniteMeasure (μ ω)] (d : ℝ) (q : ℕ → ℝ)
    (hcofinal : ∀ a : ℝ, 0 ≤ a → a < d → ∃ n, a ≤ q n)
    (henergy : ∀ n, ∀ᵐ ω ∂P,
      (∫⁻ x, ∫⁻ y, rieszEnergyKernel (q n) x y ∂(μ ω) ∂(μ ω)) < ⊤)
    (hbounded : ∀ᵐ ω ∂P, ∃ R : ℝ, ∀ᵐ x ∂(μ ω), ∀ᵐ y ∂(μ ω), dist x y ≤ R) :
    ∀ᵐ ω ∂P, HasFiniteDimensionalEnergy (μ ω) d := by
  filter_upwards [ae_rieszEnergy_lt_top_of_countable_cofinal P μ d q hcofinal henergy,
    hbounded] with ω hω ⟨R, hR⟩ δ hδ
  by_cases ha : 0 ≤ d - δ
  · exact hω (d - δ) ha (sub_lt_self d hδ)
  · exact rieszEnergy_lt_top_of_ae_bounded (μ ω) (le_of_not_ge ha) hR

end MatedCRT
